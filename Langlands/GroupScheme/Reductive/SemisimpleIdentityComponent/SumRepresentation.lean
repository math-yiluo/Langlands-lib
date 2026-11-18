import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Multiplicative
import Mathlib.Data.Matrix.Block
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Semisimple
import Langlands.GroupScheme.Reductive.InvariantLinearForm

/-! # The direct sum of two matrix representations on `Fin (n + m)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n m : ℕ}

/-- The block diagonal matrix of two square matrices, indexed by `Fin (n + m)`. -/
def sumMatrix {A : Type*} [Zero A] (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin m) (Fin m) A) :
    Matrix (Fin (n + m)) (Fin (n + m)) A :=
  (Matrix.fromBlocks M 0 0 N).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem sumMatrix_one {A : Type*} [Semiring A] :
    sumMatrix (1 : Matrix (Fin n) (Fin n) A) (1 : Matrix (Fin m) (Fin m) A) = 1 := by
  rw [sumMatrix, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem sumMatrix_mul {A : Type*} [Semiring A] (M M' : Matrix (Fin n) (Fin n) A)
    (N N' : Matrix (Fin m) (Fin m) A) :
    sumMatrix (M * M') (N * N') = sumMatrix M N * sumMatrix M' N' := by
  rw [sumMatrix, sumMatrix, sumMatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem sumMatrix_map {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (M : Matrix (Fin n) (Fin n) A) (N : Matrix (Fin m) (Fin m) A) :
    (sumMatrix M N).map f = sumMatrix (M.map f) (N.map f) := by
  rw [sumMatrix, sumMatrix, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

theorem sumMatrix_eq_one_iff {A : Type*} [Semiring A] (M : Matrix (Fin n) (Fin n) A)
    (N : Matrix (Fin m) (Fin m) A) : sumMatrix M N = 1 ↔ M = 1 ∧ N = 1 := by
  rw [← sumMatrix_one (A := A) (n := n) (m := m), sumMatrix, sumMatrix]
  constructor
  · intro h
    have h' := congrArg (fun P => P.submatrix finSumFinEquiv finSumFinEquiv) h
    simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
    rw [Matrix.fromBlocks_inj] at h'
    exact ⟨h'.1, h'.2.2.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Embedding of the first summand. -/
def sumInl {A : Type*} [Zero A] (v : Fin n → A) : Fin (n + m) → A :=
  Sum.elim v 0 ∘ finSumFinEquiv.symm

/-- Embedding of the second summand. -/
def sumInr {A : Type*} [Zero A] (w : Fin m → A) : Fin (n + m) → A :=
  Sum.elim 0 w ∘ finSumFinEquiv.symm

theorem sumMatrix_mulVec_sumInl {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A)
    (N : Matrix (Fin m) (Fin m) A) (v : Fin n → A) :
    sumMatrix M N *ᵥ sumInl v = sumInl (m := m) (M *ᵥ v) := by
  rw [sumMatrix, sumInl, sumInl, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Matrix.fromBlocks_mulVec]
  congr 1
  funext i
  rcases i with i | i <;> simp [Function.comp_def, ← Pi.zero_def, Matrix.mulVec_zero]

theorem sumMatrix_mulVec_sumInr {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A)
    (N : Matrix (Fin m) (Fin m) A) (w : Fin m → A) :
    sumMatrix M N *ᵥ sumInr w = sumInr (n := n) (N *ᵥ w) := by
  rw [sumMatrix, sumInr, sumInr, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Matrix.fromBlocks_mulVec]
  congr 1
  funext i
  rcases i with i | i <;> simp [Function.comp_def, ← Pi.zero_def, Matrix.mulVec_zero]

theorem sumInl_add_sumInr {A : Type*} [AddZeroClass A] (x : Fin (n + m) → A) :
    sumInl (m := m) (fun i => x (finSumFinEquiv (Sum.inl i))) +
      sumInr (n := n) (fun j => x (finSumFinEquiv (Sum.inr j))) = x := by
  funext t
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective t
  rcases s with i | j <;> simp [sumInl, sumInr]

variable (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m))

/-- The block point matrices of two representations form a monoid action. -/
def sumMatrixHom (T : Over (Spec R)) :
    (T ⟶ G.X) →* Matrix (Fin (n + m)) (Fin (n + m)) Γ(T.left, ⊤) where
  toFun x := sumMatrix (ρ.pointMatrix T x : Matrix _ _ _) (σ.pointMatrix T x : Matrix _ _ _)
  map_one' := by
    simp only [map_one, Matrix.GeneralLinearGroup.coe_one]
    exact sumMatrix_one
  map_mul' x y := by
    simp only [map_mul, Matrix.GeneralLinearGroup.coe_mul]
    exact sumMatrix_mul _ _ _ _

/-- The direct-sum point family. -/
def sumPoints (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme (Fin (n + m)) R).X) :=
  (GeneralLinear.pointsEquiv (Fin (n + m)) R T).symm.toMonoidHom.comp
    (sumMatrixHom ρ σ T).toHomUnits

theorem sumPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ G.X) :
    sumPoints ρ σ T' (a ≫ x) = a ≫ sumPoints ρ σ T x := by
  apply (GeneralLinear.pointsEquiv (Fin (n + m)) R T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [sumPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  change sumMatrix _ _ = (sumMatrix _ _).map a.left.appTop.hom
  rw [sumMatrix_map, pointMatrix_naturality, pointMatrix_naturality]
  rfl

/-- The direct sum of two matrix representations, on `Fin (n + m)`. -/
def sum : MatrixRepresentation G (Fin (n + m)) :=
  homOfPoints (sumPoints ρ σ) (sumPoints_naturality ρ σ)

theorem sum_pointMatrix_val (T : Over (Spec R)) (x : T ⟶ G.X) :
    ((ρ.sum σ).pointMatrix T x : Matrix (Fin (n + m)) (Fin (n + m)) Γ(T.left, ⊤)) =
      sumMatrix (ρ.pointMatrix T x : Matrix _ _ _) (σ.pointMatrix T x : Matrix _ _ _) := by
  have h : (ρ.sum σ).pointMatrix T x = (sumMatrixHom ρ σ T).toHomUnits x := by
    rw [pointMatrix_apply, sum, comp_homOfPoints]
    exact (GeneralLinear.pointsEquiv (Fin (n + m)) R T).apply_symm_apply _
  rw [h]
  rfl

theorem sum_pointMatrix_eq_one_iff (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.sum σ).pointMatrix T x = 1 ↔ ρ.pointMatrix T x = 1 ∧ σ.pointMatrix T x = 1 := by
  rw [Units.ext_iff, sum_pointMatrix_val, Matrix.GeneralLinearGroup.coe_one,
    sumMatrix_eq_one_iff, Units.ext_iff, Units.ext_iff]
  rfl

theorem sum_rationalMatrix_val (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    ((ρ.sum σ).rationalMatrix x : Matrix (Fin (n + m)) (Fin (n + m)) R) =
      sumMatrix (ρ.rationalMatrix x : Matrix _ _ _) (σ.rationalMatrix x : Matrix _ _ _) := by
  change ((ρ.sum σ).pointMatrix (Over.mk (𝟙 (Spec R))) x :
    Matrix (Fin (n + m)) (Fin (n + m)) Γ((Over.mk (𝟙 (Spec R))).left, ⊤)).map
      (Scheme.ΓSpecIso R).hom.hom = _
  rw [sum_pointMatrix_val, sumMatrix_map]
  rfl

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SemisimpleIdentityComponent

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- A representation that is the sum of the images of two intertwining maps out of
semisimple representations is semisimple. -/
theorem isSemisimpleRepresentation_of_sup_range {k Γ V V₁ V₂ : Type*} [Field k] [Group Γ]
    [AddCommGroup V] [Module k V] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (τ : Representation k Γ V) (τ₁ : Representation k Γ V₁) (τ₂ : Representation k Γ V₂)
    (f₁ : τ₁.IntertwiningMap τ) (f₂ : τ₂.IntertwiningMap τ)
    (h : LinearMap.range f₁.toLinearMap ⊔ LinearMap.range f₂.toLinearMap = ⊤)
    (h₁ : τ₁.IsSemisimpleRepresentation) (h₂ : τ₂.IsSemisimpleRepresentation) :
    τ.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at h₁ h₂ ⊢
  let F₁ := Representation.IntertwiningMap.equivLinearMapAsModule τ₁ τ f₁
  let F₂ := Representation.IntertwiningMap.equivLinearMapAsModule τ₂ τ f₂
  have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range F₁) (IsSemisimpleModule.range F₂)
  have htop : LinearMap.range F₁ ⊔ LinearMap.range F₂ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : (v : V) ∈ LinearMap.range f₁.toLinearMap ⊔ LinearMap.range f₂.toLinearMap := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, hab⟩ := Submodule.mem_sup.1 hv
    exact Submodule.mem_sup.2 ⟨F₁ x, ⟨x, rfl⟩, F₂ y, ⟨y, rfl⟩, hab⟩
  rw [htop] at hs
  exact IsSemisimpleModule.congr (Submodule.topEquiv).symm

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} {n m : ℕ}

/-- The direct sum of two representations with semisimple rational-point representations has
semisimple rational-point representation. -/
theorem sum_rationalRepresentation_isSemisimple (ρ : MatrixRepresentation G (Fin n))
    (σ : MatrixRepresentation G (Fin m))
    (hρ : ρ.rationalRepresentation.IsSemisimpleRepresentation)
    (hσ : σ.rationalRepresentation.IsSemisimpleRepresentation) :
    (ρ.sum σ).rationalRepresentation.IsSemisimpleRepresentation := by
  let f₁ : ρ.rationalRepresentation.IntertwiningMap (ρ.sum σ).rationalRepresentation :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _
      { toFun := fun v => sumInl (m := m) v
        map_add' := fun v w => by
          funext t
          simp only [sumInl, Function.comp_apply, Pi.add_apply]
          rcases finSumFinEquiv.symm t with i | j <;> simp
        map_smul' := fun c v => by
          funext t
          simp only [sumInl, Function.comp_apply, Pi.smul_apply, RingHom.id_apply]
          rcases finSumFinEquiv.symm t with i | j <;> simp }
      (fun g v => by
        change sumInl (m := m) ((ρ.rationalMatrix g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
          ((ρ.sum σ).rationalMatrix g : Matrix (Fin (n + m)) (Fin (n + m)) k) *ᵥ sumInl v
        rw [sum_rationalMatrix_val]
        exact (sumMatrix_mulVec_sumInl _ _ v).symm)
  let f₂ : σ.rationalRepresentation.IntertwiningMap (ρ.sum σ).rationalRepresentation :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _
      { toFun := fun w => sumInr (n := n) w
        map_add' := fun v w => by
          funext t
          simp only [sumInr, Function.comp_apply, Pi.add_apply]
          rcases finSumFinEquiv.symm t with i | j <;> simp
        map_smul' := fun c v => by
          funext t
          simp only [sumInr, Function.comp_apply, Pi.smul_apply, RingHom.id_apply]
          rcases finSumFinEquiv.symm t with i | j <;> simp }
      (fun g w => by
        change sumInr (n := n) ((σ.rationalMatrix g : Matrix (Fin m) (Fin m) k) *ᵥ w) =
          ((ρ.sum σ).rationalMatrix g : Matrix (Fin (n + m)) (Fin (n + m)) k) *ᵥ sumInr w
        rw [sum_rationalMatrix_val]
        exact (sumMatrix_mulVec_sumInr _ _ w).symm)
  refine isSemisimpleRepresentation_of_sup_range _ _ _ f₁ f₂ ?_ hρ hσ
  rw [eq_top_iff]
  intro x _
  rw [← sumInl_add_sumInr (n := n) (m := m) x]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

end Langlands.GroupScheme.SemisimpleIdentityComponent
