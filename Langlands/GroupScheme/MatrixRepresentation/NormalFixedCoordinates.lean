import Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates
import Langlands.GroupScheme.MatrixRepresentation.InvariantCoordinates
import Langlands.GroupScheme.AffinePoints
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Coefficient extraction for fixed vectors of normal subgroups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

section AffineTests

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Point-matrix fixedness on an affine test is exactly the equation in its algebra. -/
theorem affine_fixed_iff (ρ : MatrixRepresentation G n) (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ G.X) (v : n → R) :
    (ρ.pointMatrix ((algSpec R).obj (op A)) x : Matrix n n Γ(_, ⊤)) *ᵥ
        (fun i => scalarMap ((algSpec R).obj (op A)) (v i)) =
      (fun i => scalarMap ((algSpec R).obj (op A)) (v i)) ↔
    (ρ.affineMatrix A x : Matrix n n A) *ᵥ (fun i => algebraMap R A (v i)) =
      (fun i => algebraMap R A (v i)) := by
  let e := Corepresented.affineSectionsAlgEquiv A
  rw [pointMatrix_eq_affineMatrix]
  simp only [UnipotentMatrixCriterion.scalarMap_affine]
  constructor
  · intro h
    funext i
    apply e.symm.injective
    exact (e.symm.toRingHom.map_mulVec _ _ i).trans (congrFun h i)
  · intro h
    funext i
    exact ((e.symm.toRingHom.map_mulVec _ _ i).symm).trans
      (congrArg e.symm (congrFun h i))

theorem IsFixedVector.affine {ρ : MatrixRepresentation G n} {v : n → R}
    (hv : ρ.IsFixedVector v) (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶ G.X) :
    (ρ.affineMatrix A x : Matrix n n A) *ᵥ (fun i => algebraMap R A (v i)) =
      (fun i => algebraMap R A (v i)) :=
  (affine_fixed_iff ρ A x v).1 (hv _ x)

/-- One affine model point detects all-test fixedness. -/
theorem isFixedVector_iff_affine_model (ρ : MatrixRepresentation G n)
    {A : CommAlgCat.{u} R} (j : (algSpec R).obj (op A) ≅ G.X) (v : n → R) :
    ρ.IsFixedVector v ↔
      (ρ.affineMatrix A j.hom : Matrix n n A) *ᵥ
        (fun i => algebraMap R A (v i)) = (fun i => algebraMap R A (v i)) := by
  constructor
  · exact fun hv => hv.affine A j.hom
  · intro hv T x
    have h := (affine_fixed_iff ρ A j.hom v).2 hv
    have hmat := ρ.pointMatrix_naturality (x ≫ j.inv) j.hom
    simp only [Category.assoc, j.inv_hom_id, Category.comp_id] at hmat
    rw [hmat]
    funext i
    have hi := congrArg (fun w => (x ≫ j.inv).left.appTop.hom (w i)) h
    rw [(x ≫ j.inv).left.appTop.hom.map_mulVec] at hi
    change (((ρ.pointMatrix ((algSpec R).obj (op A)) j.hom :
      Matrix n n Γ(_, ⊤)).map (x ≫ j.inv).left.appTop.hom) *ᵥ
        (fun i => scalarMap T (v i))) i = _
    simpa only [Function.comp_def, scalarMap_naturality] using hi

end AffineTests

section TensorCoefficients

variable {k A B : Type u} [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B]
  {n : Type} [Fintype n]

/-- Apply a linear functional to the left tensor coefficient. -/
def tensorCoefficient (ℓ : A →ₗ[k] k) : A ⊗[k] B →ₗ[k] B :=
  (TensorProduct.lid k B).toLinearMap ∘ₗ ℓ.rTensor B

@[simp]
theorem tensorCoefficient_tmul (ℓ : A →ₗ[k] k) (a : A) (b : B) :
    tensorCoefficient ℓ (a ⊗ₜ[k] b) = ℓ a • b := by
  simp [tensorCoefficient]

/-- A fixed tensor vector has fixed vectors as every left coefficient. -/
theorem fixed_tensor_coefficients (M : Matrix n n B) (w : n → A)
    (hw : M.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) *ᵥ
        (fun i => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) (w i)) =
      (fun i => (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) (w i)))
    (ℓ : A →ₗ[k] k) :
    M *ᵥ (fun i => algebraMap k B (ℓ (w i))) =
      (fun i => algebraMap k B (ℓ (w i))) := by
  funext i
  have hi := congrArg (tensorCoefficient ℓ) (congrFun hw i)
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, tensorCoefficient_tmul,
    Algebra.smul_def, mul_comm] using hi

end TensorCoefficients

section NormalFixedVectors

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n) (i : H ⟶ G)
  (hN : (SubgroupFunctor.range i).IsNormal)

include hN in
/-- Normality fixes every translate of a fixed vector on the same affine test. -/
theorem normal_fixed_affine {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (h : (algSpec (CommRingCat.of k)).obj (op A) ⟶ H.X) :
    (ρ.affineMatrix A (h ≫ i.hom.hom) : Matrix n n A) *ᵥ
        ((ρ.affineMatrix A g : Matrix n n A) *ᵥ
          (fun j => algebraMap k A (v j))) =
      (ρ.affineMatrix A g : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (v j)) := by
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1
    (hN _ g⁻¹ (h ≫ i.hom.hom) (by trivial)
      (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
  have key := hv.affine A h'
  rw [affineMatrix_restrict, hh', map_mul, map_mul, map_inv, inv_inv] at key
  set U := ρ.affineMatrix A g
  set M := ρ.affineMatrix A (h ≫ i.hom.hom)
  have he :
      (M : Matrix n n A) *ᵥ
          ((U : Matrix n n A) *ᵥ (fun j => algebraMap k A (v j))) =
        (U : Matrix n n A) *ᵥ
          (((U⁻¹ * M * U : GL n A) : Matrix n n A) *ᵥ
            (fun j => algebraMap k A (v j))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [he, key]

include hN in
/-- Every linear coefficient of an affine translate lies in the original fixed space. -/
theorem normal_fixed_coefficient {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    {B : CommAlgCat.{u} (CommRingCat.of k)}
    (j : (algSpec (CommRingCat.of k)).obj (op B) ≅ H.X)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (ℓ : A →ₗ[k] k) :
    (ρ.restrict i).IsFixedVector
      (fun a => ℓ (((ρ.affineMatrix A g : Matrix n n A) *ᵥ
        (fun b => algebraMap k A (v b))) a)) := by
  let D := CommAlgCat.of (CommRingCat.of k) (A ⊗[k] B)
  let a : A ⟶ D := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let b : B ⟶ D := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let gD := (algSpec (CommRingCat.of k)).map a.op ≫ g
  let hD := (algSpec (CommRingCat.of k)).map b.op ≫ j.hom
  have ht := normal_fixed_affine ρ i hN hv D gD hD
  have hg : ρ.affineMatrix D gD =
      Matrix.GeneralLinearGroup.map a.hom.toRingHom (ρ.affineMatrix A g) :=
    ρ.affineMatrix_naturality a g
  have hh : ρ.affineMatrix D (hD ≫ i.hom.hom) =
      Matrix.GeneralLinearGroup.map b.hom.toRingHom
        ((ρ.restrict i).affineMatrix B j.hom) := by
    dsimp only [hD]
    rw [Category.assoc, affineMatrix_naturality, affineMatrix_restrict]
  rw [hg, hh] at ht
  have hvec :
      ((Matrix.GeneralLinearGroup.map a.hom.toRingHom (ρ.affineMatrix A g) :
        GL n D) : Matrix n n D) *ᵥ (fun r => algebraMap k D (v r)) =
      (fun r => a.hom
        (((ρ.affineMatrix A g : Matrix n n A) *ᵥ
          (fun s => algebraMap k A (v s))) r)) := by
    funext r
    change (((ρ.affineMatrix A g : Matrix n n A).map a.hom.toRingHom) *ᵥ
      (fun s => algebraMap k D (v s))) r =
        a.hom.toRingHom
          (((ρ.affineMatrix A g : Matrix n n A) *ᵥ
            (fun s => algebraMap k A (v s))) r)
    rw [a.hom.toRingHom.map_mulVec]
    congr 2
  rw [hvec] at ht
  apply ((ρ.restrict i).isFixedVector_iff_affine_model j _).2
  exact fixed_tensor_coefficients
    ((ρ.restrict i).affineMatrix B j.hom : Matrix n n B)
    ((ρ.affineMatrix A g : Matrix n n A) *ᵥ (fun r => algebraMap k A (v r))) ht ℓ

end NormalFixedVectors

section Projections

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  {n : Type} [Fintype n]

theorem linearFunctional_mulVec (Q : Matrix n n k) (w : n → A)
    (ℓ : A →ₗ[k] k) (r : n) :
    ℓ ((Q.map (algebraMap k A) *ᵥ w) r) =
      (Q *ᵥ (fun s => ℓ (w s))) r := by
  have hs (c : k) (a : A) : ℓ (algebraMap k A c * a) = c * ℓ a := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, hs]

/-- Linear functionals detect whether a vector lies in the extended projection image. -/
theorem projection_mulVec_eq_of_coefficients (Q : Matrix n n k) (w : n → A)
    (hw : ∀ ℓ : A →ₗ[k] k, Q *ᵥ (fun s => ℓ (w s)) = (fun s => ℓ (w s))) :
    Q.map (algebraMap k A) *ᵥ w = w := by
  funext r
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k _).1
  intro ℓ
  rw [map_sub, linearFunctional_mulVec, congrFun (hw ℓ) r, sub_self]

end Projections

section Stability

variable {k : Type u} [Field k]
  {G H J : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- Normality makes any coordinates spanning the fixed subspace invariant on affine tests. -/
theorem normal_fixed_coordinates_affine
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    {D : CommAlgCat.{u} (CommRingCat.of k)}
    (j : (algSpec (CommRingCat.of k)).obj (op D) ≅ H.X)
    (B : Matrix n m k) (C : Matrix m n k)
    (hcols : ∀ s, (ρ.restrict i).IsFixedVector (fun r => B r s))
    (hproj : ∀ v, (ρ.restrict i).IsFixedVector v → (B * C) *ᵥ v = v)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    (ρ.affineMatrix A g : Matrix n n A) * B.map (algebraMap k A) =
      B.map (algebraMap k A) *
        (C.map (algebraMap k A) * (ρ.affineMatrix A g : Matrix n n A) *
          B.map (algebraMap k A)) := by
  have he : (ρ.affineMatrix A g : Matrix n n A) * B.map (algebraMap k A) =
      (B * C).map (algebraMap k A) *
        ((ρ.affineMatrix A g : Matrix n n A) * B.map (algebraMap k A)) := by
    ext r s
    have hs := projection_mulVec_eq_of_coefficients (B * C)
      ((ρ.affineMatrix A g : Matrix n n A) *ᵥ
        (fun a => algebraMap k A (B a s)))
      (fun ℓ => hproj _ (normal_fixed_coefficient ρ i hN (hcols s) j A g ℓ))
    exact (congrFun hs r).symm
  rw [Matrix.map_mul] at he
  simpa only [Matrix.mul_assoc] using he

omit [DecidableEq m] in
/-- An affine model equation for coordinate stability pulls back to every test. -/
theorem isStableCoordinates_of_affine_model
    (ρ : MatrixRepresentation J n)
    {A : CommAlgCat.{u} (CommRingCat.of k)}
    (j : (algSpec (CommRingCat.of k)).obj (op A) ≅ J.X)
    (B : Matrix n m k) (C : Matrix m n k)
    (h : (ρ.affineMatrix A j.hom : Matrix n n A) * B.map (algebraMap k A) =
      B.map (algebraMap k A) *
        (C.map (algebraMap k A) * (ρ.affineMatrix A j.hom : Matrix n n A) *
          B.map (algebraMap k A))) :
    ρ.IsStableCoordinates B C := by
  let e : A →+* Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) :=
    (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have h₀ := congrArg (fun M : Matrix n m A => M.map e) h
  simp only [Matrix.map_mul, Matrix.map_map] at h₀
  have hB : (B.map (e ∘ algebraMap k A)) =
      B.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  have hC : (C.map (e ∘ algebraMap k A)) =
      C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  rw [hB, hC] at h₀
  intro T x
  let a := x ≫ j.inv
  have h₁ := congrArg
    (fun M : Matrix n m Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) =>
      M.map a.left.appTop.hom) h₀
  simp only [Matrix.map_mul, Matrix.map_map] at h₁
  have hB' : B.map (a.left.appTop.hom ∘ scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) =
      B.map (scalarMap T) := by
    ext r s
    exact scalarMap_naturality a _
  have hC' : C.map (a.left.appTop.hom ∘ scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) =
      C.map (scalarMap T) := by
    ext r s
    exact scalarMap_naturality a _
  rw [hB', hC'] at h₁
  have hM := congrArg (fun U : GL n Γ(T.left, ⊤) => (U : Matrix n n Γ(T.left, ⊤)))
    (ρ.pointMatrix_naturality a j.hom)
  have hax : a ≫ j.hom = x := by simp [a]
  rw [hax, pointMatrix_eq_affineMatrix] at hM
  change (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) =
    ((ρ.affineMatrix A j.hom : Matrix n n A).map e).map a.left.appTop.hom at hM
  rw [hM]
  simpa only [Matrix.map_map] using h₁

end Stability

end Langlands.GroupScheme.MatrixRepresentation
