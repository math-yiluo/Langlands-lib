import Langlands.GroupScheme.Lie.AdjointDifferentialCentralizer
import Langlands.GroupScheme.Lie.PointTangent
import Langlands.AlgebraicGeometry.TangentSmoothness
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.LieImage

/-! # Dominance of adjoint slice maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

open GeneralLinear.DualNumber

section Bracket

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]
  {n : Type} [Fintype n] [DecidableEq n]

variable {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- The tangent-matrix differential of a monomorphic representation is injective. -/
theorem kernelDifferential_injective (ρ : MatrixRepresentation G n) (hρ : Mono ρ.hom.hom) :
    Function.Injective (ρ.kernelDifferential A) := by
  intro x y h
  rw [MatrixRepresentation.kernelDifferential_apply,
    MatrixRepresentation.kernelDifferential_apply] at h
  apply Additive.toMul.injective
  apply lieKernelTarget_injective ρ A hρ
  exact (GeneralLinear.DualNumber.pointKernelEquiv).symm.injective h

variable {d : ℕ} (c : FiniteCoordinates G d)

/-- Finite Lie coordinates of a constant dual-number tangent vector. -/
theorem equiv_lieKernelMapLinear_ofId (x : Additive (lieKernel G R)) :
    c.equiv (.of R (DualNumber R))
        (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) x) =
      fun i => TrivSqZeroExt.inl (c.equiv (.of R R) x i) :=
  c.naturality (CommAlgCat.ofHom (Algebra.ofId R (DualNumber R))) x

/-- In finite Lie coordinates, the adjoint image of a constant tangent vector `X` under
the first-order point of `Y` has constant part `X` and epsilon part `ad(Y) X`. -/
theorem equiv_adjoint_constant (X Y : lieKernel G R) :
    c.equiv (.of R (DualNumber R)) (adjoint G (DualNumber R) Y.val
        (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) (Additive.ofMul X))) =
      fun i => TrivSqZeroExt.inl (c.equiv (.of R R) (Additive.ofMul X) i) +
        TrivSqZeroExt.inr (adjointDifferentialFamily c (Additive.ofMul Y)
          (c.equiv (.of R R) (Additive.ofMul X)) i) := by
  rw [← adjointRepresentation_affineAction]
  rw [equiv_lieKernelMapLinear_ofId, MatrixRepresentation.affineAction_apply,
    MatrixRepresentation.affineMatrix_lieKernel, adjointDifferentialFamily_apply,
    Matrix.toLin'_apply, matrixUnit_val, Matrix.add_mulVec, Matrix.one_mulVec]
  funext i
  apply TrivSqZeroExt.ext <;>
    simp [Matrix.mulVec, dotProduct, epsilonMatrix,
      TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]

omit [IsAffineHom G.X.hom] in
/-- The tangent matrix of the conjugate of a constant tangent vector `X` by the first-order
point of `Y` has constant part `ρ(X)` and epsilon part `ρ(Y) ρ(X) - ρ(X) ρ(Y)`. -/
theorem tangentMatrix_conjugation_constant (ρ : MatrixRepresentation G n) (X Y : lieKernel G R) :
    ρ.tangentMatrix (DualNumber R)
      (lieKernelConjugation G Y.val (lieKernelMap G (Algebra.ofId R (DualNumber R)) X)) =
      (ρ.tangentMatrix R X).map (TrivSqZeroExt.inlHom R R) +
        epsilonMatrix (ρ.tangentMatrix R Y * ρ.tangentMatrix R X -
          ρ.tangentMatrix R X * ρ.tangentMatrix R Y) := by
  have hY : Y.val ≫ ρ.hom.hom = pointUnit (ρ.tangentMatrix R Y) :=
    (congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix R Y)).symm
  have hX : targetMap ρ (DualNumber R) (lieKernelMap G (Algebra.ofId R (DualNumber R)) X) =
      pointKernelEquiv ((ρ.tangentMatrix R X).map (TrivSqZeroExt.inlHom R R)) := by
    rw [← ρ.pointKernelEquiv_tangentMatrix, ρ.tangentMatrix_naturality]
    rfl
  unfold MatrixRepresentation.tangentMatrix
  rw [targetMap_conjugation, hY, hX]
  exact (congrArg _ (generalLinear_conjugation_constant _ _)).trans (Equiv.symm_apply_apply _ _)

/-- The adjoint action of the first-order point of `Y` on a constant tangent vector `X`
is `X + ε ad(Y) X`. -/
theorem adjoint_constant_eq (X Y : lieKernel G R) :
    adjoint G (DualNumber R) Y.val
      (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) (Additive.ofMul X)) =
      lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) (Additive.ofMul X) +
        (TrivSqZeroExt.inr 1 : DualNumber R) •
          lieKernelMapLinear G (Algebra.ofId R (DualNumber R))
            ((c.equiv (.of R R)).symm (adjointDifferentialFamily c (Additive.ofMul Y)
              (c.equiv (.of R R) (Additive.ofMul X)))) := by
  apply (c.equiv (.of R (DualNumber R))).injective
  rw [equiv_adjoint_constant, map_add, map_smul, equiv_lieKernelMapLinear_ofId,
    equiv_lieKernelMapLinear_ofId, LinearEquiv.apply_symm_apply]
  funext i
  apply TrivSqZeroExt.ext <;> simp

/-- The tangent matrix of the adjoint image of a constant tangent vector `X` under the
first-order point of `Y`. -/
theorem tangentMatrix_adjoint_constant (ρ : MatrixRepresentation G n) (X Y : lieKernel G R) :
    ρ.kernelDifferential (DualNumber R) (adjoint G (DualNumber R) Y.val
      (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) (Additive.ofMul X))) =
      (ρ.tangentMatrix R X).map (TrivSqZeroExt.inlHom R R) +
        epsilonMatrix (ρ.tangentMatrix R Y * ρ.tangentMatrix R X -
          ρ.tangentMatrix R X * ρ.tangentMatrix R Y) := by
  rw [MatrixRepresentation.kernelDifferential_apply, adjoint_toMul, lieKernelMapLinear_toMul]
  exact tangentMatrix_conjugation_constant ρ X Y

/-- The tangent-matrix differential commutes with the constant inclusion into dual
numbers. -/
theorem kernelDifferential_lieKernelMapLinear_ofId (ρ : MatrixRepresentation G n)
    (V : Additive (lieKernel G R)) :
    ρ.kernelDifferential (DualNumber R) (lieKernelMapLinear G (Algebra.ofId R (DualNumber R)) V) =
      (ρ.kernelDifferential R V).map (TrivSqZeroExt.inlHom R R) := by
  rw [MatrixRepresentation.kernelDifferential_apply,
    MatrixRepresentation.kernelDifferential_apply, lieKernelMapLinear_toMul,
    ρ.tangentMatrix_naturality]
  rfl

/-- **The adjoint differential is the matrix commutator.** For every matrix
representation `ρ`, the tangent matrix of `ad(Y) X` is `ρ(Y) ρ(X) - ρ(X) ρ(Y)`. -/
theorem kernelDifferential_adjointDifferentialFamily (ρ : MatrixRepresentation G n)
    (X Y : lieKernel G R) :
    ρ.kernelDifferential R ((c.equiv (.of R R)).symm
        (adjointDifferentialFamily c (Additive.ofMul Y)
          (c.equiv (.of R R) (Additive.ofMul X)))) =
      ρ.tangentMatrix R Y * ρ.tangentMatrix R X -
        ρ.tangentMatrix R X * ρ.tangentMatrix R Y := by
  have hL := tangentMatrix_adjoint_constant ρ X Y
  rw [adjoint_constant_eq c, map_add, map_smul, kernelDifferential_lieKernelMapLinear_ofId,
    kernelDifferential_lieKernelMapLinear_ofId] at hL
  ext i j
  have h := congrArg (fun P : Matrix n n (DualNumber R) => (P i j).snd) hL
  simpa [epsilonMatrix] using h

/-- The adjoint differential is antisymmetric, `ad(Y) X = - ad(X) Y`, whenever some
matrix representation has injective tangent-matrix differential. -/
theorem adjointDifferentialFamily_antisymm_of_injective (ρ : MatrixRepresentation G n)
    (hρ : Function.Injective (ρ.kernelDifferential R)) (X Y : lieKernel G R) :
    adjointDifferentialFamily c (Additive.ofMul Y) (c.equiv (.of R R) (Additive.ofMul X)) =
      -adjointDifferentialFamily c (Additive.ofMul X)
        (c.equiv (.of R R) (Additive.ofMul Y)) := by
  apply eq_neg_of_add_eq_zero_left
  apply (c.equiv (.of R R)).symm.injective
  apply hρ
  rw [map_add, map_add, kernelDifferential_adjointDifferentialFamily,
    kernelDifferential_adjointDifferentialFamily, map_zero, map_zero,
    sub_add_sub_cancel, sub_self]

/-- Every Lie element is annihilated by its own adjoint differential whenever some
matrix representation has injective tangent-matrix differential. -/
theorem adjointDifferentialFamily_self_of_injective (ρ : MatrixRepresentation G n)
    (hρ : Function.Injective (ρ.kernelDifferential R)) (X : lieKernel G R) :
    adjointDifferentialFamily c (Additive.ofMul X)
        (c.equiv (.of R R) (Additive.ofMul X)) = 0 := by
  apply (c.equiv (.of R R)).symm.injective
  apply hρ
  rw [map_zero, map_zero, kernelDifferential_adjointDifferentialFamily, sub_self]

end Bracket

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

/-- An affine algebraic group over a field has a matrix representation with injective
tangent-matrix differential, namely a closed linear embedding. -/
theorem exists_injective_kernelDifferential :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      Function.Injective (ρ.kernelDifferential (CommRingCat.of k)) := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  exact ⟨N, ρ, kernelDifferential_injective ρ (Over.mono_of_mono_left _)⟩

/-- The adjoint differential is antisymmetric: `ad(Y) X = - ad(X) Y` in finite Lie
coordinates of an affine algebraic group over a field. -/
theorem adjointDifferentialFamily_antisymm (X Y : lieKernel G k) :
    adjointDifferentialFamily c (Additive.ofMul Y)
        (c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul X)) =
      -adjointDifferentialFamily c (Additive.ofMul X)
        (c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul Y)) := by
  obtain ⟨N, ρ, hρ⟩ := exists_injective_kernelDifferential (G := G)
  exact adjointDifferentialFamily_antisymm_of_injective c ρ hρ X Y

/-- Every Lie element is annihilated by its own adjoint differential. -/
theorem adjointDifferentialFamily_self (X : lieKernel G k) :
    adjointDifferentialFamily c (Additive.ofMul X)
        (c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul X)) = 0 := by
  obtain ⟨N, ρ, hρ⟩ := exists_injective_kernelDifferential (G := G)
  exact adjointDifferentialFamily_self_of_injective c ρ hρ X

/-- In finite Lie coordinates the adjoint tangent matrix of `ξ` sends the coordinates of `Y`
to `-ad(Y) ξ`. -/
theorem adjointRepresentation_tangentMatrix_mulVec (ξ : lieKernel G k) (v : Fin d → k) :
    (adjointRepresentation c).tangentMatrix k ξ *ᵥ v =
      -adjointDifferentialFamily c ((c.equiv (.of (CommRingCat.of k) k)).symm v)
        (c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul ξ)) := by
  have key := adjointDifferentialFamily_antisymm c
    (Additive.toMul ((c.equiv (.of (CommRingCat.of k) k)).symm v)) ξ
  rw [ofMul_toMul, LinearEquiv.apply_symm_apply] at key
  rw [← key, adjointDifferentialFamily_apply, Matrix.toLin'_apply]

end Field

section Slice

open MatrixRepresentation

variable {R : CommRingCat.{u}} {n e : Type} [Fintype n] [DecidableEq n] [Fintype e]

/-- The linear morphism `𝔸^e ⟶ 𝔸^n` of affine coordinate spaces given by a matrix with base
coefficients. -/
def linearPoint (B : Matrix n e R) : coefficientSpace e R ⟶ coefficientSpace n R :=
  coefficientPoint _ (B.map (scalarMap _) *ᵥ coefficientCoordinates (𝟙 _))

omit [Fintype n] [DecidableEq n] in
/-- On every scheme test the linear morphism is multiplication by the matrix. -/
theorem coefficientCoordinates_linearPoint (B : Matrix n e R) {T : Over (Spec R)}
    (x : T ⟶ coefficientSpace e R) :
    coefficientCoordinates (x ≫ linearPoint B) =
      B.map (scalarMap T) *ᵥ coefficientCoordinates x := by
  rw [coefficientCoordinates_comp]
  simp only [linearPoint, coefficientCoordinates_coefficientPoint]
  funext i
  rw [RingHom.map_mulVec]
  congr 1
  · ext a b
    exact scalarMap_comp x (B a b)

variable {G : GroupScheme (Spec R)}

/-- The slice map `G × 𝔸^e ⟶ 𝔸^n`, `(g, t) ↦ ρ(g) (B t)`, of a matrix representation `ρ`
and a matrix `B` with base coefficients. -/
def sliceMap (ρ : MatrixRepresentation G n) (B : Matrix n e R) :
    G.X ⊗ coefficientSpace e R ⟶ coefficientSpace n R :=
  lift (fst _ _) (snd _ _ ≫ linearPoint B) ≫ ρ.coefficientActionHom

/-- On every scheme test the slice map is `(g, t) ↦ ρ(g) (B t)`. -/
theorem coefficientCoordinates_sliceMap (ρ : MatrixRepresentation G n) (B : Matrix n e R)
    {T : Over (Spec R)} (g : T ⟶ G.X) (x : T ⟶ coefficientSpace e R) :
    coefficientCoordinates (lift g x ≫ sliceMap ρ B) =
      (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (B.map (scalarMap T) *ᵥ coefficientCoordinates x) := by
  rw [sliceMap, ← Category.assoc, comp_lift, lift_fst, ← Category.assoc, lift_snd,
    coefficientCoordinates_actionHom, coefficientCoordinates_linearPoint]

/-- Pulling back a section of `Spec A` along `Spec φ`. -/
private theorem appTop_SpecMap_ΓSpecIso_inv {A B : CommRingCat.{u}} (φ : A ⟶ B) (z : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv z) = (Scheme.ΓSpecIso B).inv (φ z) :=
  (CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) z).symm

/-- Global sections of an affine test scheme, identified with the test algebra. -/
theorem ΓSpecIso_hom_scalarMap (S : CommAlgCat.{u} R) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom (scalarMap ((algSpec R).obj (op S)) r) =
      algebraMap R S r := by
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop ((Scheme.ΓSpecIso R).inv r)) = _
  exact (congrArg _ (appTop_SpecMap_ΓSpecIso_inv _ r)).trans (Iso.inv_hom_id_apply _ _)

/-- The affine matrix of a dual-number tangent point is `1 + ε ρ(X)`. -/
theorem affineMatrix_lieKernel_eq (ρ : MatrixRepresentation G n)
    (A : Type u) [CommRing A] [Algebra R A] (X : lieKernel G A) :
    ρ.affineMatrix (CommAlgCat.of R (DualNumber A)) X.val =
      matrixUnit (ρ.tangentMatrix A X) := by
  have h := congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix A X)
  change pointUnit (ρ.tangentMatrix A X) = X.val ≫ ρ.hom.hom at h
  rw [affineMatrix_apply, ← h, pointUnit_matrix]

/-- On an affine test scheme `Spec S`, the slice map in the coordinates of `S` is
`(g, t) ↦ ρ(g) (B t)`. -/
theorem affineCoordinates_sliceMap (ρ : MatrixRepresentation G n) (B : Matrix n e R)
    (S : CommAlgCat.{u} R) (g : (algSpec R).obj (op S) ⟶ G.X)
    (x : (algSpec R).obj (op S) ⟶ coefficientSpace e R) :
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of S)).hom
        (coefficientCoordinates (lift g x ≫ sliceMap ρ B) i)) =
      (ρ.affineMatrix S g : Matrix n n S) *ᵥ (B.map (algebraMap R S) *ᵥ
        fun j => (Scheme.ΓSpecIso (CommRingCat.of S)).hom (coefficientCoordinates x j)) := by
  rw [coefficientCoordinates_sliceMap]
  funext i
  rw [RingHom.map_mulVec]
  congr 1
  · ext a b
    rw [Matrix.map_apply, pointMatrix_eq_affineMatrix]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of S)) _
  · funext j
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    ext a b
    exact ΓSpecIso_hom_scalarMap S (B a b)

end Slice

section SliceField

open MatrixRepresentation Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.TangentSmoothness

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n e : Type} [Fintype n] [DecidableEq n] [Fintype e]

/-- The rational point `(1, t₀)` of `G × 𝔸^e`. -/
def slicePoint (t₀ : e → k) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ coefficientSpace e (CommRingCat.of k) :=
  lift 1 (constantCoefficientPoint t₀)

/-- Global sections of the base, identified with `k`. -/
private theorem scalarMap_base (r : k) :
    scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) r =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv r := rfl

omit [Fintype n] [DecidableEq n] in
private theorem mulVec_algebraMap_inl_add_inr {m : Type} [Fintype m] (M : Matrix n m k)
    (a b : m → k) :
    M.map (algebraMap k (DualNumber k)) *ᵥ
        (fun j => TrivSqZeroExt.inl (a j) + TrivSqZeroExt.inr (b j)) =
      fun i => TrivSqZeroExt.inl ((M *ᵥ a) i) + TrivSqZeroExt.inr ((M *ᵥ b) i) := by
  funext i
  apply TrivSqZeroExt.ext <;>
    simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.snd_sum]

omit [DecidableEq n] in
private theorem epsilonMatrix_mulVec_inl_add_inr (M : Matrix n n k) (a b : n → k) :
    epsilonMatrix M *ᵥ (fun j => TrivSqZeroExt.inl (a j) + TrivSqZeroExt.inr (b j)) =
      fun i => TrivSqZeroExt.inr ((M *ᵥ a) i) := by
  funext i
  apply TrivSqZeroExt.ext <;>
    simp [Matrix.mulVec, dotProduct, epsilonMatrix, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.snd_sum]

/-- The augmentation `Spec k ⟶ Spec k[ε]` on global sections is the constant part. -/
private theorem dualNumberAugmentation_appTop_ΓSpecIso_inv (z : DualNumber k) :
    (dualNumberAugmentation k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv z) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv z.fst := by
  rw [dualNumberAugmentation, appTop_SpecMap_ΓSpecIso_inv]
  rfl

/-- **Tangent surjectivity of the slice map.** If every vector `v` is of the form
`ρ(ξ) (B t₀) + B t'` for a Lie element `ξ` and a vector `t'`, then the slice map
`(g, t) ↦ ρ(g) (B t)` is surjective on rational tangent vectors at `(1, t₀)`. -/
theorem isTangentSurjectiveAt_sliceMap [IsAffineHom G.X.hom] (ρ : MatrixRepresentation G n)
    (B : Matrix n e k) (t₀ : e → k)
    (h : ∀ v : n → k, ∃ (ξ : lieKernel G k) (t' : e → k),
      ρ.tangentMatrix k ξ *ᵥ (B *ᵥ t₀) + B *ᵥ t' = v) :
    IsTangentSurjectiveAt (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom
      (coefficientSpace n (CommRingCat.of k)).hom (sliceMap ρ B).left
      (slicePoint (G := G) t₀).left := by
  rintro t ⟨ht₁, ht₂⟩
  let tt : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))) ⟶
      coefficientSpace n (CommRingCat.of k) := Over.homMk t ht₁
  let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))) :=
    Over.homMk (dualNumberAugmentation k) (dualNumberAugmentation_comp_dualNumberProjection)
  let w : n → DualNumber k := fun i =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom (coefficientCoordinates tt i)
  have hw : ∀ i, coefficientCoordinates tt i =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv (w i) := fun i =>
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))) _).symm
  -- The base of the tangent vector is `B t₀`.
  have hfst : ∀ i, (w i).fst = (B *ᵥ t₀) i := by
    have hat : a ≫ tt = slicePoint t₀ ≫ sliceMap ρ B := Over.OverMorphism.ext ht₂
    have hc := congrArg coefficientCoordinates hat
    rw [slicePoint, coefficientCoordinates_sliceMap, map_one,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, constantCoefficientPoint,
      coefficientCoordinates_coefficientPoint, coefficientCoordinates_comp] at hc
    intro i
    have hi := congrFun hc i
    change (dualNumberAugmentation k).appTop (coefficientCoordinates tt i) = _ at hi
    rw [hw, dualNumberAugmentation_appTop_ΓSpecIso_inv] at hi
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
    rw [hi, RingHom.map_mulVec]
    rfl
  obtain ⟨ξ, t', hξ⟩ := h fun i => (w i).snd
  let y : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))) ⟶
      coefficientSpace e (CommRingCat.of k) :=
    coefficientPoint _ fun j => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv
      (TrivSqZeroExt.inl (t₀ j) + TrivSqZeroExt.inr (t' j))
  let s : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))) ⟶
      G.X ⊗ coefficientSpace e (CommRingCat.of k) := lift ξ.val y
  have hy : ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom
      (coefficientCoordinates y j) = TrivSqZeroExt.inl (t₀ j) + TrivSqZeroExt.inr (t' j) := by
    intro j
    rw [coefficientCoordinates_coefficientPoint]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))) _
  have hs₁ : a ≫ s = slicePoint t₀ := by
    rw [comp_lift, slicePoint]
    congr 1
    · exact Over.OverMorphism.ext ((kernelTangentEquiv G ξ).property.2)
    · apply coefficientCoordinates_injective
      rw [coefficientCoordinates_comp, constantCoefficientPoint,
        coefficientCoordinates_coefficientPoint, coefficientCoordinates_coefficientPoint]
      funext j
      change (dualNumberAugmentation k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv _) = _
      rw [dualNumberAugmentation_appTop_ΓSpecIso_inv]
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      rfl
  have hs₂ : s ≫ sliceMap ρ B = tt := by
    apply coefficientCoordinates_injective
    funext i
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom).1
    have hc := congrFun (affineCoordinates_sliceMap ρ B
      (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) ξ.val y) i
    simp only [hy] at hc
    rw [affineMatrix_lieKernel_eq, matrixUnit_val, Matrix.add_mulVec,
      Matrix.one_mulVec, mulVec_algebraMap_inl_add_inr, epsilonMatrix_mulVec_inl_add_inr] at hc
    refine hc.trans ?_
    change _ = w i
    apply TrivSqZeroExt.ext
    · simp [hfst i]
    · have := congrFun hξ i
      simp only [Pi.add_apply] at this
      simp [← this, add_comm]
  exact ⟨s.left, ⟨Over.w s, congrArg CommaMorphism.left hs₁⟩, congrArg CommaMorphism.left hs₂⟩

/-- **Dominance of the slice map.** For a smooth affine group `G` over a field `k`, if every
vector `v` is of the form `ρ(ξ) (B t₀) + B t'` for a Lie element `ξ` and a vector `t'`, then
the slice map `(g, t) ↦ ρ(g) (B t)` from `G × 𝔸^e` to `𝔸^n` has dense range. -/
theorem denseRange_sliceMap [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (ρ : MatrixRepresentation G n) (B : Matrix n e k) (t₀ : e → k)
    (h : ∀ v : n → k, ∃ (ξ : lieKernel G k) (t' : e → k),
      ρ.tangentMatrix k ξ *ᵥ (B *ᵥ t₀) + B *ᵥ t' = v) :
    DenseRange (sliceMap ρ B).left := by
  have : Smooth (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom :=
    smooth_tensor _ _ inferInstance
      (inferInstanceAs (Smooth (𝔸(ULift.{u} e; Spec (CommRingCat.of k)) ↘ _)))
  have : IrreducibleSpace (coefficientSpace n (CommRingCat.of k)).left :=
    inferInstanceAs (IrreducibleSpace 𝔸(ULift.{u} n; Spec (CommRingCat.of k)))
  have : LocallyOfFiniteType (coefficientSpace n (CommRingCat.of k)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝔸(ULift.{u} n; Spec (CommRingCat.of k)) ↘ _))
  exact denseRange_of_isTangentSurjectiveAt _ (Over.w _) (Over.w (slicePoint (G := G) t₀))
    (isTangentSurjectiveAt_sliceMap ρ B t₀ h)

/-- If the kernel of a linear endomorphism meets its image only in `0`, then its image and
every subspace containing its kernel together span the space. -/
theorem range_sup_eq_top_of_ker_le {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : V →ₗ[k] V) (W : Submodule k V) (hker : LinearMap.ker f ≤ W)
    (hdisj : Disjoint (LinearMap.ker f) (LinearMap.range f)) :
    LinearMap.range f ⊔ W = ⊤ := by
  have htop : LinearMap.range f ⊔ LinearMap.ker f = ⊤ :=
    Submodule.eq_top_of_disjoint _ _ (LinearMap.finrank_range_add_finrank_ker f).ge
      hdisj.symm
  exact eq_top_iff.mpr (htop.ge.trans (sup_le_sup_left hker _))

/-- **Dominance of the adjoint slice map.** Let `G` be a smooth affine group over a field `k`
with finite Lie coordinates `c`, let `B` be a matrix and `t₀` a vector, and let `Y₀` be the
Lie element with coordinates `B t₀`. If the image of `ad(Y₀)` and the column space of `B`
together span the coordinate space, then the adjoint slice map `(g, t) ↦ Ad(g) (B t)` from
`G × 𝔸^e` to `𝔸^d` has dense range. -/
theorem denseRange_adjointSliceMap [IsAffineHom G.X.hom] [Smooth G.X.hom] {d : ℕ}
    (c : FiniteCoordinates G d) (B : Matrix (Fin d) e k) (t₀ : e → k)
    (h : LinearMap.range (adjointDifferentialFamily c
        ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ t₀))) ⊔
      LinearMap.range B.mulVecLin = ⊤) :
    DenseRange (sliceMap (adjointRepresentation c) B).left := by
  refine denseRange_sliceMap _ B t₀ fun v => ?_
  obtain ⟨u, ⟨u', rfl⟩, w, ⟨t', rfl⟩, huw⟩ :=
    Submodule.mem_sup.mp (h.ge (Submodule.mem_top (x := v)))
  refine ⟨Additive.toMul ((c.equiv (.of (CommRingCat.of k) k)).symm (-u')), t', ?_⟩
  rw [← huw, Matrix.mulVecLin_apply, adjointRepresentation_tangentMatrix_mulVec, ofMul_toMul,
    LinearEquiv.apply_symm_apply, LinearMap.map_neg, neg_neg]

/-- **Dominance of the adjoint slice map, kernel form.** If the column space of `B` contains
the kernel of `ad(Y₀)`, `Y₀` the Lie element with coordinates `B t₀`, and that kernel meets
the image of `ad(Y₀)` only in `0`, then `(g, t) ↦ Ad(g) (B t)` has dense range. -/
theorem denseRange_adjointSliceMap_of_ker_le [IsAffineHom G.X.hom] [Smooth G.X.hom] {d : ℕ}
    (c : FiniteCoordinates G d) (B : Matrix (Fin d) e k) (t₀ : e → k)
    (hker : LinearMap.ker (adjointDifferentialFamily c
        ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ t₀))) ≤ LinearMap.range B.mulVecLin)
    (hdisj : Disjoint
      (LinearMap.ker (adjointDifferentialFamily c
        ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ t₀))))
      (LinearMap.range (adjointDifferentialFamily c
        ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ t₀))))) :
    DenseRange (sliceMap (adjointRepresentation c) B).left :=
  denseRange_adjointSliceMap c B t₀ (range_sup_eq_top_of_ker_le _ _ hker hdisj)

end SliceField

end Langlands.GroupScheme.Lie
