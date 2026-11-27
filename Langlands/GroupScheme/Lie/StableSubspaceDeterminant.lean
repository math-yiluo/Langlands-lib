import Langlands.GroupScheme.Lie.FiniteAction
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Torus.Weights
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # Determinant characters on stable subspaces of the actual Lie algebra

Let `G` be an affine group scheme locally of finite type over a field `k`, `l : M ⟶ G` a
homomorphism and `V` a `k`-subspace of the actual Lie algebra `Lie(G)(k)`. For a test algebra
`A`, the scalar extension `A ⊗ V` embeds in `Lie(G)(A)`. When the adjoint operator of every
point of `M` through `l` preserves these images, the determinants of the induced operators on
`A ⊗ V` form a rational character of `M`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (V : Submodule k (Additive (lieKernel G k)))

section Extension

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The scalar extension `A ⊗ V → Lie(G)(A)` of a base subspace `V`. -/
def subspaceExtension : A ⊗[k] V →ₗ[A] Additive (lieKernel G A) :=
  (kernelScalarExtension G A).toLinearMap ∘ₗ V.subtype.baseChange A

variable {A}

@[simp] theorem subspaceExtension_tmul (a : A) (v : V) :
    subspaceExtension G V A (a ⊗ₜ v) =
      a • lieKernelMapLinear G (Algebra.ofId k A) (v : Additive (lieKernel G k)) := by
  simp [subspaceExtension]

variable (A)

/-- Over a field the scalar extension of a subspace embeds into the extended Lie algebra. -/
theorem subspaceExtension_injective : Function.Injective (subspaceExtension G V A) := by
  have h : Function.Injective (V.subtype.baseChange A) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ V.injective_subtype
  exact (kernelScalarExtension G A).injective.comp h

/-- The scalar extension of a subspace is natural in the test algebra. -/
theorem subspaceExtension_naturality {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (x : A ⊗[k] V) :
    lieKernelMapLinear G f (subspaceExtension G V A x) =
      subspaceExtension G V B (TensorProduct.map f.toLinearMap LinearMap.id x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    simp only [subspaceExtension_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.map_smulₛₗ, lieKernelMapLinear_base]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Extension

omit [LocallyOfFiniteType G.X.hom] in
/-- Coordinates in a base-changed basis are natural in the test algebra. -/
theorem baseChange_repr_map {J : Type*} (b : Module.Basis J k V)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : A ⊗[k] V) (i : J) :
    (b.baseChange B).repr (TensorProduct.map f.toLinearMap LinearMap.id x) i =
      f ((b.baseChange A).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      Module.Basis.baseChange_repr_tmul, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.coe_add, Pi.add_apply, hx, hy]

variable {M : GroupScheme (Spec (CommRingCat.of k))} (l : M ⟶ G)

/-- The subspace `V` is stable for `M` acting through `l` and the adjoint representation: after
every scalar extension, the adjoint operator of every point of `M` preserves the image of the
extended subspace. -/
def IsAdjointStable : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (m : AffinePoints M A) (x : A ⊗[k] V),
    adjoint G A (m ≫ l.hom.hom) (subspaceExtension G V A x) ∈
      LinearMap.range (subspaceExtension G V A)

variable {G V l}

section Operator

variable (hV : IsAdjointStable G V l) (A : Type u) [CommRing A] [Algebra k A]

/-- The operator induced by a point of `M` on the scalar extension of a stable subspace. -/
def stableOperator (m : AffinePoints M A) : Module.End A (A ⊗[k] V) :=
  (LinearEquiv.ofInjective _ (subspaceExtension_injective G V A)).symm.toLinearMap ∘ₗ
    ((adjoint G A (m ≫ l.hom.hom)).comp (subspaceExtension G V A)).codRestrict
      (LinearMap.range (subspaceExtension G V A)) (hV A m)

/-- The induced operator is the restriction of the adjoint operator. -/
theorem subspaceExtension_stableOperator (m : AffinePoints M A) (x : A ⊗[k] V) :
    subspaceExtension G V A (stableOperator hV A m x) =
      adjoint G A (m ≫ l.hom.hom) (subspaceExtension G V A x) := by
  let e := LinearEquiv.ofInjective _ (subspaceExtension_injective G V A)
  have h := LinearEquiv.ofInjective_apply (subspaceExtension G V A)
    (h := subspaceExtension_injective G V A)
    (e.symm (((adjoint G A (m ≫ l.hom.hom)).comp (subspaceExtension G V A)).codRestrict
      (LinearMap.range (subspaceExtension G V A)) (hV A m) x))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The induced operators form a representation of the points of `M`. -/
def stableOperatorHom : AffinePoints M A →* Module.End A (A ⊗[k] V) where
  toFun := stableOperator hV A
  map_one' := by
    apply LinearMap.ext
    intro x
    apply subspaceExtension_injective G V A
    rw [subspaceExtension_stableOperator, MonObj.one_comp, map_one]
    rfl
  map_mul' m m' := by
    apply LinearMap.ext
    intro x
    apply subspaceExtension_injective G V A
    rw [Module.End.mul_apply, subspaceExtension_stableOperator, subspaceExtension_stableOperator,
      subspaceExtension_stableOperator, MonObj.mul_comp, map_mul, Module.End.mul_apply]

@[simp] theorem stableOperatorHom_apply (m : AffinePoints M A) :
    stableOperatorHom hV A m = stableOperator hV A m := rfl

/-- The induced operators commute with every change of test algebra. -/
theorem stableOperator_naturality {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (m : AffinePoints M A) (x : A ⊗[k] V) :
    stableOperator hV B (affineMap M f m) (TensorProduct.map f.toLinearMap LinearMap.id x) =
      TensorProduct.map f.toLinearMap LinearMap.id (stableOperator hV A m x) := by
  apply subspaceExtension_injective G V B
  rw [subspaceExtension_stableOperator, ← subspaceExtension_naturality,
    ← subspaceExtension_naturality, subspaceExtension_stableOperator, adjoint_naturality]
  congr 2

end Operator

section Character

variable (hV : IsAdjointStable G V l)

/-- The matrices of the induced operators in the base change of a chosen basis of `V`. -/
def stableMatrix (A : CommAlgCat.{u} (CommRingCat.of k)) :
    M.affinePoints A →* GL (Fin (Module.finrank k V)) A :=
  (((LinearMap.toMatrixAlgEquiv ((Module.finBasis k V).baseChange A)).toRingEquiv.toMonoidHom).comp
    (stableOperatorHom hV A)).toHomUnits

theorem stableMatrix_val (A : CommAlgCat.{u} (CommRingCat.of k)) (m : M.affinePoints A) :
    (stableMatrix hV A m : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) A) =
      LinearMap.toMatrix ((Module.finBasis k V).baseChange A)
        ((Module.finBasis k V).baseChange A) (stableOperator hV A m) :=
  rfl

theorem stableMatrix_apply (A : CommAlgCat.{u} (CommRingCat.of k)) (m : M.affinePoints A)
    (i j : Fin (Module.finrank k V)) :
    (stableMatrix hV A m : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) A) i j =
      ((Module.finBasis k V).baseChange A).repr
        (stableOperator hV A m (((Module.finBasis k V).baseChange A) j)) i :=
  LinearMap.toMatrix_apply _ _ _ i j

/-- The matrices are natural under every change of test algebra. -/
theorem stableMatrix_naturality {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B)
    (m : M.affinePoints A) :
    stableMatrix hV B (M.affinePointMap f m) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (stableMatrix hV A m) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, stableMatrix_apply, stableMatrix_apply]
  let b := Module.finBasis k V
  have hj : (b.baseChange B) j =
      TensorProduct.map f.hom.toLinearMap LinearMap.id ((b.baseChange A) j) := by
    simp only [Module.Basis.baseChange_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      AlgHom.toLinearMap_apply, map_one]
  rw [hj]
  have hm : stableOperator hV B (M.affinePointMap f m)
      (TensorProduct.map f.hom.toLinearMap LinearMap.id ((b.baseChange A) j)) =
      TensorProduct.map f.hom.toLinearMap LinearMap.id (stableOperator hV A m ((b.baseChange A) j)) :=
    stableOperator_naturality hV f.hom m ((b.baseChange A) j)
  rw [hm, baseChange_repr_map]
  rfl

variable [IsAffine M.X.left]

/-- The rational determinant character of `M` on a stable subspace of the Lie algebra. -/
def stableDeterminantCharacter : rationalCharacters M :=
  characterRestrict
    (AffineCoordinates.matrixRepresentationOfAffinePoints M (stableMatrix hV)
      (stableMatrix_naturality hV))
    (GeneralLinear.determinantCharacter (Fin (Module.finrank k V)) (CommRingCat.of k))

/-- On every test scheme the character is the determinant of the algebraic representation. -/
theorem stableDeterminantCharacter_eval (T : Over (Spec (CommRingCat.of k))) (m : T ⟶ M.X) :
    characterEval (stableDeterminantCharacter hV) T m =
      Matrix.GeneralLinearGroup.det
        ((AffineCoordinates.matrixRepresentationOfAffinePoints M (stableMatrix hV)
          (stableMatrix_naturality hV)).pointMatrix T m) := by
  rw [stableDeterminantCharacter, characterEval_characterRestrict,
    GeneralLinear.characterEval_determinantCharacter]
  rfl

/-- On every affine test the value is the determinant of the constructed matrix, transported
to global sections. -/
theorem stableDeterminantCharacter_eval_affine (A : CommAlgCat.{u} (CommRingCat.of k))
    (m : M.affinePoints A) :
    characterEval (stableDeterminantCharacter hV) ((algSpec (CommRingCat.of k)).obj (op A)) m =
      Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom
        (Matrix.GeneralLinearGroup.det (stableMatrix hV A m)) := by
  rw [stableDeterminantCharacter_eval, MatrixRepresentation.pointMatrix_eq_affineMatrix,
    AffineCoordinates.matrixRepresentationOfAffinePoints_affineMatrix]
  exact Matrix.GeneralLinearGroup.map_det _ _

/-- On every affine test the character takes the determinant of the constructed matrix. -/
theorem stableDeterminantCharacter_affinePoints (A : CommAlgCat.{u} (CommRingCat.of k))
    (m : M.affinePoints A) :
    Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
        (m ≫ (stableDeterminantCharacter hV).toMul.hom.hom) =
      Matrix.GeneralLinearGroup.det (stableMatrix hV A m) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (characterEval (stableDeterminantCharacter hV)
      ((algSpec (CommRingCat.of k)).obj (op A)) m).val = _
  rw [stableDeterminantCharacter_eval_affine]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv
      (Matrix.GeneralLinearGroup.det (stableMatrix hV A m)).val) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id _

omit [IsAffine M.X.left] in
/-- The determinant of the constructed matrix is the determinant of the induced operator. -/
theorem stableMatrix_det (A : CommAlgCat.{u} (CommRingCat.of k)) (m : M.affinePoints A) :
    ((Matrix.GeneralLinearGroup.det (stableMatrix hV A m) : Aˣ) : A) =
      LinearMap.det (stableOperator hV A m) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, stableMatrix_val, LinearMap.det_toMatrix]

end Character

section Torus

/-- Rational characters of an affine commutative group scheme agree if their values agree at
every affine point. -/
theorem rationalCharacters_ext_affine {S : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffine S.X.left] {χ ψ : rationalCharacters S.toGrp}
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (t : Lie.AffinePoints S.toGrp A),
      Lie.characterValue ((rationalCharacters.equivCharacterLattice S) χ) t =
        Lie.characterValue ((rationalCharacters.equivCharacterLattice S) ψ) t) : χ = ψ := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  let e := (Grp.forget _).mapIso (AffineCoordinates.coordinateCogroupIso S.toGrp)
  apply (cancel_epi e.hom).mp
  exact (Gm.affinePointsEquiv _).injective (h (AffineCoordinates.algebra S.toGrp) e.hom)

variable (hV : IsAdjointStable G V l) {S : CommGroupScheme (Spec (CommRingCat.of k))}
  (s : S.toGrp ⟶ M) {J : Type*} (e : Module.Basis J k V) (w : J → characterLattice S)
  (he : ∀ j, ((e j : V) : Additive (lieKernel G k)) ∈ weightSpace (s ≫ l) (w j))

include he in
/-- On a basis of weight vectors the operators of torus points are diagonal. -/
theorem stableOperator_weightBasis (A : Type u) [CommRing A] [Algebra k A]
    (t : AffinePoints S.toGrp A) (j : J) :
    stableOperator hV A (t ≫ s.hom.hom) (e.baseChange A j) =
      (characterValue (w j) t : A) • e.baseChange A j := by
  apply subspaceExtension_injective G V A
  rw [subspaceExtension_stableOperator, map_smul, Module.Basis.baseChange_apply,
    subspaceExtension_tmul, one_smul]
  have h := he j A t
  rw [Grp.comp_hom_hom, ← Category.assoc] at h
  exact h

include he in
/-- The determinant of a torus point is the product of the characters of a weight basis. -/
theorem det_stableOperator_weightBasis [Fintype J] [DecidableEq J]
    (A : Type u) [CommRing A] [Algebra k A] (t : AffinePoints S.toGrp A) :
    LinearMap.det (stableOperator hV A (t ≫ s.hom.hom)) =
      ∏ j, (characterValue (w j) t : A) := by
  rw [← LinearMap.det_toMatrix (e.baseChange A)]
  have hd : LinearMap.toMatrix (e.baseChange A) (e.baseChange A)
      (stableOperator hV A (t ≫ s.hom.hom)) =
      Matrix.diagonal (fun j => (characterValue (w j) t : A)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, stableOperator_weightBasis hV s e w he A t j, map_smul,
      Module.Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [hd, Matrix.det_diagonal]

variable [IsAffine M.X.left]

include he in
/-- **Torus restriction.** Restricted to a commutative group scheme `S` acting through `s`, the
determinant character on a stable subspace with a basis of weight vectors is the sum of their
weights. -/
theorem characterRestrict_stableDeterminantCharacter [IsAffine S.X.left] [Fintype J]
    [DecidableEq J] :
    characterRestrict s (stableDeterminantCharacter hV) =
      ∑ j, (rationalCharacters.equivCharacterLattice S).symm (w j) := by
  apply rationalCharacters_ext_affine
  intro A t
  have hR : Lie.characterValue ((rationalCharacters.equivCharacterLattice S)
      (∑ j, (rationalCharacters.equivCharacterLattice S).symm (w j))) t =
        ∏ j, Lie.characterValue (w j) t := by
    rw [map_sum]
    simp only [AddEquiv.apply_symm_apply]
    change Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
      (t ≫ (CommGroupScheme.groupHom (∑ j, w j)).hom.hom) = _
    rw [comp_groupHom_sum, map_prod]
    rfl
  rw [hR]
  change Gm.affinePointsEquiv _
    (t ≫ (characterRestrict s (stableDeterminantCharacter hV)).toMul.hom.hom) = _
  rw [characterRestrict_apply, Grp.comp_hom_hom, ← Category.assoc]
  refine (stableDeterminantCharacter_affinePoints hV A (t ≫ s.hom.hom)).trans ?_
  apply Units.ext
  rw [stableMatrix_det, Units.coe_prod]
  exact det_stableOperator_weightBasis hV s e w he A t

end Torus

end Langlands.GroupScheme.Lie
