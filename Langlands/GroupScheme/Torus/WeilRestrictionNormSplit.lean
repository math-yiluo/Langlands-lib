import Langlands.Algebra.TensorNormSplit
import Langlands.GroupScheme.Torus.WeilRestrictionNorm
import Langlands.GroupScheme.Torus.WeilRestrictionDecomposition

/-! # Scalar and norm morphisms in splitting coordinates -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

section Algebra

variable (A A' B R : Type u) [CommRing A] [CommRing A'] [CommRing B] [CommRing R]
  [Algebra A A'] [Algebra A B] [Algebra A' R] [Algebra A R] [IsScalarTower A A' R]
  (I : Type u) [Fintype I] [DecidableEq I] (e : A' ⊗[A] B ≃ₐ[A'] (I → A'))

/-- The coefficient-first version of the algebra decomposition, as an `R`-algebra equivalence. -/
def normDecompositionEquiv : R ⊗[A] B ≃ₐ[R] (I → R) :=
  (Algebra.TensorProduct.cancelBaseChange A A' R R B).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := R)) e).trans
      (Algebra.TensorProduct.piScalarRight A' R R I))

/-- The coefficient-first and coefficient-last decompositions have the same coordinates. -/
theorem normDecompositionEquiv_comm (x : B ⊗[A] R) :
    normDecompositionEquiv A A' B R I e (Algebra.TensorProduct.comm A B R x) =
      decompositionTensorEquiv A A' B R I e x := by
  induction x using TensorProduct.inductionOn with
  | tmul b r =>
      simp [normDecompositionEquiv, decompositionTensorEquiv_tmul]
      rfl
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- In any product decomposition the norm is the product of all coordinates. -/
theorem tensorNorm_decomposition (x : B ⊗[A] R) :
    Langlands.Algebra.tensorNorm A B R x =
      ∏ i, decompositionTensorEquiv A A' B R I e x i := by
  rw [Langlands.Algebra.tensorNorm_eq_prod (normDecompositionEquiv A A' B R I e),
    normDecompositionEquiv_comm]

end Algebra

section Scheme

variable (A A' : CommRingCat.{u}) [Algebra A A'] (B : Type u) [CommRing B]
  [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (I : Type u) [Fintype I] [DecidableEq I] (e : A' ⊗[A] B ≃ₐ[A'] (I → A'))

/-- The base change of the norm character, with the canonical multiplicative-group comparison. -/
def decompositionNormHom :
    ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)) ⟶ Gm (Spec A') :=
  characterLattice.baseChange (baseMap A A') (commGroupScheme A B) (normHom A B)

/-- The base change of the scalar cocharacter, with the canonical multiplicative-group comparison. -/
def decompositionScalarHom :
    Gm (Spec A') ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)) :=
  (Gm.commBaseChangeIso (baseMap A A')).inv ≫
    (CommGroupScheme.baseChange (baseMap A A')).map (scalarHom A B)

omit [DecidableEq I] in
/-- A splitting coordinate is obtained by the induced decomposition of the tensor unit. -/
theorem decompositionPointsEquiv_apply (T : Over (Spec A'))
    (x : T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)).X)
    (i : I) :
    ((decompositionPointsEquiv A A' B I e T x i : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) =
      decompositionTensorEquiv A A' B (restrictedSections A A' T) I e
        (pointsEquiv A B ((Over.map (baseMap A A')).obj T)
          (GroupScheme.baseChangePointsEquiv (baseMap A A') (groupScheme A B) T x)) i :=
  rfl

/-- On every test scheme, the base-changed norm is the product of the splitting coordinates. -/
theorem decompositionNormHom_points (T : Over (Spec A'))
    (x : T ⟶ ((CommGroupScheme.baseChange (baseMap A A')).obj (commGroupScheme A B)).X) :
    Gm.pointsEquiv (Spec A') T
        (x ≫ (CommGroupScheme.groupHom (decompositionNormHom A A' B)).hom.hom) =
      ∏ i, decompositionPointsEquiv A A' B I e T x i := by
  rw [decompositionNormHom, characterLattice.baseChange_apply, comp_groupHom_comp]
  change Gm.pointsEquiv (Spec A') T
    ((x ≫ ((GroupScheme.baseChange (baseMap A A')).map (norm A B)).hom.hom) ≫
      (Gm.baseChangeIso (baseMap A A')).hom.hom.hom) = _
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_comp, norm_points]
  apply Units.ext
  simp only [← Units.coeHom_apply, map_prod]
  change Langlands.Algebra.tensorNorm A B (restrictedSections A A' T) _ = _
  rw [tensorNorm_decomposition A A' B (restrictedSections A A' T) I e]
  rfl

omit [DecidableEq I] in
/-- On every test scheme, the base-changed scalar cocharacter is the diagonal map. -/
theorem decompositionScalarHom_points (T : Over (Spec A'))
    (x : T ⟶ (Gm (Spec A')).X) :
    decompositionPointsEquiv A A' B I e T
        (x ≫ (CommGroupScheme.groupHom (decompositionScalarHom A A' B)).hom.hom) =
      fun _ => Gm.pointsEquiv (Spec A') T x := by
  funext i
  apply Units.ext
  rw [decompositionPointsEquiv_apply, decompositionScalarHom, comp_groupHom_comp]
  change decompositionTensorEquiv A A' B (restrictedSections A A' T) I e
    (pointsEquiv A B ((Over.map (baseMap A A')).obj T)
      (GroupScheme.baseChangePointsEquiv (baseMap A A') (groupScheme A B) T
        ((x ≫ (Gm.baseChangeIso (baseMap A A')).inv.hom.hom) ≫
          ((GroupScheme.baseChange (baseMap A A')).map (scalar A B)).hom.hom))) i = _
  rw [GroupScheme.baseChangePointsEquiv_comp, scalar_points]
  change decompositionTensorEquiv A A' B (restrictedSections A A' T) I e
    (1 ⊗ₜ (Units.val (Gm.baseChangeUnitsEquiv (baseMap A A') T
      (x ≫ (Gm.baseChangeIso (baseMap A A')).inv.hom.hom)) : restrictedSections A A' T)) i = _
  rw [Gm.baseChangeUnitsEquiv_baseChangeIso_inv, decompositionTensorEquiv_tmul]
  simp [← Algebra.TensorProduct.one_def]

end Scheme

section Lattices

variable (A : CommRingCat.{u}) (K : Type u) [Field K] [Algebra A K]
  (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (I : Type u) [Fintype I] (e : K ⊗[A] B ≃ₐ[K] (I → K))

local notation "T_K" =>
  (Functor.obj (CommGroupScheme.baseChange (baseMap A (CommRingCat.of K))) (commGroupScheme A B))

/-- The norm character has coefficient one in every splitting coordinate. -/
theorem decompositionCharacterEquiv_normHom :
    decompositionCharacterEquiv A K B I e (decompositionNormHom A (CommRingCat.of K) B) =
      fun _ => 1 := by
  classical
  apply (decompositionCharacterEquiv A K B I e).symm.injective
  rw [AddEquiv.symm_apply_apply]
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (Gm.pointsEquiv _ T).injective
  rw [decompositionNormHom_points A (CommRingCat.of K) B I e,
    decompositionCharacterEquiv_symm_points]
  simp

/-- The scalar cocharacter has coefficient one in every splitting coordinate. -/
theorem decompositionCocharacterEquiv_scalarHom :
    decompositionCocharacterEquiv A K B I e (decompositionScalarHom A (CommRingCat.of K) B) =
      fun _ => 1 := by
  apply (decompositionCocharacterEquiv A K B I e).symm.injective
  rw [AddEquiv.symm_apply_apply]
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (decompositionPointsEquiv A (CommRingCat.of K) B I e T).injective
  rw [decompositionScalarHom_points, decompositionCocharacterEquiv_symm_points]
  simp

/-- Pairing with the norm character sums the cocharacter coordinates. -/
theorem decomposition_latticePairing_normHom (ν : cocharacterLattice T_K) :
    latticePairing T_K (decompositionNormHom A (CommRingCat.of K) B) ν =
      ∑ i, decompositionCocharacterEquiv A K B I e ν i := by
  rw [decomposition_latticePairing_eq_sum A K B I e, decompositionCharacterEquiv_normHom]
  simp

/-- Pairing with the scalar cocharacter sums the character coordinates. -/
theorem decomposition_latticePairing_scalarHom (χ : characterLattice T_K) :
    latticePairing T_K χ (decompositionScalarHom A (CommRingCat.of K) B) =
      ∑ i, decompositionCharacterEquiv A K B I e χ i := by
  rw [decomposition_latticePairing_eq_sum A K B I e, decompositionCocharacterEquiv_scalarHom]
  simp

end Lattices

end Langlands.GroupScheme.WeilGm
