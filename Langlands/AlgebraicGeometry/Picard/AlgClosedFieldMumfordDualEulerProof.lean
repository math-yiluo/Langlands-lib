import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerFromPrerequisites
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareDirectImageProof
import Langlands.AlgebraicGeometry.Picard.LineBundleHigherProjectionFormulaProof
import Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveProof
import Langlands.AlgebraicGeometry.Picard.DualSchemeSubalgebraFactorization
import Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeProof
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Proof of the dual-side Euler characteristic of a finite flat Mumford map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Over a field, a finite flat surjective map from an abelian scheme to its chosen dual has
the same degree at every point of the dual. -/
theorem finrank_eq_of_surjective_dualScheme
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))) (hA : HasDualScheme A)
    (f : A.X ⟶ dualScheme A hA) [IsFinite f.left] [Flat f.left]
    (hsurj : Function.Surjective f.left) (y y' : (dualScheme A hA).left) :
    f.left.finrank y = f.left.finrank y' := by
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := A.X.hom)
  have : ConnectedSpace (dualScheme A hA).left :=
    hsurj.connectedSpace f.left.continuous
  have : LocallyOfFiniteType (dualScheme A hA).hom := dualScheme_locallyOfFiniteType A hA
  have : IsLocallyNoetherian (dualScheme A hA).left :=
    LocallyOfFiniteType.isLocallyNoetherian (dualScheme A hA).hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  exact f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace y y'

/-- The dual-side Euler characteristic of a finite flat Mumford map over an algebraically
closed field: `χ(A ×_K A, m^* N ⊗ snd^* M) = (-1)^g · rank_y(f_* 𝒪_A)` at every point `y` of
the dual. -/
theorem algClosedFieldMumfordDualEuler : AlgClosedFieldMumfordDualEulerStatement.{u} := by
  intro preservation square K _ _ A hA L B evaluationB M evaluation f hf hfin hflat g hg hQ y
  have hsurj : Function.Surjective f.left := by
    subst hf
    exact fieldFiniteMumfordMapSurjective preservation square K A hA _ M evaluation hfin
  obtain ⟨hzero, ⟨iso⟩⟩ := mumfordDual_higherDirectImage preservation K A hA L B evaluationB
    M evaluation square algClosedFieldPoincareDirectImage flatHigherDirectImageBaseChange
    lineBundleHigherProjectionFormula f hf hflat g hg
  let N := (RigidifiedLineBundle.forget (unitSection A)).obj
    (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A) L B
      evaluationB)
  have he : (dualOrigin A hA).left ≫ (dualScheme A hA).hom = 𝟙 _ := Over.w (dualOrigin A hA)
  have hfD : f.left ≫ (dualScheme A hA).hom = A.X.hom := Over.w f
  have hsupp := (hasFiniteClosedSupport_iff_of_iso iso).2
    (FiniteFlatPointFibre.hasFiniteClosedSupport_tensor_pullback_pushforward
      flatHigherDirectImageBaseChange (dualScheme A hA).hom f.left (dualOrigin A hA).left he N)
  refine (eulerCharacteristic_comp_eq_of_concentrated (pullback.fst A.X.hom A.X.hom) A.X.hom
    _ g hzero hsupp hQ).trans ?_
  congr 2
  refine ((relativeGlobalSections A.X.hom).mapIso iso).toLinearEquiv.finrank_eq.trans
    ((FiniteFlatPointFibre.finrank_relativeGlobalSections_tensor_pullback_pushforward
      flatHigherDirectImageBaseChange A.X.hom (dualScheme A hA).hom f.left hfD
      (dualOrigin A hA).left he N ((dualScheme A hA).hom y)).trans ?_)
  exact finrank_eq_of_surjective_dualScheme K A hA f hsurj _ y

end Langlands.AbelianScheme
