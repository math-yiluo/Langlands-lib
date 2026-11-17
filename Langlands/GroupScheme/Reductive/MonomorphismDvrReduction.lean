import Langlands.GroupScheme.Descent.FiniteCoefficientReductiveExtension
import Langlands.AlgebraicGeometry.FiniteCoefficientMonomorphism
import Langlands.GroupScheme.Reductive.MonomorphismNoetherianReductionProof
import Langlands.GroupScheme.Reductive.MonomorphismValuativeReductionProof

/-! # Actual noetherian models and reduction to discrete valuation rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ReductiveMonomorphismDvrReduction

open Descent.FiniteCoefficient

/-- An actual noetherian reductive monic model of the specified affine-base
homomorphism, over a finite coefficient algebra over the prime subring. -/
structure AffineModel {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} (f : G ⟶ H) where
  model : SimultaneousHomModel ↥(⊥ : Subalgebra ℤ A) A f
  noetherian : IsNoetherianRing model.coefficients
  reductive : IsReductive model.source
  mono : Mono model.hom.hom.hom.left

/-- Choose a noetherian reductive monic coefficient model of the given homomorphism. -/
def affineModel
    {A : Type u} [CommRing A] {G H : GroupScheme (Spec (CommRingCat.of A))}
    (f : G ⟶ H) (hG : IsReductive G) [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    [Mono f.hom.hom.left] : AffineModel f := by
  have : IsNoetherianRing (⊥ : Subalgebra ℤ A) := by
    have := (Subalgebra.fg_iff_finiteType (⊥ : Subalgebra ℤ A)).mp Subalgebra.fg_bot
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  let hex := exists_reductiveMonoModel_of_monomorphism_descent
    (R := ↥(⊥ : Subalgebra ℤ A))
    Langlands.AlgebraicGeometry.FiniteCoefficient.monomorphism f hG ∅
  let D := Classical.choose hex
  have := (Subalgebra.fg_iff_finiteType D.coefficients).mp D.finite
  exact
    { model := D
      noetherian := Algebra.FiniteType.isNoetherianRing (⊥ : Subalgebra ℤ A) D.coefficients
      reductive := (Classical.choose_spec hex).2.1
      mono := (Classical.choose_spec hex).2.2 }

/-- The locally noetherian theorem applies to a chosen actual coefficient model. -/
theorem AffineModel.isClosedImmersion
    {A : Type u} [CommRing A] {G H : GroupScheme (Spec (CommRingCat.of A))}
    {f : G ⟶ H} (D : AffineModel f)
    (hN : ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u}) :
    IsClosedImmersion f.hom.hom.left := by
  let := D.noetherian
  apply ReductiveMonomorphismNoetherianReduction.SimultaneousHomModel.isClosedImmersion_of_model
    D.model
  exact hN _ D.model.source D.model.target D.reductive D.model.targetSeparated
    D.model.targetFinitePresentation D.model.targetQuasiCompact D.model.hom D.mono

/-- The locally noetherian case implies the theorem over every affine base. -/
theorem affineCase_of_locallyNoetherianCase
    (hN : ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u})
    (A : Type u) [CommRing A] (G H : GroupScheme (Spec (CommRingCat.of A)))
    (hG : IsReductive G) [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (f : G ⟶ H) [Mono f.hom.hom.left] : IsClosedImmersion f.hom.hom.left :=
  (affineModel f hG).isClosedImmersion hN

/-- Actual finite coefficient descent reduces arbitrary bases to the locally
noetherian case using the published descent proofs. -/
theorem generalCase_of_locallyNoetherianCase
    (hN : ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u}) :
    ReductiveMonomorphismClosedImmersionStatement.{u} := by
  intro S G H hG hs hp hq f hm
  let := hs
  let := hp
  let := hq
  let := hm
  apply ReductiveMonomorphismNoetherianReduction.isClosedImmersion_of_openCover
    f S.affineOpenCover.openCover
  intro i
  let b := S.affineOpenCover.f i
  have : IsSeparated ((baseChange b).obj H).X.hom := by
    change IsSeparated (pullback.snd H.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation ((baseChange b).obj H).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd H.X.hom b)
    infer_instance
  have : QuasiCompact ((baseChange b).obj H).X.hom := by
    change QuasiCompact (pullback.snd H.X.hom b)
    infer_instance
  have : Mono ((baseChange b).map f).hom.hom.left :=
    (baseChange_map_isPullback b f).flip.mono_snd_of_mono
  exact affineCase_of_locallyNoetherianCase hN
    (S.affineOpenCover.X i) _ _ (hG.baseChange b) ((baseChange b).map f)

/-- The remaining geometric input is the closed-immersion theorem over DVRs. -/
theorem generalCase_of_dvrCase
    (hDvr : ReductiveMonomorphismValuativeReduction.DvrCase.{u}) :
    ReductiveMonomorphismClosedImmersionStatement.{u} :=
  generalCase_of_locallyNoetherianCase
    (ReductiveMonomorphismValuativeReduction.locallyNoetherianCase_of_dvrCase hDvr)

/-- The unchanged arbitrary-base theorem is equivalent to its restriction to DVRs. -/
theorem dvrCase_iff_generalCase :
    ReductiveMonomorphismValuativeReduction.DvrCase.{u} ↔
      ReductiveMonomorphismClosedImmersionStatement.{u} := by
  constructor
  · exact generalCase_of_dvrCase
  · intro h R _ _ _ G H hG hs hp hq f hm
    exact h (Spec (CommRingCat.of R)) G H hG hs hp hq f hm

end Langlands.GroupScheme.ReductiveMonomorphismDvrReduction
