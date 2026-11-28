import Langlands.Sheaf.Equivariant.AnalyticEtaleProperRestriction
import Langlands.Geometry.Analytic.EtaleSiteBaseChange
import Langlands.Cohomology.DerivedPlusExactSource
import Langlands.Cohomology.DerivedPlusNaturality

/-! # Derived proper restriction on analytic étale sites -/

noncomputable section

universe u v uR uL w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation Langlands.Cohomology

section Exactness

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y} (hf : etale f)
  (R : Type uR) [CommRing R]

private abbrev modules (R : Type uR) [CommRing R] := ModuleCat.{uR} R

local notation "M" => modules R
local notation "res" => Functor.sheafPushforwardContinuous (EtaleSite.postcomposeEtale hf) M
  (etaleTopology X) (etaleTopology Y)

instance etaleRestriction_additive : (res).Additive where
  map_add := by
    intro F G a b
    apply Sheaf.hom_ext
    rfl

variable [HasSheafify (etaleTopology X) (ModuleCat.{uR} R)]
  [HasSheafify (etaleTopology Y) (ModuleCat.{uR} R)]

/-- Étale restriction preserves finite limits because it is precomposition on presheaves. -/
instance etaleRestriction_preservesFiniteLimits : PreservesFiniteLimits res := by
  let G := sheafToPresheaf (etaleTopology X) M
  have : PreservesFiniteLimits (res ⋙ G) := by
    change PreservesFiniteLimits (sheafToPresheaf (etaleTopology Y) M ⋙
      (Functor.whiskeringLeft (EtaleSite X)ᵒᵖ (EtaleSite Y)ᵒᵖ M).obj (EtaleSite.postcomposeEtale hf).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves res G

/-- Étale restriction preserves finite colimits by its right adjoint, the actual direct image. -/
instance etaleRestriction_preservesFiniteColimits : PreservesFiniteColimits res := by
  let : (res).IsLeftAdjoint := (EtaleSite.postcomposeEtaleAdjunction f M hf).isLeftAdjoint
  infer_instance

end Exactness

section Compact

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y} (hf : etale f)
  (R : Type (max u (v + 1) uL)) [CommRing R]
  (Lₓ Lᵧ : Type uL) [NormedField Lₓ] [NormedAlgebra K Lₓ]
  [NormedField Lᵧ] [NormedAlgebra K Lᵧ]
  [T2Space (localizedSpaceFunctor.obj X)] [T2Space (localizedSpaceFunctor.obj Y)]
  (hX : ∀ x : (localizedFieldPointFunctor Lₓ).obj X, EtaleSite.PointAxioms Lₓ x)
  (hY : ∀ y : (localizedFieldPointFunctor Lᵧ).obj Y, EtaleSite.PointAxioms Lᵧ y)
  (surjX : Function.Surjective (pointProjection Lₓ X))
  (surjY : Function.Surjective (pointProjection Lᵧ Y))
  (hp : IsProperMap (localizedSpaceFunctor.map f))
  [HasDerivedCategory.{w} (ModuleCat.{max u (v + 1) uL} R)]

/-- Proper étale restriction on the actual bounded-below compactly supported complexes. -/
def etaleCompactComplexRestriction : etaleCompactComplex Lᵧ hY R ⟶
    etaleRestriction.{u, v, uL} hf R ⋙ etaleCompactComplex Lₓ hX R := by
  letI := etale_hasSheafify.{u, v, uL} X R
  letI := etale_hasSheafify.{u, v, uL} Y R
  letI := etale_enoughInjectives.{u, v, uL} X R
  letI := etale_enoughInjectives.{u, v, uL} Y R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology Y) (ModuleCat.{max u (v + 1) uL} R))
  exact DerivedPlusExactSource.derivedComplexComparison (etaleRestriction.{u, v, uL} hf R)
    (etaleCompactSections Lᵧ hY R) (etaleCompactSections Lₓ hX R)
    (etaleCompactSectionsRestriction.{u, v, uL} hf R Lₓ Lᵧ hX hY surjX surjY hp)

/-- The existing homology comparison of compact étale complexes is natural in the sheaf. -/
def etaleCompactComplexHomologyNatIso (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x) (d : ℕ) :
    etaleCompactComplex L h R ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) d ≅
      etaleCompactCohomology L h R d := by
  letI := etale_hasSheafify.{u, v, uL} X R
  letI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exact DerivedPlus.homologyNatIso (etaleCompactSections L h R) d

/-- Restriction on ordinary compactly supported cohomology, induced by the complex map. -/
def etaleCompactCohomologyRestriction (d : ℕ) : etaleCompactCohomology Lᵧ hY R d ⟶
    etaleRestriction.{u, v, uL} hf R ⋙ etaleCompactCohomology Lₓ hX R d :=
  (etaleCompactComplexHomologyNatIso R Lᵧ Y hY d).inv ≫
    Functor.whiskerRight (etaleCompactComplexRestriction hf R Lₓ Lᵧ hX hY surjX surjY hp) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleCompactComplexHomologyNatIso R Lₓ X hX d).hom

end Compact

end Langlands.Sheaf.Equivariant.Analytic
