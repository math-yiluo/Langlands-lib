import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleDerived
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleSupport
import Langlands.AlgebraicGeometry.Modules.PushforwardComparison

/-! # Supported derived comparison conditional on higher direct-image vanishing -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport Langlands.Cohomology.AcyclicResolution

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

theorem etaleUnderlyingSheaf_isRightAdjoint :
    (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).IsRightAdjoint :=
  (etaleUnderlyingAdjunction.{u, v, uL} X R).isRightAdjoint

theorem etaleUnderlyingSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)) := by
  have := etaleUnderlyingSheaf_isRightAdjoint.{u, v, uL} X R
  infer_instance

section Additive

variable [HasSheafify (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]
  [HasSheafify (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
    (ModuleCat.{max u (v + 1) uL} R)]

theorem etaleUnderlyingSheaf_additive :
    (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).Additive := by
  have := etaleUnderlyingSheaf_preservesFiniteLimits.{u, v, uL} X R
  exact Functor.additive_of_preserves_binary_products _

omit [HasSheafify (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)] in
theorem underlyingTopologyCompactSections_additive :
    (underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R)).Additive := by
  exact sheafCompactSections_additive
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
    (underlyingTopologyPoint.{u, v, uL} X) R ⊤

end Additive

theorem underlyingTopologyCompactSections_preservesFiniteLimits :
    PreservesFiniteLimits
      (underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R)) := by
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  exact sheafCompactSections_preservesFiniteLimits
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
    (underlyingTopologyPoint.{u, v, uL} X) R ⊤

/-- The actual ordinary-open module sheaf category has enough injectives. -/
theorem underlyingTopology_enoughInjectives :
    EnoughInjectives
      (TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X)) := by
  change EnoughInjectives
    (Sheaf (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
      (ModuleCat.{max u (v + 1) uL} R))
  have : Small.{max u (v + 1) uL} (Opens (localizedSpaceFunctor.obj X)) :=
    small_lift.{v, max u (v + 1) uL, v} _
  have : EssentiallySmall.{max u (v + 1) uL} (Opens (localizedSpaceFunctor.obj X)) :=
    essentiallySmall_of_small_of_locallySmall _
  have : ∀ Y : (Opens (localizedSpaceFunctor.obj X))ᵒᵖ,
      HasLimitsOfShape
        (StructuredArrow Y
          (equivSmallModel.{max u (v + 1) uL} (Opens (localizedSpaceFunctor.obj X))).inverse.op)
        (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  have := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u (v + 1) uL}
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (ModuleCat.{max u (v + 1) uL} R)
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  exact IsGrothendieckAbelian.enoughInjectives

/-- Right-derived ordinary direct image of the actual analytic étale sheaf. -/
def etaleUnderlyingHigherDirectImage (q : ℕ) :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := underlyingTopology_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etaleUnderlyingSheaf_additive.{u, v, uL} X R
  (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).rightDerived q

/-- The existing right-derived point-support functor for the ordinary-open site. -/
def underlyingTopologyCompactCohomology (q : ℕ) :
    TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  haveI := underlyingTopology_hasSheafify.{u, v, uL} X R
  haveI := underlyingTopology_enoughInjectives.{u, v, uL} X R
  haveI := underlyingTopologyCompactSections_additive.{u, v, uL} X R
  (underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R)).rightDerived q

variable {X}
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable [T2Space (localizedSpaceFunctor.obj X)]

/-- The actual supported derived comparison for a sheaf whose higher ordinary
direct images vanish. -/
def etaleUnderlyingCompactCohomologyComparison
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (hF : ∀ q : ℕ, IsZero
      ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj F)) (q : ℕ) :
    (etaleCompactCohomology L h R q).obj F ⟶
      (underlyingTopologyCompactCohomology.{u, v, uL} X R q).obj
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F) := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := underlyingTopology_enoughInjectives.{u, v, uL} X R
  have := etaleUnderlyingSheaf_additive.{u, v, uL} X R
  have := etaleUnderlyingSheaf_preservesFiniteLimits.{u, v, uL} X R
  have := underlyingTopologyCompactSections_additive.{u, v, uL} X R
  exact compComparison
    (underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R))
    (etaleUnderlyingCompactIso L h hX (R := R)).symm F hF q

/-- The supported comparison is invertible because ordinary direct image
preserves injectives, provided the displayed higher-direct-image condition holds. -/
theorem isIso_etaleUnderlyingCompactCohomologyComparison
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (hF : ∀ q : ℕ, IsZero
      ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj F)) (q : ℕ) :
    IsIso (etaleUnderlyingCompactCohomologyComparison R L h hX F hF q) := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := underlyingTopology_enoughInjectives.{u, v, uL} X R
  have := etaleUnderlyingSheaf_additive.{u, v, uL} X R
  have := etaleUnderlyingSheaf_preservesFiniteLimits.{u, v, uL} X R
  have := underlyingTopologyCompactSections_additive.{u, v, uL} X R
  have := underlyingTopologyCompactSections_preservesFiniteLimits.{u, v, uL} X R
  have := etaleUnderlyingSheaf_preservesInjectiveObjects.{u, v, uL} X R
  change IsIso (compComparison
    (underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R))
    (etaleUnderlyingCompactIso L h hX (R := R)).symm F hF q)
  apply isIso_compComparison
  intro I hI n
  have := hI
  exact (underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R)).isZero_rightDerived_obj_injective_succ n _

/-- A supported derived identification on each sheaf satisfying the
explicit higher-direct-image vanishing condition. -/
def etaleUnderlyingCompactCohomologyIso
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (hF : ∀ q : ℕ, IsZero
      ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj F)) (q : ℕ) :
    (etaleCompactCohomology L h R q).obj F ≅
      (underlyingTopologyCompactCohomology.{u, v, uL} X R q).obj
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F) :=
  haveI := isIso_etaleUnderlyingCompactCohomologyComparison R L h hX F hF q
  asIso (etaleUnderlyingCompactCohomologyComparison R L h hX F hF q)

/-- Higher-direct-image vanishing and ordinary compact acyclicity imply the
required vanishing for the existing analytic étale compact cohomology. -/
theorem isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (hF : ∀ q : ℕ, IsZero
      ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj F)) (q : ℕ)
    (hzero : IsZero ((underlyingTopologyCompactCohomology.{u, v, uL} X R (q + 1)).obj
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj F))) :
    IsZero ((etaleCompactCohomology L h R (q + 1)).obj F) :=
  IsZero.of_iso hzero (etaleUnderlyingCompactCohomologyIso R L h hX F hF (q + 1))

end Langlands.Sheaf.Equivariant.Analytic
