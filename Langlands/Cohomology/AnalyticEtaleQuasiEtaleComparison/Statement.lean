import Langlands.Sheaf.Equivariant.AnalyticEtaleToCompactProbe.Statement
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleToposComparison.Statement
import Langlands.Sheaf.Equivariant.AnalyticCompactProbeGlobalCohomology

/-! # Berkovich's cohomological change of site for equivariant sheaves -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf (HasImagePullbacks)
open Langlands.Sheaf.Equivariant.Analytic

set_option autoImplicit false

universe u v z uR w uC vC

namespace Langlands.Cohomology.AnalyticEtaleQuasiEtaleComparison

private abbrev Coefficients (R : Type w) [CommRing R] := ModuleCat.{w} R

private def siteCohomology {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{w} C] [LocallySmall.{w} C]
    (J : GrothendieckTopology C) (R : Type w) [CommRing R] (q : ℕ) :
    Sheaf J (Coefficients R) ⥤ Coefficients R :=
  haveI : HasLimitsOfShape Cᵒᵖ (Coefficients R) :=
    hasLimitsOfShape_of_essentiallySmall.{w} _ _
  haveI := hasSheafifyEssentiallySmallSite J (Coefficients R)
  haveI : ∀ Y : Cᵒᵖ, HasLimitsOfShape
    (StructuredArrow Y (equivSmallModel.{w} C).inverse.op) (Coefficients R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{w} _ _
  haveI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{w} J (Coefficients R)
  haveI : EnoughInjectives (Sheaf J (Coefficients R)) := IsGrothendieckAbelian.enoughInjectives
  haveI : (CategoryTheory.Sheaf.Γ J (Coefficients R)).Additive :=
    (constantSheafΓAdj J (Coefficients R)).right_adjoint_additive
  (CategoryTheory.Sheaf.Γ J (Coefficients R)).rightDerived q

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : GSpace.{u, v, v} K G) (R : Type (max u (v + 1) z uR)) [CommRing R]

/-- Right derived global sections on the equivariant étale site. -/
def equivariantEtaleCohomology (q : ℕ) :
    Sheaf (equivariantEtaleTopology X) (Coefficients R) ⥤ Coefficients R :=
  haveI : Small.{max u (v + 1) z uR} (EquivariantEtaleSite X) :=
    small_lift.{max u (v + 1) z, uR, max u (v + 1) z} _
  haveI : LocallySmall.{max u (v + 1) z uR} (EquivariantEtaleSite X) :=
    ⟨fun V W => small_lift.{max u (v + 1), max z uR, max u (v + 1)} (V ⟶ W)⟩
  siteCohomology (equivariantEtaleTopology X) R q

/-- Right derived global sections on the equivariant compact-probe site. -/
def equivariantCompactProbeCohomology (q : ℕ) :
    Sheaf (equivariantCompactProbeQuasiEtaleTopology X) (Coefficients R) ⥤ Coefficients R :=
  haveI : Small.{max u (v + 1) z uR} (EquivariantQuasiEtaleSite X) :=
    small_lift.{max u (v + 1) z, uR, max u (v + 1) z} _
  haveI : LocallySmall.{max u (v + 1) z uR} (EquivariantQuasiEtaleSite X) :=
    ⟨fun V W => small_lift.{max u (v + 1), max z uR, max u (v + 1)} (V ⟶ W)⟩
  siteCohomology (equivariantCompactProbeQuasiEtaleTopology X) R q

/-- Theorem 1.6.1(iii), first comparison, expressed by a natural
isomorphism between the actual derived functors. -/
def EquivariantEtaleQuasiEtaleCohomologyStatement : Prop :=
  OpenQuotientsSmall.{v, z} (G := G) →
    ∀ q : ℕ, Nonempty (equivariantEtaleCohomology.{u, v, z, uR} X R q ≅
      equivariantEtaleToCompactProbeInverseImage.{u, v, z, uR} X R ⋙
        equivariantCompactProbeCohomology.{u, v, z, uR} X R q)

variable (hEt : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X))
variable (hE : EtaleInverseImageSmooth.{u, v, uR, z} X R hEt)
variable (hQ : CompactProbeQuasiEtaleInverseImageDiscrete.{u, v, uR, z} X R)
variable [(distinguishedLiftSystem X.obj.ρAut).HasAdmissibleRefinements
  (twistedEtaleTopology X.obj.ρAut)]

/-- Theorem 1.6.1(iii), second comparison, for cohomology in smooth
representations using the actual smooth inverse images. -/
def SmoothEtaleQuasiEtaleCohomologyStatement : Prop :=
  OpenQuotientsSmall.{v, z} (G := G) →
    letI : Small.{max u (v + 1) z uR} G := small_lift.{z, max u (v + 1) uR, z} _
    letI := compactProbe_hasFiniteEquivariantRefinements X.obj.ρAut X.property.1 X.property.2
    ∀ q : ℕ, Nonempty
      (etaleSmoothInverseImage.{u, v, uR, z} X R hEt hE ⋙
          etaleGSheafCohomology.{u, v, max z uR} X.obj.ρAut R q ≅
        equivariantEtaleToCompactProbeInverseImage.{u, v, z, uR} X R ⋙
          compactProbeQuasiEtaleDiscreteInverseImage.{u, v, uR, z} X R hQ ⋙
            compactProbeQuasiEtaleGSheafCohomology.{u, v, max z uR} X.obj.ρAut R q)

end Langlands.Cohomology.AnalyticEtaleQuasiEtaleComparison
