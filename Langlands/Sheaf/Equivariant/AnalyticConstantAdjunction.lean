import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedConstantAdjunction

/-!
# Constant étale and quasi-étale `G`-sheaves and injectivity of `Γ_{X{G}}`

Let `G` act on an analytic space `X`. For a smooth representation `M` of `G`, this module
defines the constant étale `G`-sheaf and the constant quasi-étale `G`-sheaf of `M`: the
constructions of `TwistedConstantAdjunction` for the distinguished and the compact lift
systems, whose admissible actions are lifts. The constant `G`-sheaf functors are left adjoint
to Berkovich's `Γ_{X{G}}` and preserve monomorphisms, so `Γ_{X{G}}` sends injective étale
(resp. quasi-étale) `G`-sheaves to injective smooth representations of `G`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]

section Etale

variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The constant étale `G`-sheaf of a smooth representation of `G`: the sheafification of the
presheaf that is `M` on every object of the twisted étale site, where a twisted morphism with
twist `g` acts by `g⁻¹`. -/
def etaleConstantGSheaf :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G ⥤
      EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  smoothSheafConstantTwisted (etaleTopology X) R (distinguishedLiftSystem ρ)
    (isLiftSystem_liftSystem _)

/-- The constant étale `G`-sheaf functor is left adjoint to `Γ_{X{G}}`. -/
def etaleConstantGSheafAdjunction :
    etaleConstantGSheaf.{u, v, uL} ρ R ⊣ etaleGSheafSections.{u, v, uL} ρ R :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  smoothSheafConstantTwistedAdjunction (etaleTopology X) R (distinguishedLiftSystem ρ)
    (isLiftSystem_liftSystem _)

omit [IsTopologicalGroup G] in
/-- The constant étale `G`-sheaf functor preserves monomorphisms. -/
theorem etaleConstantGSheaf_preservesMonomorphisms :
    (etaleConstantGSheaf.{u, v, uL} ρ R).PreservesMonomorphisms :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  smoothSheafConstantTwisted_preservesMonomorphisms (etaleTopology X) R
    (distinguishedLiftSystem ρ) (isLiftSystem_liftSystem _)

/-- `Γ_{X{G}}` sends injective étale `G`-sheaves to injective smooth representations of
`G`. -/
theorem etaleGSheafSections_preservesInjectiveObjects :
    (etaleGSheafSections.{u, v, uL} ρ R).PreservesInjectiveObjects :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactGlobalSections_smoothSheafInclusion_preservesInjectiveObjects (etaleTopology X) R
    (distinguishedLiftSystem ρ) (isLiftSystem_liftSystem _)

end Etale

section QuasiEtale

variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The constant quasi-étale `G`-sheaf of a smooth representation of `G`: the sheafification
of the presheaf that is `M` on every object of the twisted quasi-étale site, where a twisted
morphism with twist `g` acts by `g⁻¹`. -/
def quasiEtaleConstantGSheaf :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G ⥤
      QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteConstantTwisted (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (isLiftSystem_liftSystem _)

/-- The constant quasi-étale `G`-sheaf functor is left adjoint to `Γ_{X{G}}`. -/
def quasiEtaleConstantGSheafAdjunction :
    quasiEtaleConstantGSheaf.{u, v, uL} ρ R ⊣ quasiEtaleGSheafSections.{u, v, uL} ρ R :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteConstantTwistedAdjunction (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (isLiftSystem_liftSystem _)

omit [IsTopologicalGroup G] in
/-- The constant quasi-étale `G`-sheaf functor preserves monomorphisms. -/
theorem quasiEtaleConstantGSheaf_preservesMonomorphisms :
    (quasiEtaleConstantGSheaf.{u, v, uL} ρ R).PreservesMonomorphisms :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteConstantTwisted_preservesMonomorphisms (quasiEtaleTopology X) R
    (compactLiftSystem ρ) (isLiftSystem_liftSystem _)

/-- `Γ_{X{G}}` sends injective quasi-étale `G`-sheaves to injective smooth representations of
`G`. -/
theorem quasiEtaleGSheafSections_preservesInjectiveObjects :
    (quasiEtaleGSheafSections.{u, v, uL} ρ R).PreservesInjectiveObjects :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteGlobalSections_preservesInjectiveObjects (quasiEtaleTopology X) R
    (compactLiftSystem ρ) (isLiftSystem_liftSystem _)

end QuasiEtale

end Langlands.Sheaf.Equivariant.Analytic
