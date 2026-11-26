import Langlands.Cohomology.DivisibleSystem.AnalyticEtale

/-!
# Uniform pro-`p` kernel for compactly supported cohomology

Under the finiteness and boundedness used in Harris 1999, §2, one open
normal pro-`p` subgroup acts trivially on all compactly supported
cohomology groups of an `ℓ`-divisible coefficient system.
-/

set_option autoImplicit false

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

section

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The smooth compactly supported cohomology in degree `q` at level `m`
of an analytic étale divisible system, viewed as a representation. -/
noncomputable def etaleCompactCohomologyAtLevel
    (R : Type (max u (v + 1) uL)) [CommRing R]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    {ℓ : ℕ} (T : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ) (m q : ℕ) :
    Rep.{max u (v + 1) uL} R G :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  SmoothRep.toRep.obj ((etaleGSheafCompactCohomology L ρ h R q).obj (T.obj m))

end

/-- Finiteness and vanishing above `D` at level `1` extend to every level.
There is a common open normal pro-`p` subgroup acting trivially on the
cohomology in every degree and at every level. -/
def AnalyticEtaleCompactUniformProPKernelStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R]
    (p ℓ : ℕ) (T : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ) (D : ℕ) : Prop :=
  let Hc := etaleCompactCohomologyAtLevel ρ R L h T
  ℓ.Prime → p ≠ ℓ → IsUnit (p : R) →
    (∃ N : OpenNormalSubgroup G, IsProPSubgroup p N.toSubgroup) →
    (∀ q : ℕ, q ≤ D → Finite (Hc 1 q)) →
    (∀ q : ℕ, D < q → IsZero (Hc 1 q)) →
    (∀ m q : ℕ, Finite (Hc m q)) ∧
    (∀ m q : ℕ, D < q → IsZero (Hc m q)) ∧
    ∃ N : OpenNormalSubgroup G, IsProPSubgroup p N.toSubgroup ∧
      ∀ (m q : ℕ) (g : N.toSubgroup), (Hc m q).ρ g = LinearMap.id

end Langlands.Cohomology.DivisibleSystem.Analytic
