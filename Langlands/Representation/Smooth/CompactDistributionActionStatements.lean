import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.Representation.Smooth.Definitions

/-!
# Compactly supported distributions act on smooth representations (Renard III.1.3)

A smooth representation `(π, V)` of a t.d. group is a module over the convolution algebra
`ℰ′(G)` of compactly supported distributions, by `π(T) v = ∫ π(g) v dT(g)`, with
`π(T₁ ∗ T₂) = π(T₁) π(T₂)` and `π(δ_g) = π(g)`. For the left regular representation on test
functions, `l(T) f = T ∗ f`.
-/

namespace Langlands

open HarmonicAnalysis

universe u v

/-- Renard III.1.3: for a smooth representation `ρ` of a t.d. group `G`, there is a linear
map `T ↦ ρ(T)` from compactly supported distributions to endomorphisms of `V` with
`ℓ(ρ(T) v) = ⟨T, g ↦ ℓ(ρ(g) v)⟩` for every linear form `ℓ` (the vector-valued pairing
`ρ(T) v = ∫ ρ(g) v dT(g)`), and it satisfies `ρ(T₁ ∗ T₂) = ρ(T₁) ρ(T₂)` and `ρ(δ_g) = ρ(g)`. -/
def CompactDistributionActionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
    ∃ act : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ V,
      (∀ (T : Distribution.compactlySupported (X := G)) (v : V) (ℓ : Module.Dual ℂ V)
          (φ : LocallyConstant G ℂ), (∀ g : G, φ g = ℓ (ρ g v)) →
          ℓ (act T v) = Distribution.compactSupportFunctional T φ) ∧
      (∀ T S : Distribution.compactlySupported (X := G),
          act (Distribution.convolution T S) = act T * act S) ∧
      ∀ g : G, act (Distribution.compactDirac g) = ρ g

/-- Renard III.1.3, Example: for the left regular representation `l` of `G` on test
functions, the action of a compactly supported distribution characterized as above is
convolution: `l(T) f = T ∗ f`, `(T ∗ f)(x) = ⟨T, y ↦ f(y⁻¹ x)⟩`. -/
def LeftRegularCompactDistributionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (act : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ (SchwartzBruhat G)),
    (∀ (T : Distribution.compactlySupported (X := G)) (f : SchwartzBruhat G)
        (ℓ : Module.Dual ℂ (SchwartzBruhat G)) (φ : LocallyConstant G ℂ),
        (∀ g : G, φ g = ℓ (GroupAction.leftTests g f)) →
        ℓ (act T f) = Distribution.compactSupportFunctional T φ) →
    ∀ (T : Distribution.compactlySupported (X := G)) (f : SchwartzBruhat G) (x : G),
      act T f x = Distribution.leftConvolveTest (T : Distribution G) f x

end Langlands
