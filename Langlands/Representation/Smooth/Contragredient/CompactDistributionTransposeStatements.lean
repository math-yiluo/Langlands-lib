import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.HarmonicAnalysis.Distribution.CompactSubgroup
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Transposes of compactly supported distributions on the contragredient (Renard III.1.6, Lemma)

For a smooth representation `(π, V)` of a t.d. group, `T ∈ ℰ′(G)`, `λ ∈ Ṽ` and `v ∈ V`,
`(π̃(Ť) λ)(v) = λ(π(T) v)`. For a compact subgroup `K`, `π(e_K)` is self-transposed and
fixes `K`-invariant functionals, and restriction identifies `(V*)^K` with `(V^K)*`.
-/

namespace Langlands

open HarmonicAnalysis

universe u v

/-- Renard III.1.6, Lemma, first assertion: let `T ↦ π(T)` and `T ↦ π̃(T)` be actions of the
compactly supported distributions on a smooth representation `(π, V)` and on its smooth
contragredient, each characterized by the III.1.3 pairing `m(π(T) v) = ⟨T, g ↦ m(π(g) v)⟩`
for all linear forms `m`. For `T ∈ ℰ′(G)` with inversion `Ť`, `ℓ ∈ Ṽ` and `v ∈ V`,
`(π̃(Ť) ℓ)(v) = ℓ(π(T) v)`. -/
def CompactDistributionContragredientTransposeStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
    ∀ (act : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ V)
      (act' : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ (SmoothDual ρ)),
      (∀ (T : Distribution.compactlySupported (X := G)) (x : V) (m : Module.Dual ℂ V)
          (φ : LocallyConstant G ℂ), (∀ g : G, φ g = m (ρ g x)) →
          m (act T x) = Distribution.compactSupportFunctional T φ) →
      (∀ (T : Distribution.compactlySupported (X := G)) (ℓ : SmoothDual ρ)
          (m : Module.Dual ℂ (SmoothDual ρ)) (φ : LocallyConstant G ℂ),
          (∀ g : G, φ g = m (smoothContragredient ρ g ℓ)) →
          m (act' T ℓ) = Distribution.compactSupportFunctional T φ) →
      ∀ (T Tinv : Distribution.compactlySupported (X := G)),
        (Tinv : Distribution G) = GroupAction.inversionDistributions (T : Distribution G) →
        ∀ (ℓ : SmoothDual ρ) (x : V),
          smoothDualPairing ρ (act' Tinv ℓ) x = smoothDualPairing ρ ℓ (act T x)

/-- Renard III.1.6, Lemma, second and third assertions: for a compact subgroup `K` (not
necessarily open) with normalized Haar distribution `e_K`, and actions characterized as in
`CompactDistributionContragredientTransposeStatement`,
`(π̃(e_K) ℓ)(v) = ℓ(π(e_K) v)` for `ℓ ∈ Ṽ`, and `m(π(e_K) v) = m(v)` for every `K`-invariant
linear form `m ∈ (V*)^K`. -/
def CompactSubgroupHaarTransposeStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
    ∀ (act : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ V)
      (act' : Distribution.compactlySupported (X := G) →ₗ[ℂ] Module.End ℂ (SmoothDual ρ)),
      (∀ (T : Distribution.compactlySupported (X := G)) (x : V) (m : Module.Dual ℂ V)
          (φ : LocallyConstant G ℂ), (∀ g : G, φ g = m (ρ g x)) →
          m (act T x) = Distribution.compactSupportFunctional T φ) →
      (∀ (T : Distribution.compactlySupported (X := G)) (ℓ : SmoothDual ρ)
          (m : Module.Dual ℂ (SmoothDual ρ)) (φ : LocallyConstant G ℂ),
          (∀ g : G, φ g = m (smoothContragredient ρ g ℓ)) →
          m (act' T ℓ) = Distribution.compactSupportFunctional T φ) →
      ∀ (K : Subgroup G) (hK : IsCompact (K : Set G)),
        (∀ (ℓ : SmoothDual ρ) (x : V),
          smoothDualPairing ρ (act' (Distribution.compactSubgroupHaar K hK) ℓ) x =
            smoothDualPairing ρ ℓ (act (Distribution.compactSubgroupHaar K hK) x)) ∧
        ∀ m : Module.Dual ℂ V, (∀ k ∈ K, ∀ x : V, m (ρ k x) = m x) →
          ∀ x : V, m (act (Distribution.compactSubgroupHaar K hK) x) = m x

/-- Renard III.1.6, Lemma, fourth assertion: for a smooth representation `(π, V)` of a t.d.
group and a compact subgroup `K` (not necessarily open), restriction of linear forms to the
fixed vectors is a bijection `(V*)^K → (V^K)*`. -/
def CompactFixedDualRestrictionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
    ∀ K : Subgroup G, IsCompact (K : Set G) →
      Function.Bijective (fun m : fixedVectors ρ.dual K =>
        (m.val : Module.Dual ℂ V).comp (fixedVectors ρ K).subtype)

/-- Renard III.1.6, Lemma: the three statements above. -/
def ContragredientDistributionLemmaStatement : Prop :=
  CompactDistributionContragredientTransposeStatement.{u, v} ∧
  CompactSubgroupHaarTransposeStatement.{u, v} ∧
  CompactFixedDualRestrictionStatement.{u, v}

end Langlands
