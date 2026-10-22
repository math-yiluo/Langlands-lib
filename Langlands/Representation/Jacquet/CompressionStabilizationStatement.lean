import Langlands.Representation.Jacquet.CanonicalLiftDefinitions

/-!
# Finite-dimensional stabilization of compact compressed actions

Statements only. On a finite-dimensional space of `K`-fixed vectors, the
published compressed action of `g` has eventually constant power ranges and
power kernels, its all-power kernel supremum and stable image are complementary,
and its published restriction to the stable image is bijective. No Jacquet
quotient, independence of `g`, multiplicativity or pairing is asserted.
-/

namespace Langlands.Jacquet

universe uG uV

section Conclusions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- From some exponent `r` on, every power range of the compressed action is the
published stable image and every power kernel is the published kernel supremum. -/
def CompactCompressionEventuallyStable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) : Prop :=
  ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
    stableImage ρ hρ K hK g = LinearMap.range (compressedAction ρ hρ K hK g ^ s) ∧
      powerKernelSup ρ hρ K hK g = LinearMap.ker (compressedAction ρ hρ K hK g ^ s)

/-- The published kernel supremum and stable image split the whole module of
`K`-fixed vectors. -/
def CompactCompressionSplits (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) : Prop :=
  IsCompl (powerKernelSup ρ hρ K hK g) (stableImage ρ hρ K hK g)

/-- The published restriction of the compressed action to its stable image is
bijective. -/
def CompactCompressionStableActionBijective (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    Prop :=
  Function.Bijective (stableImageAction ρ hρ K hK g)

/-- The three stabilization conclusions for fixed data. -/
def CompactCompressionStabilizes (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) : Prop :=
  CompactCompressionEventuallyStable ρ hρ K hK g ∧
    CompactCompressionSplits ρ hρ K hK g ∧
    CompactCompressionStableActionBijective ρ hρ K hK g

end Conclusions

/-- Fitting stabilization of the compressed action of every `g` on a
finite-dimensional space of fixed vectors of a compact open subgroup, for every
smooth complex representation of every topological group. -/
def CompactCompressionStabilizationStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G),
    FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) →
      CompactCompressionStabilizes ρ hρ K hK g

end Langlands.Jacquet
