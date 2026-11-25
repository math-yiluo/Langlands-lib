# The positive-cocharacter criterion for unipotent root subsets

`Langlands.GroupScheme.unipotentRootSubsetCocharacter` proves exactly the
published proposition
`Langlands.GroupScheme.UnipotentRootSubsetCocharacterStatement.{u}` from
[ClosedRootSubsetStatements](ClosedRootSubsetStatements.md).

For any field `k : Type u`, connected reductive group scheme `G`, maximal split
torus `i : T.toGrp ⟶ G`, and generic integral cocharacter `ν`, let `R` be either
the possibly nonreduced set `relativeRoots i` or the reduced set
`RelativeRoot.indivisibleRoots i`. For every set `X` of characters, the theorem
states that

```text
IsUnipotentRootSubset i ν R X
  ↔ IsClosedRootSubset R X
      ∧ ∃ ζ : cocharacterLattice T, ∀ γ ∈ X, 0 < latticePairing T γ ζ.
```

Here unipotence means closedness in `R` together with containment in a Weyl
translate of `positiveRootSubset R ν`. The witnessing `ζ` need not be generic.
There are no extra hypotheses on the field or the root system.

## Implemented proof

Two elementary lemmas handle the ambient sets.

- `IsRelativeRootAmbient.subset_relativeRoots` observes that either permitted
  ambient set consists of actual relative roots.
- `IsRelativeRootAmbient.mapsTo_relativeWeylCharacterAction` proves that each
  integral Weyl character action preserves either ambient set. Preservation of
  actual roots comes from `relativeWeylRootPermutation`. For an indivisible root
  `α`, a proposed equality `m • β = w α`, with `β` a root and `m > 1`, gives
  `m • (w⁻¹ β) = α` after applying the inverse integral linear action. The inverse
  action preserves roots, so this contradicts indivisibility.

For the forward implication, write each `γ ∈ X` as `w α` with
`α ∈ positiveRootSubset R ν`. Take
`ζ = relativeWeylCocharacterAction i w ν`. The integral pairing identity
`latticePairing_relativeWeyl` gives
`⟨w α, w ν⟩ = ⟨α, ν⟩ > 0`.

For the reverse implication, suppose `X` is closed and `ζ` pairs positively
with every element of `X`. The unconditional published theorem
`relativeRootSystem` supplies `HasRelativeRootSystem i`; splitness comes from
maximal splitness. Apply
`HasRelativeRootSystem.exists_normalizerPoint_dominant` to obtain a normalizing
rational point `n` such that `η = cocharacterAut (normalizingAut i n) ζ` pairs
nonnegatively with every positive relative root of `ν`. Let `w` be its class
in the actual relative Weyl quotient.

Given `γ ∈ X`, put `β = w γ`. Ambient preservation gives `β ∈ R`, and pairing
invariance gives `⟨β, η⟩ = ⟨γ, ζ⟩ > 0`. Genericity of `ν` makes `⟨β, ν⟩`
nonzero. If it were negative, root negation
(`HasRelativeRootSystem.neg_mem_relativeRoots`) would put `−β` among the
positive relative roots of `ν`. Dominance would then imply
`0 ≤ ⟨−β, η⟩ = −⟨β, η⟩`, contradicting strict positivity. Thus `β` is positive
for `ν`, and `γ = w⁻¹ β` lies in the required translate. The original closedness
of `X` completes the definition of unipotence.

This argument uses the closed dominant chamber directly. It requires neither a
generic perturbation of `ζ` nor a dynamic-parabolic root-sign theorem.

## Provenance and scope

This is a proof of the derived cocharacter reformulation already stated in the
Library, not a new translation of a source assertion. Its source comparison is
documented in [ClosedRootSubsetStatements](ClosedRootSubsetStatements.md):

- David Renard, *Représentations des groupes réductifs p-adiques*, French version
  dated 9 July 2026, V.4.2, printed p.118 / PDF p.124; registered source
  `renard-2026-representations-groupes-reductifs-padiques`. Renard defines
  unipotence by containment in a Weyl translate of the fixed positive roots.
- A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), §3.8(iv),
  printed p.77 / PDF p.24; registered source
  `borel-tits-1965-groupes-reductifs`. This passage compares unipotence with
  positivity for a suitable ordering, under its stated torus hypotheses.
- Their *Compléments à l'article « Groupes réductifs »* (1972), §5, printed
  pp.274–275 / PDF pp.23–24; registered source
  `borel-tits-1972-complements-groupes-reductifs`. The corrections concerning
  §3.8 change a subgroup comparison and a misprinted ambient root set; they do
  not change the positivity assertion used in the published target's provenance.

The Lean route is the elementary root-sign consequence of the published
dominant chamber theorem, whose proof maximizes evaluation on the sum of the
positive roots. Closedness is retained unchanged on both sides. This module
asserts no root-subgroup existence or intersection theorem and proves none of
the other components of `ClosedRootSubsetStatements`.

## Imports

| Module | Purpose |
| --- | --- |
| `Rational.ClosedRootSubsetStatements` | Exact target and root-subset definitions |
| `Rational.DominantChamberMove` | Move an integral cocharacter into the closed dominant chamber; root negation through its imports |
| `Rational.RelativeRootSystemProof` | Discharge the root-system hypothesis unconditionally |
| `Rational.RelativeWeylRootPermutation` | Preservation of actual relative roots |
| `Rational.WeylPositiveCocharacter` | Integral cocharacter action and pairing invariance |

All module names in this table have prefix `Langlands.GroupScheme`.

The shared ambient-root inclusion lemma is imported from
[RootSubsetAmbient](RootSubsetAmbient.md).
