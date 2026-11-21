# Additivity of finite-Galois conductors in short exact sequences

This module proves the published proposition
`Langlands.Ramification.Padic.FiniteGaloisConductorExactSequenceStatement`
(module `Langlands.LocalFactor.Ramification.FiniteStatement`). The theorem is

`Langlands.Ramification.Padic.finiteGaloisConductorExactSequence`.

It holds for every prime `p`, every `F : PadicField.{uL} p` with topological data
`T`, every field `K` in the scalar tower `Padic p → K → F.Carrier`, and all
finite-dimensional complex vector spaces `U`, `V`, `W`. The universe levels
`uK`, `uL`, `uU`, `uV`, `uW` are independent. Its complete type is the target
type, with the binders in the same order: `{p} [Fact p.Prime] {F} (T) (K)`,
the instances on `K`, then `{U}`, `{V}`, `{W}` with their instances.

## Statement proved

Let `F/K` be Galois with group `G = F.Carrier ≃ₐ[K] F.Carrier`. Let
`ρ`, `σ`, `τ` be complex representations of `G` on `U`, `V`, `W`. Let
`i : U → V` and `q : V → W` be intertwining maps such that `i` is injective,
the range of `i` equals the kernel of `q`, and `q` is surjective. Then

`a_K(σ) = a_K(ρ) + a_K(τ)` and `sw_K(σ) = sw_K(ρ) + sw_K(τ)`.

Here `a_K = Padic.artinConductor T K` and `sw_K = Padic.swanConductor T K`.
They are the Library's rational sums
`Σ_i |G_i|/|G_0| · (dim V − dim V^(G_i))`, over `i ≥ 0` for Artin and `i ≥ 1`
for Swan. The `G_i` are the lower ramification groups of the integer-ring
action. The proof adds no hypothesis on the ramification groups, the
representations or the conductors. It does not use the Galois hypothesis,
only that `G` is finite.

## Proof outline

Fixed vectors of every subgroup form a short exact sequence again, because
averaging over a finite group is possible in characteristic zero. So every
fixed-space dimension is additive, and so is every fixed-space codimension.
Each conductor summand is a fixed rational weight times such a codimension,
so each summand is additive. The two conductors are finite sums of summands
over a common range, so they are additive. The last step applies this to the
actual integer-ring action of the finite p-adic Galois group.

## Declarations, in order

### Linear algebra

`finrank_eq_add_of_shortExact` (field `k`, linear maps `f : A → B`,
`g : B → C`, `B` finite-dimensional). If `f` is injective,
`range f = ker g` and `g` is surjective, then
`finrank B = finrank A + finrank C`. Proof: rank–nullity for `g`
(Mathlib `LinearMap.finrank_range_add_finrank_ker`). The range of `g` is
everything (`LinearMap.range_eq_top`, `finrank_top`). The kernel of `g` is the
range of `f`, which has the dimension of `A` because `f` is injective
(`LinearMap.finrank_range_of_inj`).

### Fixed vectors

The fixed vectors `Langlands.fixedVectors ρ N` (module
`Langlands.Representation.Smooth.Definitions`) are by definition Mathlib's
`Representation.invariants (ρ.comp N.subtype)`. An intertwiner `f` restricts to
`Langlands.fixedVectorsMap f N` between fixed vectors (module
`Langlands.Representation.Smooth.FixedVectors.Definitions`). In this section
`N` is a subgroup with a `Fintype` instance whose cardinality is invertible in
`k`.

- `averageMap_eq_smul_sum`. Mathlib's `Representation.averageMap π v` (module
  `Mathlib.RepresentationTheory.Invariants`) equals `(1/|H|) • Σ_h π h v` for a
  representation `π` of a finite group `H`. Proof: unfold the averaging
  element `GroupAlgebra.average` and simplify.
- `intertwiningMap_averageMap`. For an intertwiner `q`,
  `q (average_σ v) = average_τ (q v)` for averaging over `N`. Proof: by the
  previous lemma, linearity of `q`, and `q (σ g v) = τ g (q v)`
  (`IntertwiningMap.isIntertwining`).
- `fixedVectorsMap_surjective`. If `q` is surjective, so is
  `fixedVectorsMap q N`. Proof: lift `w ∈ W^N` to some `v ∈ V`. The average
  `v'` of `v` over `N` is `N`-fixed (`Representation.averageMap_invariant`).
  By the previous lemma `q v'` is the average of `w`, which is `w` because `w`
  is fixed (`Representation.averageMap_id`).
- `range_fixedVectorsMap_eq_ker`. If `i` is injective and `range i = ker q`,
  then the range of `fixedVectorsMap i N` is the kernel of
  `fixedVectorsMap q N`. Proof: one inclusion is `q (i u) = 0`. For the
  other, a fixed `v` with `q v = 0` equals `i u` for some `u ∈ U`. Then `u` is
  fixed: for `g ∈ N`, `i (ρ g u) = σ g (i u) = σ g v = v = i u`, and `i` is
  injective.
- `finrank_fixedVectors_eq_add`. Under the three exactness hypotheses and `V`
  finite-dimensional,
  `dim V^N = dim U^N + dim W^N`. Proof: `finrank_eq_add_of_shortExact` for
  `fixedVectorsMap i N` (injective as a restriction of `i`) and
  `fixedVectorsMap q N`, with the two previous lemmas.
- `fixedCodimension_eq_add`. With `U`, `V`, `W` finite-dimensional,
  `fixedCodimension G σ N = fixedCodimension G ρ N + fixedCodimension G τ N`.
  Here `fixedCodimension G ρ N = dim U − dim U^N` with natural subtraction
  (module `Langlands.LocalFactor.Ramification.Conductor`). Proof:
  `dim V = dim U + dim W` by `finrank_eq_add_of_shortExact` for `i` and `q`,
  together with the previous lemma. Each fixed space is a subspace, so
  `dim U^N ≤ dim U` and `dim W^N ≤ dim W` (`Submodule.finrank_le`). Hence
  the natural subtractions add (`omega`).

### Generic conductors

This section works with the generic definitions of module
`Langlands.LocalFactor.Ramification.Conductor`: a local ring `R` with an
action of a group `G` by ring automorphisms, and a field `k` of
characteristic zero. The lower groups are `lowerGroup R G n`.

- `conductorTerm_eq_add` (`G` finite). The summand
  `conductorTerm R G ρ n = |G_n|/|G_0| · fixedCodimension G ρ G_n` is
  additive. Proof: give `G_n` a `Fintype` instance (`Fintype.ofFinite`). Its
  cardinality is nonzero in `k` by characteristic zero, hence invertible
  (`invertibleOfNonzero`). Then `fixedCodimension_eq_add` and distributivity
  apply.
- `artinConductor_eq_add` and `swanConductor_eq_add` (`R` Noetherian, `G`
  finite and acting faithfully). The generic `artinConductor R G` and
  `swanConductor R G` are additive. Proof: the Library theorem
  `exists_lowerGroup_eq_bot` gives `b` with `G_n = ⊥` for `n ≥ b`. The
  Library theorems `artinConductor_eq_sum_range` and
  `swanConductor_eq_sum_range` write all three conductors as sums over
  `Finset.range b`: of `conductorTerm R G _ n` for Artin, and of
  `conductorTerm R G _ (n + 1)` for Swan. Then `Finset.sum_add_distrib` and
  `conductorTerm_eq_add` termwise finish the proof.

### The p-adic specialization

`Padic.artinConductor T K` and `Padic.swanConductor T K` (module
`Langlands.LocalFactor.Ramification.Galois`) are the generic sums for the
actual action `Padic.integerAction T K` of `G` on the integer ring
`T.Integers`. The proof uses three published lemmas to supply the same
instance facts as the private proofs in `Galois`:

- `Langlands.Ramification.HerbrandBridge.integerAction_faithful` (module
  `Langlands.LocalFactor.Ramification.Herbrand.QuotientProof`) gives
  faithfulness. Two automorphisms that agree on the valuation subring
  `T.Integers` agree on its fraction field `F.Carrier` by
  `IsFractionRing.ringHom_ext`.
- `Langlands.LocalFactor.SpectralConductor.integerRing_noetherian'` (module
  `Langlands.LocalFactor.SpectralConductorFunctional`) gives Noetherianity
  of `T.Integers` using the topology, valuation relation and local-field
  structure of `T`.
- `Langlands.LocalFactor.SpectralConductor.automorphismGroup_finite'` (the
  same module) gives finiteness of `G`. It first obtains finite dimension of
  `F.Carrier` over `K` from finite dimension over `Padic p` by
  `Module.Finite.of_restrictScalars_finite`, then uses finiteness of the
  automorphism group of a finite-dimensional field extension.

`finiteGaloisConductorExactSequence` introduces the Galois premise, the
representations, the intertwiners and the three exactness hypotheses. It
installs the integer action and the three facts above as local instances,
then applies `artinConductor_eq_add` and `swanConductor_eq_add` with
`R = T.Integers`. Both p-adic definitions unfold to the corresponding
`R`-based definitions with the same action. The three instance arguments
are proofs of propositions, so the imported proofs and the private ones in
`Galois` agree by proof irrelevance.

## Checks

`lean_check` compiles the module with no errors or warnings. The axioms of
the theorem are `propext`, `Classical.choice` and `Quot.sound`. A separate
file assigned the unapplied constant `@finiteGaloisConductorExactSequence` to
the full target type quoted in the task, and compiled. This confirms the
binder order and universe levels.

## Sources

This is the additivity of the conductor as a function on characters in Serre,
*Local Fields* (1979), Chapter VI §2 (literature ID `serre-1979-local-fields`).
Proposition 2 and Corollary 1' there (printed pp. 100–101) give the Artin
conductor as the weighted sum of fixed-space codimensions, which is the Library
definition. The Swan conductor is its positive-index part, as in Deligne (1973),
§4.5 (literature ID `deligne-1973-local-constants`). The target Markdown
`Langlands/LocalFactor/Ramification/FiniteStatement.md` explains these sources.
The Lean proof is the direct averaging argument above. It does not go through
characters.
