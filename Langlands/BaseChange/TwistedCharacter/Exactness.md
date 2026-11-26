# Exactness and vanishing of twisted distributions

This module proves exactness and diagonal formulas for the twisted distribution
`Langlands.BaseChange.twistedDistribution μ ρ hρ T` of the Library module
`Langlands.BaseChange.TwistedCharacter.Basic`. That distribution sends a
Schwartz–Bruhat test function `φ` to `FiniteRankEnd.trace` of the finite-rank
operator `ρ(φ) ∘ T`, where `ρ(φ)` is `Hecke.integratedAction μ ρ hρ.1 φ`.

These derived lemmas implement trace relations used in the construction of
twisted pseudo-coefficients (Henniart–Lemaire 2011, II.5.10–II.5.13).

## Setting

`G` is a group with a topology that makes it a Hausdorff, locally compact,
totally disconnected topological group, with a measurable structure equal to the
Borel sigma-algebra. The measure `μ` on `G` is finite on compact sets and left
invariant. These are the hypotheses of `twistedDistribution`. No Haar
normalization is chosen. All vector spaces are complex vector spaces of
arbitrary dimension. The twisting endomorphisms are arbitrary complex-linear
maps: the results do not assume that they intertwine `ρ` with a twist of `ρ`,
or that they are invertible.

## `Langlands.FiniteRankEnd.trace_eq_zero_of_offDiagonal`

Let `V` be a complex vector space and let `e i` (for `i` in a finite type `ι`) be
linear endomorphisms of `V` with `∑ i, e i = 1` and `e i ∘ e i = e i` for each `i`.
Let `T` be a finite-rank endomorphism of `V` (an element of the Library type
`finiteRankEnd V`) whose diagonal blocks vanish: `e i ∘ T ∘ e i = 0` for every `i`.
Then `FiniteRankEnd.trace T = 0`.

The idempotents need not commute with each other or with `T`.

Proof. Since `∑ i, e i = 1`, `T` is the sum of the finite-rank maps `T ∘ e i`.
Each one equals `(T ∘ e i) ∘ e i` because `e i` is idempotent. Cyclicity of the
finite-rank trace (the Library lemma `FiniteRankEnd.trace_comp_of_hasNoetherianRange`,
applied to the finite-rank map `T ∘ e i` and to `e i`) turns its trace into the
trace of `e i ∘ T ∘ e i = 0`. Linearity of the trace then gives `trace T = 0`.

## `Langlands.BaseChange.twistedDistribution_shortExact`

Let `ρA`, `ρB`, `ρC` be admissible representations of `G` on `A`, `B`, `C`, with
admissibility proofs `hA`, `hB`, `hC`. Let `f : ρA → ρB` and `g : ρB → ρC` be
intertwining maps forming a short exact sequence: `f` is injective, `g` is
surjective, and the range of `f` equals the kernel of `g`. Let `TA`, `TB`, `TC` be
complex-linear endomorphisms of `A`, `B`, `C` with `TB ∘ f = f ∘ TA` and
`g ∘ TB = TC ∘ g`. Then

`twistedDistribution μ ρB hB TB = twistedDistribution μ ρA hA TA + twistedDistribution μ ρC hC TC`.

The sequence need not split as a sequence of representations, and the splitting
of the underlying vector spaces need not be compatible with the `T`'s.

This is the twisted analogue of the Library's short-exact additivity of ordinary
character distributions (module `Langlands.Representation.Character.ExactAdditivityProof`).
It is what makes a twisted character well defined on the Grothendieck group of
`σ`-representations of finite length in HL II.5.2, printed p. 101, and II.5.4 Remark,
printed p. 103. There HL note that the category of `σ`-representations is not
abelian, but that short exact sequences of `σ`-representations make sense. Our
hypotheses are exactly a short exact sequence of representations together with
endomorphisms compatible with both maps.

Proof. Evaluate both sides at a test function `φ`. The operators `ρ(φ) ∘ TA`,
`ρ(φ) ∘ TB` and `ρ(φ) ∘ TC` have finite rank. They are compatible with `f` and `g`,
because `ρ(φ)` commutes with intertwining maps (Library lemma
`Hecke.integratedAction_intertwiner`) and the `T`'s are compatible by hypothesis.
The Library lemma `FiniteRankEnd.trace_shortExact` (module
`Langlands.LinearAlgebra.FiniteRankTraceExact`) then gives the additivity of the traces.

## `Langlands.BaseChange.twistedDistribution_eq_zero_of_offDiagonal`

Let `ρ` be an admissible representation of `G` on `V`, and let `e i` (for `i` in a
finite type `ι`) be endomorphisms of `V` with `∑ i, e i = 1`, `e i ∘ e i = e i`, and
`e i ∘ ρ g = ρ g ∘ e i` for all `i` and `g`. Thus the `e i` are `G`-equivariant
idempotents with sum `1`. Let `T` be an endomorphism of `V` with
`e i ∘ T ∘ e i = 0` for every `i`. Then `twistedDistribution μ ρ hρ T = 0`.

Example: HL II.5.4, printed pp. 102–103, define `ι_s(Π₀, A₀)` for `s > 1` on
`V = ⊕_{i<s} V_{Π₀}` with `A(v₀, …, v_{s-1}) = (v₁, …, v_{s-1}, A₀ v₀)`. Take `e i` to be
the projection onto the `i`-th summand. Each summand is `G`-stable, and `A` maps the
`i`-th summand into the `(i-1)`-th one, so every diagonal block of `A` is zero.
The theorem then says that the twisted character of `ι_s(Π₀, A₀)` vanishes.
HL use this vanishing in II.5.4 Remark, printed p. 103, when the twisted character
factors through their quotient of the Grothendieck group.

Proof. Evaluate at a test function `φ` and apply
`FiniteRankEnd.trace_eq_zero_of_offDiagonal` to `ρ(φ) ∘ T`. Its diagonal blocks are
`e i ∘ ρ(φ) ∘ T ∘ e i = ρ(φ) ∘ (e i ∘ T ∘ e i) = 0`, because each `e i` is an
intertwining map from `ρ` to itself, so it commutes with `ρ(φ)` by
`Hecke.integratedAction_intertwiner`.

## Trace as a sum of diagonal components

`Langlands.FiniteRankEnd.trace_eq_sum_of_resolution` takes a finite family
of linear maps `j_i` and `q_i` whose composites `j_i ∘ q_i` sum to the
identity. For a finite-rank endomorphism `T`, it writes `T` as the sum
of `j_i ∘ q_i ∘ T` and uses cyclicity of the finite-rank trace to obtain
the sum of the traces of `q_i ∘ T ∘ j_i`.

`Langlands.BaseChange.twistedDistribution_eq_sum_diagonal` applies this
formula to the integrated action composed with the twisting map, using
equivariant `j_i` and `q_i`. The projections commute with the integrated
action, so the summands are the twisted distributions on the constituent
spaces for the diagonal maps of the twisting operator.

## Sources

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. Soc. Math. France 124 (2011), II.5.2, printed
  pp. 100–101 (σ-representations, short exact sequences, Grothendieck group), and II.5.4,
  printed pp. 102–103 (the functor `ι_s` and the Remark on the vanishing of twisted
  characters).
