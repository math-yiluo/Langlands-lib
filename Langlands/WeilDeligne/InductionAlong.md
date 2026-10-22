# Induction along an injective homomorphism

Worker 17 authored this construction module. It imports
`Langlands.WeilDeligne.ParameterInduction` and
`Langlands.WeilDeligne.ParameterRestriction`.

The existing finite-index induction is defined for an actual subgroup
`S ≤ G`. A finite extension `E/F` instead supplies a group `W_E` together
with an injective homomorphism `ι : W_E → W_F`. This module moves a
representation or pair of `H` to the range `ι(H)` and induces it from there,
so that the local specialization needs no new induction construction.

## Construction

`InductionAlong.rangeInverse ι hι` is the inverse of the corestriction
`H ≃* ι.range` from Mathlib's `MonoidHom.ofInjective`. The lemmas
`apply_rangeInverse` and `rangeInverse_apply` state the two inverse laws.
For a topological embedding, `continuous_rangeInverse` proves continuity
of this inverse: composing with the embedding gives the subtype inclusion.
For an open embedding, `isOpen_range` proves that the range subgroup is open.

`FiniteRepresentation.induceAlong ι hι A` is
`induce ι.range (restrict (rangeInverse ι hι) A)`, with its functor,
equivalence transport and class operation. `rank_induceAlong` gives
`[G : ι(H)] * rank A`; rank zero is allowed.

For pairs, the restricted pair has norm `νH ∘ rangeInverse`, while
induction from the range requires the restricted ambient norm `ν|ι(H)`.
The hypothesis `hν : ∀ h, ν (ι h) = νH h` makes them pointwise equal
(`norm_rangeInverse`). `ofNormEq` regards a pair with a pointwise equal norm
character: carrier, action and monodromy are unchanged and only covariance
is restated. `ofNormEqMap`, `ofNormEqFunctor` and `ofNormEqEquiv` keep the
same linear maps. `WeilDeligneRepresentation.induceAlong ι hι hν A` then
induces from the range. Its monodromy is the weighted operator
`N_ind(f)(g) = ν(g) N(f(g))` (`induceAlong_monodromy_apply`), so nonzero
monodromy is retained. The module supplies the functor, equivalence
transport, class operation and rank formula.

## Open-inertia parameters

The open-inertia versions assume that `G` is a topological group, that `H`
has a specified topology, and:

- `ι` is an open embedding (`Topology.IsOpenEmbedding`), with finite-index
  range;
- the ambient inertia `I` is open in `G`;
- `hJ : ∀ h, ι h ∈ I → h ∈ J`, that is, `ι⁻¹(I) ⊆ J` for the source
  inertia `J`;
- for pairs, the norm compatibility `hν`.

`hasOpenInertiaKernel_induceAlong` restricts along the continuous inverse
(the open-kernel certificate of `ParameterRestriction`, using `hJ` to map
`I ∩ ι(H)` into `J`) and then applies the published induction certificate
for an open subgroup and open inertia. `openInertiaInduceAlong`,
`openInertiaInduceAlongClass`, `parameterInduceAlong`,
`parameterInduceAlongClass` and `parameterInduceAlongClassOfRank` give
actual objects and genuine classes, the last from rank `n` to rank
`[G : ι(H)] * n`.

## Source correspondence and scope

Tate, *Number theoretic background*, Corvallis Part II: §1.4.5, printed
page 7 (PDF page 16), states that the subgroups `W_E` of `W_F` for finite
extensions `E/F` are exactly the open subgroups of finite index. §1.4.6,
printed page 7, states that the norm of `W_F` restricts to the norm of
`W_E`, which is the hypothesis `hν`. §1.4.1, printed page 6 (PDF page 15),
defines inertia as the subgroup fixing the residue closure, so that
`I_E = I_F ∩ W_E` for an actual extension. §2.1, printed pages 9–10
(PDF pages 18–19), uses induction from `W_E`, identified with a closed
subgroup of finite index of `W_F`. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The range transport and the norm change are derived construction
obligations, proved here.

This is a generic construction along supplied data. The actual inclusion
`W_E → W_F` for a finite extension of p-adic fields, its openness, finite
index, inertia compatibility and norm compatibility belong to the local
specialization and are not asserted here. No Mackey formula, induction
compatibility with other operations, Frobenius-semisimplicity preservation
or usual-topology continuity statement is included.
