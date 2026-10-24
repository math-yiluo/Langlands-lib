# Finite whole image under finite-index induction

Worker 261 proves the published proposition
`Langlands.Weil.RepresentationInductionFiniteImage.{uG,uV}` from
[`InductionFinitenessStatements`](InductionFinitenessStatements.md) by the
closed theorem `Langlands.Weil.representationInductionFiniteImage`. The only
project import is `Langlands.Weil.Representation.InductionFinitenessStatements`;
that statement pair and everything it imports are unchanged.

For every group `G : Type uG`, subgroup `H` with `[H.FiniteIndex]`, complex
vector space `V : Type uV` with `[FiniteDimensional ℂ V]`, and
`ρ : Representation ℂ H V`, the theorem proves

`(Set.range (ρ.ind H.subtype)).Finite ↔ (Set.range ρ).Finite`.

Both ranges are ranges of the actual action homomorphisms: Mathlib's
`Representation.ind` on its carrier `Representation.IndV H.subtype ρ`, and `ρ`
itself. No coordinate model, coinduced representation or replacement carrier
is introduced. The universes `uG` and `uV` stay independent. The closing
`example` assigns the entire unapplied constant
`@representationInductionFiniteImage.{uG, uV}` to
`RepresentationInductionFiniteImage.{uG, uV}`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Notation and Mathlib facts used

Write `[x ⊗ v]` for `IndV.mk H.subtype ρ x v`, with `x : G` and `v : V`.
`IndV H.subtype ρ` is the module of coinvariants of `ℂ[G] ⊗[ℂ] V` under the
diagonal `H` action, which sends `x ⊗ v` to `(s*x) ⊗ ρ(s)(v)` for `s ∈ H`.
Hence `[s*x ⊗ ρ(s)(v)] = [x ⊗ v]`; this is `Coinvariants.mk_self_apply`. The
induced action is given on generators by
`Representation.ind_mk`: `g` sends `[x ⊗ v]` to `[x*g⁻¹ ⊗ v]`. Two linear maps
out of `IndV` agree when they agree on all generators
(`Representation.IndV.hom_ext`).

## Reflection: finite induced image gives finite image of `ρ`

The private linear map `identityCosetProjection : IndV H.subtype ρ →ₗ[ℂ] V`
sends `[x ⊗ v]` to `ρ(x⁻¹)(v)` when `x ∈ H` and to `0` otherwise. It is first
defined on `ℂ[G] ⊗[ℂ] V` with `Finsupp.lift`, `MonoidAlgebra.coeffLinearEquiv`
and `TensorProduct.lift`. It then descends through
`Representation.Coinvariants.lift`, which needs invariance under the diagonal
action on generators. If `x ∈ H`, then `s*x ∈ H` and
`ρ((s*x)⁻¹)(ρ(s)(v)) = ρ(x⁻¹)(v)`. If `x ∉ H`, then `s*x ∉ H` and both values
are `0`. The private lemma `identityCosetProjection_mk` records the generator
formula.

The private lemma `compress_ind` shows, for `s ∈ H`, that composing the
projection with the induced action of `s` and the linear map `IndV.mk H.subtype ρ 1`
from `V` (the identity-coset copy) gives exactly `ρ(s)`. On a vector `v` this is

`ρ.ind H.subtype s [1 ⊗ v] = [s⁻¹ ⊗ v] ↦ ρ((s⁻¹)⁻¹)(v) = ρ(s)(v)`.

Thus `A ↦ identityCosetProjection ∘ₗ A ∘ₗ IndV.mk H.subtype ρ 1` maps
`Set.range (ρ.ind H.subtype)` onto a set containing `Set.range ρ`. The image
of a finite set is finite, so `finite_range_of_finite_range_ind` concludes by
`Set.Finite.subset`. This direction is proved for an arbitrary subgroup: its
lemma takes neither a finite-index nor a finite-dimension hypothesis.

## Preservation: finite image of `ρ` gives finite induced image

1. `finiteIndex_ker_of_finite_range` shows that `ρ.ker` has finite index in
   `H`. Mathlib's `ρ.toHomUnits : H →* (Module.End ℂ V)ˣ` has the same kernel
   as `ρ`. Its range is finite, because `Units.val` is injective and sends it
   into `Set.range ρ`. Mathlib's instance `Subgroup.finiteIndex_ker` then
   applies to `ρ.toHomUnits`.
2. Let `K = (ρ.ker).map H.subtype`, a subgroup of `G`.
   `Subgroup.index_map_subtype` gives
   `K.index = (ρ.ker).index * H.index`. Both factors are nonzero, the
   second by the hypothesis `[H.FiniteIndex]`, so `K` has finite index.
   This is the only use of `[H.FiniteIndex]`.
3. Let `N = K.normalCore`, the largest normal subgroup of `G` contained in
   `K`. It has finite index by Mathlib's instance
   `Subgroup.finiteIndex_normalCore`.
4. `ind_eq_one_of_mem_normalCore` shows that every `g ∈ N` acts as the
   identity on `IndV H.subtype ρ`. By `IndV.hom_ext` it suffices to check
   generators `[x ⊗ v]`. Since `g⁻¹ ∈ N`, the conjugate `x*g⁻¹*x⁻¹` lies in `K`,
   so it equals some `k ∈ ρ.ker` viewed in `G`, and `x*g⁻¹ = k*x`. Then
   `[x*g⁻¹ ⊗ v] = [k*x ⊗ ρ(k)(v)] = [x ⊗ v]` by `ρ(k) = 1` and
   `Coinvariants.mk_self_apply`.
5. Hence `N ≤ (ρ.ind H.subtype).ker`, and `QuotientGroup.lift` factors the
   induced action through `G ⧸ N`. That quotient is finite, so the lift has
   finite range (`Set.finite_range`). Every `ρ.ind H.subtype g` equals the
   lift at the class of `g`. So `finite_range_ind_of_finite_range` obtains
   the finite range of the induced action as a subset of that finite range.

The closing theorem combines the two directions after introducing the binders.

## Hypotheses and scope

The proof uses no normality of `H`, topology, continuity, irreducibility,
positive dimension or finite dimension of the induced carrier. The hypothesis
`[FiniteDimensional ℂ V]` of the target is not used by either direction. No
case split on dimension occurs, so the zero-dimensional case is covered by the
same argument.

This theorem proves only the finite-image component. It makes no claim about
the dimension or semisimplicity components, their aggregate
`RepresentationInductionFiniteness`, topology, actual local Weil
specialization, or a Langlands correspondence.

## Provenance

This is derived generic algebraic representation theory over `ℂ`, as the
statement Markdown and `RestrictionInduction.md` label it. It is not a verbatim
theorem of the cited original. That original is John Tate, *Number theoretic
background*, in *Automorphic Forms, Representations and L-Functions*,
Proceedings of Symposia in Pure Mathematics 33, Part II (1979), pages 3–26.
The relevant part is section 2.1, printed pages 9–10 / PDF pages 18–19.
Registered literature ID: `tate-1979-number-theoretic-background`. Retained file:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Worker 261 read these pages. Tate there takes representations to be
continuous and finite-dimensional over `ℂ`. He gives restriction and
induction maps for a finite separable extension `E/F`, identifying `W_E` with
a closed finite-index subgroup of `W_F`. On printed page 10, (2.2) characterizes
representations of Galois type as those with finite image `ρ(W_F)`. Tate does
not state or prove that finite-index induction preserves and reflects finite
image. The kernel and normal-core argument and the identity-coset compression
argument above are standard group and representation theory written by
Worker 261 for this proof.

The quotient-lift construction of `identityCosetProjection` adapts the
`invFun` construction of Amelia Livingston's `Rep.indResHomEquiv` in Mathlib's
`Mathlib/RepresentationTheory/Induced.lean`, lines 140–146: the
`Coinvariants.lift`/`TensorProduct.lift`/`Finsupp.lift` expression and its
first two invariance-proof tactic lines. The Library proof
`InductionReciprocityProof` also adapts this construction. Here the family of
maps is changed to `ρ(x⁻¹)` on `H` and `0` off `H`, and the invariance proof
splits on membership in `H`. The Lean file retains the upstream copyright
and Apache-2.0 notice. `Representation.ind_mk` and
`Representation.IndV.hom_ext` come from the same file, lines 84 and 68.
Source ID: `mathlib-induced-5ed296525643`; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; source file SHA-256
`f462f392700d339611a2fb1480192d0a870efa20c06d248a96122b90fc6a79b2`.

## Dependencies

The sole direct import is the unchanged published
`Langlands.Weil.Representation.InductionFinitenessStatements`. Every other
construction and lemma used comes from pinned Mathlib by Lean name. The
approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).
