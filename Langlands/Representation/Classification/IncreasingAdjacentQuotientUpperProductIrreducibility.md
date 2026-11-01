# Increasing adjacent quotient times its upper factor

Author: Worker 168. Worker 19 supplied the actual three-factor quotient
presentation used to close this proof.

The internal proposition
`Langlands.Classification.IncreasingAdjacentQuotientUpperProductIrreducibility`
and its closing theorem
`increasingAdjacentQuotientUpperProductIrreducibility` assert the following.
Fix any prime, actual p-adic field `F`, supplied topological data `T`, and
positive rank `d`. Let `B,A` be actual rank-`d` supercuspidal objects, with
`A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass`. Let
`P = B × A`, the normalized product along the literal positive two-block
shape. For every supplied invariant subspace `S` of `P` with `S ≠ ⊥` and
`S ≠ ⊤`, put `Q = P/S`. Then the actual normalized binary product `Q × A`
is irreducible.

The field universe `uF` and representation universe `uV` remain independent;
the factor and constituent carriers are in `Type (max uF uV)`. The total
rank is `((d+d)+d)`. The conclusion uses the actual quotient and product
objects, with upper-parabolic normalization from `T`. There is no
additive-character or product-presentation premise in the public proposition.
The nonzero proper invariant subspace `S` is supplied: existence of such a
subspace is a separate assertion. This unit supplies local rank-three
irreducibility for the host repeated-triple argument; the ambient Jacquet
extraction and both transfer implications remain separate host obligations.

## Implemented proof

The helpers are in `Classification.AdjacentUpperIrreducibility`.

`eq_d_or_two_d_of_dvd` is the elementary order bound. A positive multiple of
`d` strictly below `3d` equals `d` or `2d`.

`top_nontrivial_of_upper_derivative_support` gives the main obstruction.
It takes an actual rank-`3d` object `M` and a lower cuspidal datum `ρ`.
Its explicit hypotheses say that the actual derivatives of `M` of orders
`d` and `2d` have finite composition length, and that every irreducible actual
subquotient of either derivative has an actual supercuspidal support
containing `νρ`. For an irreducible actual subquotient `ω` of `M`, it further
uses the actual support with two copies of `νρ` and one copy of `ρ`, and
vanishing of all proper positive derivatives whose orders are not divisible
by `d`.

Choose the greatest bounded order `k` with a nonzero derivative of `ω`,
using `Nat.findGreatest`. The zeroth derivative is the identity, so such an
order exists. Suppose the top derivative were zero. Then `k` is proper.
The published positive-derivative detection theorem implies `k > 0`, and
nondivisible derivative vanishing implies `d ∣ k`. The elementary order
bound therefore gives `k=d` or `k=2d`.

Exactness of the actual derivative maps `ω`'s actual subquotient relation
into the corresponding derivative of `M`. Its finite length passes to the
derivative of `ω`. This derivative is nonzero, so Artinian atom extraction
supplies an actual irreducible invariant subspace `D` and an injective
intertwiner into it. Composing actual subquotient relations makes `D` an
actual subquotient of the derivative of `M`. The assumed support property
gives a support `s` of `D` containing `νρ`.

Because `k` is the highest nonzero order, the published actual
`highestDerivativeSupportShift` says that the multiset obtained by twisting
every member of `s` by `ν` is bounded by the displayed source support
`{ρ,νρ,νρ}`. The independently proved integral twist freeness makes `ν²ρ`
different from both `ρ` and `νρ`. Consequently that inequality excludes
`νρ` from `s`, a contradiction. The top derivative of every such `ω` is
therefore nonzero. Only the shifted support inequality is used here; no
unshifted general support inequality is assumed.

`support_of_irreducible_subquotient` composes the actual subquotient in a
supplied cuspidal induction presentation with the new actual subquotient
relation. This gives the same displayed support for the new irreducible
object directly from the definition.

`proper_derivative_data` discharges the two derivative hypotheses for
`M = Q × A`, using the proved first and second common-rank derivative
units. At order `d`, every actual nonzero Leibniz grade is transported `Q`
or `A × A`. Their irreducible actual subquotients have support `{B,A}` or
`{A,A}`, respectively, so the datum of `A` occurs. At order `2d`, every
irreducible actual derivative subquotient occurs in transported `A`;
composing its actual support presentation gives the singleton support.
Both derivative objects have finite group-algebra composition length by
those units. Equality elimination removes the prescribed rank transports.

`irreducible_of_product_presentation` applies the obstruction to every
irreducible actual subquotient of `Q × A`. At this intermediate helper only,
a supplied actual presentation by a supercuspidal product with displayed
support `{B,A,A}` and common divisor `d` gives both the actual support and
nondivisible derivative vanishing. The proper supplied `S` makes `P`
reducible, so the proved adjacent two-factor structure makes its actual
quotient `Q` irreducible. Finite length of the product of two irreducibles
then gives finite length of `Q × A`. Its actual top derivative has dimension
one by the separately proved top Leibniz calculation.

The exact-functor criterion
`ExactFunctorIrreducibility.isIrreducible_of_finrank_obj_eq_one` now applies:
the top derivative is exact, its value on the product has dimension one,
and it is nonzero on every irreducible actual subquotient. Thus `Q × A`
is irreducible. The functor exactness is the published
`generalLinearDerivativeExactness`, obtained by composing restriction,
equality rank transport, and the actual exact minus functors.

`increasing_quotient_upper_product_irreducible` removes the intermediate
presentation hypothesis. Set `C = Parabolic.threeBlocksRight d d d hd hd hd`
and choose the literal bundled supercuspidal family `B,A,A` by `Fin.cases`.
Every block rank is divisible by `d`. Equality of the class of `A` with
`ν[B]`, followed by commutativity of multiset addition, identifies its
three-entry support with `pairSupport ρ 2 1`. The pointwise identity of the
underlying smooth factor families is checked at all three indices.

Apply
`Parabolic.binaryRightProduct_isQuotient_threeBlocksRight` to the actual
quotient map `P → P/S`. It constructs an actual surjection
`B × A × A → Q × A`, hence an actual subquotient presentation, at the already
matching total rank `(d+d)+d`. The helper therefore proves irreducibility
without a remaining presentation premise. The general equality-based
`subquotient_product_of_rankCast` adapter is also provided, although this
literal bracketing does not require it.

Finally the public closing theorem chooses a continuous nontrivial unitary
additive character from the published
`HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T` and applies the
preceding helper. The character disappears from the stated conclusion.

## Provenance and dependency audit

This is internal derived content. Its meaning is justified by the implemented
actual quotient presentation, derivative computations, finite composition
length, exactness, individual highest-derivative support shift and integral
twist freeness. It does not use a printed classification assertion as an
unproved local irreducibility input.

The recursive project import closure contains 964 modules. Relative to
Library base `676ac944440098acb714f6b953083e88bb89c9c2`, 961 project Lean
files are byte-identical to the base. The three absent entries are this
entry, `AdjacentQuotientUpperProductFirstDerivative`, and
`Induction.ThreeFactorProductPresentation`. The latter two are separately
staged prerequisite units with their own independent review and integration
gates. All project modules have nonempty Markdown companions. External
imports are from Lean and Mathlib. The integrated
`Derivative.LocalPositiveLeibniz` is used unchanged, including its published
left mixed-product comparison, vanishing and right filtration proofs.

The derivative-support and top-dimension prerequisites retain their
documented lower proof routes: actual positive Leibniz gluing from minus
identities and exact localization, actual adjacent Jacquet structure and
partial derivatives, highest-derivative pairing and support shift, integral
twist freeness, and Whittaker multiplicity one. The highest-support result
uses individual cuspidal embeddings and support uniqueness from the actual
geometric lemma, together with duality and the derivative pairing; it does
not assume a global support decomposition.

The actual irreducible-product finite-length route embeds each original
irreducible factor separately into cuspidal induction, tensors and induces
the injections, and regroups the actual products. Finite length of cuspidal
induction is proved with a finite detecting family of actual Jacquet
functors, nonassociation vanishing and associated-grade bounds. Thus it
uses neither general ordered quotient coverage nor multisegment exhaustion.

The added triple presentation uses actual ordered induction in stages,
explicit factor-family equivalences, the positive-rank binary comparison,
and actual right-product exactness. That exactness splits the indexed
tensor into an ordinary binary tensor, uses flatness and tensor right
exactness, and applies actual normalized-induction exactness. The
regrouping proof composes actual tensor refinement, consecutive coordinates
and their half-modulus comparison, and induction in stages. No
irreducibility conclusion is a premise of the presentation.

The additive-character existence proof has only harmonic-analysis and
local-field project imports. It obtains a nontrivial character of
`ℚ_p/ℤ_p` from character-module duality, uses its discrete quotient topology
for continuity, and pulls it back by the surjective field trace. It has no
representation-classification dependency. The exact-functor irreducibility
criterion is the actual short exact sequence argument on an invariant
subspace and its quotient, using finite module length and nonvanishing
on simple actual subquotients.

Imported broad classification proposition definitions and conditional
assembly helpers are not applied as proved classification conclusions.
No used proof invokes the host's excluded analytic strong-head
classification, ordered strong-head existence, general ordered quotient
coverage, multisegment exhaustion, tempered block uniqueness,
square-integrable Langlands classification, square-integrable exhaustion
or regular exhaustion, or their conclusions under another name.
