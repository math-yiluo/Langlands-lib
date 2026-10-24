# Base change of the actual Picard-zero universal property

`PicardZeroUniversalBaseChangeStatement` states that for any morphism
`b : S' → S` of schemes, any abelian scheme `A/S`, and any actual universal
rigidified Picard-zero family `L` with parameter scheme `P/S`, the family
`(baseChangeFamily b A P).obj L` is universal for `A_{S'}`. Its parameter
scheme is the actual fibre product `P_{S'}`. All schemes lie in the same
universe; there is no noetherian, reducedness, projectivity or field
hypothesis.

Both occurrences of `IsUniversalPicardZero` have their existing concrete
meaning. The family satisfies geometric Picard-zero on every geometric
fibre, and for every test scheme, every rigidified Picard-zero class is
uniquely the class of an actual parameter pullback of that family. Thus the
conclusion includes both the geometric fibre condition and unique
classification on all test schemes, including nonreduced ones. It does
not merely assert existence of some new universal family or some unrelated
representing scheme.

The new family is the constructed composite of parameter pullback along
`P_{S'} → P` and ground-base pullback. Its ordinary line bundle is already
identified with pullback along
`P_{S'} ×_{S'} A_{S'} → P ×_S A`. This statement does not assume the desired
new universal property, a dual comparison isomorphism, or representability
of any other family.

This file states a theorem obligation as a `Prop`-valued definition. It
contains no proof of that obligation and establishes no unconditional
existence of a dual abelian scheme or geometry of its parameter scheme.

## Provenance and proof obligations

This is a derived base-change statement for the existing actual universal
property. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
March 14, 2021 thesis revision, Lemma 1.3.2.2(2), Theorem 1.3.2.3 and
Definition 1.3.2.5, printed p.74 (PDF102), give the rigidified Picard-zero
functor, its representing dual, and its universal Poincare family. The
preceding Definition 1.3.2.1(2)(b), printed p.73 (PDF101), specifies the
fibre condition. These passages motivate the universal property; they do
not explicitly state the exact base-change theorem formalized here.

For each `T/S'`, the canonical isomorphism
`T ×_{S'} A_{S'} ≅ T ×_S A` should identify actual rigidified families,
their isomorphism classes and their geometric Picard-zero conditions.
The slice pullback adjunction identifies maps `T → P_{S'}` over `S'` with
maps `T → P` over `S`. Compatibility of these identifications with the
explicit constructed family should transport unique classification.
Proving these comparisons, including pullback and rigidification
coherence and the geometric fibre identifications, is part of the proof
obligation, not an established result of this module.

Lan uses the second parameter factor, whereas the Library uses the first.
The Library's geometric fibre condition uses translation invariance of the
line bundle on algebraically closed fibres. Its equivalence with the
source's algebraic-equivalence condition is not proved here. The stated
transport property is intrinsic to the existing Library definition, so
its proof can work directly with translation invariance. Its arbitrary-base
scope comes from transporting a supplied universal property by scheme
pullbacks; it does not extend Lan's existence theorem beyond his
quasi-separated base convention.
