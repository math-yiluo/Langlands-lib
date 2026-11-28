# Central characters under arithmetic weak base change

Let `E/F` be an extension of number fields and let `S` and `T` be cuspidal operator
realizations of the same positive rank over `F` and `E`, respectively. If `S` has
central character `ω` and the class of `T` is an arithmetic weak base change of
the class of `S`, then `T` has central character `ω ∘ N_{E/F}`. This holds in the
common field universe used by `HeckeCharacter.normComp`, with independent universes
for the two spectral presentations.

The arithmetic relation is the unramified Satake power comparison in Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula* (1989),
I §4 and III §1, Definition 1.1. Taking the product of the Satake parameters gives
this consequence for central characters. The proof uses the cofinite comparison
and idele density, through the central-character lemmas in
`Langlands.Automorphic.CentralCharacterTopCoefficient`.

`HeckeCharacter.normComp_finiteUniformizerValue` specializes the local norm formula
at the chosen uniformizers. At a place `w` above `v` of ramification index one,
the uniformizer value of the pulled-back unramified character is `ω_v(ϖ_v)` raised
to the residue degree.

`CuspidalOperatorRealization.hasCentralCharacter_normComp_of_isWeakBaseChangeOf`
chooses spectral presentations of the two realizations that witness weak base
change. Outside finitely many places of `F`, the lower central character is
unramified and its uniformizer value equals the top elementary coefficient of
the lower spectrum. Restriction of places preserves the cofinite filter. At each
upper place in the resulting cofinite set, the norm pullback is unramified and
its uniformizer value equals the top elementary coefficient of the upper spectrum.
Indeed, the top coefficient is the product of the parameters, so powering the
parameters raises this product to the same power. The converse central-character
lemma then gives the asserted action of all scalar ideles on `T`.

`weakBaseChangeCentralCharacter` proves the universally quantified
`WeakBaseChangeCentralCharacterStatement` by applying this result.
