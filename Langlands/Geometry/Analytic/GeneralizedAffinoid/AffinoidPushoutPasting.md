# Pasting actual bounded affinoid pushouts

For actual bounded maps `f : A → B`, `g : A → C`, and `h : C → D` of
presented affinoid algebras, this internal construction gives a bounded
algebra equivalence from the iterated closed-quotient pushout
`(B ⊗̂_A C) ⊗̂_C D` to the direct pushout `B ⊗̂_A D`, where the
direct second structural map is `h.comp g`. These symbols denote the
existing actual `AffinoidPushout.algebra` constructions.

The old pushout maps into the direct one by its actual bounded
universal property: use the direct first leg and the direct second leg
composed with `h`. This gives the iterated-to-direct map by a second
pushout lift. The direct-to-iterated map uses the composite of the two
original first legs and the original outer second leg. The two original
pushout equations prove its compatibility.

Pushout uniqueness proves both entire bounded inverse identities.
For the identity on the iterated quotient, apply uniqueness to the
outer pushout and then to the inner pushout. This constructs
`pastingEquiv`. Its formulas preserve the entire original `D` leg and
the composite original `B` leg. No equality is inferred from spectrum
points or merely algebraic tensor products.

The coefficient field is any complete ultrametric normed field, including
trivially normed fields. The presentations use arbitrary positive
polyradii. No finiteness, injectivity, nonzero-algebra or nonempty-spectrum
hypothesis is used. This is an internal consequence of the published
actual bounded pushout universal property, with no external theorem
transcription.
