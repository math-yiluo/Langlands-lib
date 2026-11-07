# Closed immersion of the actual split Steinberg root product

The theorem `Langlands.GroupScheme.splitSteinbergImmersion` proves exactly the
published `SplitSteinbergImmersionStatement.{u}`. Its scope is every field
`k : Type u`, every actual affine group scheme with a supplied split pinning and
the stated semisimplicity hypothesis, every ordering of the simple roots, and all
supplied normalized root maps and simple-reflection representatives. The empty
simple-root family is included. The conclusion is a closed immersion of the
underlying schemes of the existing actual ordered morphism.

The proof applies the internal reduction in
`SteinbergIndependentWeightReduction` to the general theorem
`independentWeightProductImmersion` in `IndependentWeightProductProof`. The
reduction identifies the actual Steinberg morphism with the product of the
prefix-conjugated root maps followed by right translation by the full product
of the supplied representatives. The prefix maps are closed additive embeddings
with independent integral weights for conjugation by the pinning's split torus.
The general criterion proves that their ordered product is a closed immersion;
right translation is a scheme isomorphism and preserves that property.

The helper pair contains the all-test product calculation, the equality of
actual scheme morphisms, and the application of the criterion. The closing
theorem supplies that criterion from its proved general statement, so it retains
no additional premise. This is an internal derivation from the cited Library
modules. It neither asserts existence of the supplied families nor constructs a
rational section for any quasi-split group.
