# Actual prime Tate maps for rational homomorphisms

This internal construction extends the existing actual prime Tate maps on
abelian-scheme homomorphisms to the existing rational Hom spaces. It is valid over
an arbitrary base scheme and every rational prime, for any test object over the
base. It uses the actual `PrimeAdic.Rational` module.

`PrimeAdic.rationalFunctor` bundles the published prime Tate maps into an additive
functor with values in modules over the p-adic field. The existing additive
rationalization lift defines `rationalizedFunctor` and `rationalHomMap`. The
latter is rational-linear in the rational homomorphism and its values are
p-adic-linear maps. The pure-tensor and integral-inclusion formulas follow from
the lift. The identity and composition laws follow from its functor laws.
`rationalEndAction` is the resulting rational algebra homomorphism on actual
rational endomorphisms, using the existing equivalence between categorical and
linear endomorphisms.

`PrimeComparison.rationalToPrime_homMap` proves that actual prime extraction
commutes with these rational Hom maps. Tensor induction in the rational
homomorphism reduces the claim to the published naturality for integral
homomorphisms; rational linearity handles scalar multiples and sums.
`rationalFullToPrime_homMap` specializes to the full Tate module.

`rationalFullToPrime_surjective` is supplied first for commutative group schemes
and then for abelian schemes. It chooses the proved restricted-product comparison
and inserts the desired prime vector as the single nonzero coordinate. The
inverse comparison gives a full rational section with the required prime
coordinate. This public theorem consolidates the former private
`full_coordinate_surjective` argument from
`WeilRationalPolarizationNondegeneracyProof`, which now imports and reuses it.

`rationalHomMap_eq_id_of_extraction_fixed` combines this surjectivity and the
naturality identity. Every prime vector has a full preimage; the assumed
fixedness after extraction therefore implies that the actual prime Tate operator
is the identity.

All results are internal consequences of the imported actual constructions.
Injectivity of the rational Hom representation at one prime is a separate
geometric theorem and is not asserted here. In particular, the operator identity
does not yet identify the rational endomorphism itself.
