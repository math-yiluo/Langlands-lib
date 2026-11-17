# Base change of all-test centralizers and represented preimages

This internal module is derived from the Library's definitions of subgroup
functors, all-test centralizers, base-change point equivalences and represented
subgroup functors. It does not transcribe an additional literature statement.

For any subgroup functor `F` of any group scheme and any base morphism `b`,
`centralizer_baseChange` identifies the base change of its all-test centralizer
with the all-test centralizer of its base change. No flatness or representability
is required. `centralizerBaseChangeEquiv` is the resulting multiplicative
equivalence of points, on every test scheme over the new base.

The forward inclusion transports commutation through the base-change point
equivalence. For the reverse inclusion, a refinement of the test scheme over
the original base inherits a morphism to the new base from the parameter
scheme. Regarding it as a test scheme over that base lets us apply the assumed
centralization; the point equivalence then transports the equality back.

The existing `SubgroupFunctor.comap_baseChange` from
`Derived.CentralIntersectionReduction` similarly transports preimages through the naturality of
the point equivalence. `IsRepresentedBy.comap_of_comp` says that if `n` represents
`E`, `c` represents `F`, and `f ≫ n = c`, then `f` represents `F.comap n`.
Monicity of `c` gives monicity of `f`; monicity of `n` identifies the factorizing
points in the two directions. This abstracts the argument previously used for
the relative-torus centralizer inclusion in `Torus.CentralizerOpenInNormalizer`.
