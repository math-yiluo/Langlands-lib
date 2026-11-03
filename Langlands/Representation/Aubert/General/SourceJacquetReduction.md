# Actual source Jacquet decomposition, preservation and K0 reduction

This internal unit continues `SourceJacquetComparison`. It transports supplied
structural subgroup identities and existing restricted-standard preservation
to the actual geometric source. It does not prove the structural identities
or the final rational-point Aubert induction-compatibility statement.

`geometricSourceDecompositionOfEq` takes a standard restricted semidirect
decomposition inside `M J`, an equality of the source parabolic restricted to
`M J`, an equality of the ambient source Levi with `M K`, and an equality of
the restricted source radical. Rewriting those three groups proves the actual
`GeometricSourceDecomposition`. In particular the source decomposition is no
longer a separate assumption once those identities and the standard
decomposition are supplied. This elementary part needs only a group.

The remaining results work in any locally compact nonarchimedean group with
closed ambient Levis and radicals, at independent index, group and carrier
universes `uI`, `uG`, `uV`. The finite labels `I,J,K` and the element `n` are
arbitrary; no finite label-type, normalizer, minimality or nonemptiness
assumption is used. They retain the source decomposition, the standard
restricted decomposition, `M K ≤ M J`, and the exact ambient Levi and restricted
radical identities as visible inputs. The latter inputs are those of
`geometricSourceJacquetComparisonIso`.

`geometricSourceJacquetPreservationOfEq` assumes finite-length and short-exact
preservation only for the literal normalized `jacquetFunctor` inside `M J`
with the standard restricted decomposition at `K`. The closedness witness is
the inverse image of the ambient radical closedness. The supplied standard
preservation composes with the published continuous equivalence from the
restricted Levi to the ambient `M K`. The natural comparison then transfers
both properties to the actual source functor followed by identity transport
of its Levi. Finite length of the actual source itself follows by reflection
along the surjective continuous group equivalence, using the published
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`. Short exactness
reflects directly because smooth pullback preserves the underlying linear
maps. No additional preservation assertion for the actual source is assumed.

`geometricSourceJacquetK0` defines the actual source Jacquet map on the full
exact finite-length Grothendieck group using these derived preservation
witnesses. Its codomain is the Grothendieck group of the actual intersection
Levi, before any change of acting group.

`geometricSourceJacquetK0OfEq` identifies the full integer-linear maps on the actual exact finite-length
Grothendieck groups. The left side is the map of the actual source Jacquet
functor followed by `conjugationK0` at the identity, identifying its actual
intersection Levi with `M K`. The right side is the K0 map of the literal
standard restricted Jacquet functor followed by the actual subgroupOf
continuous-equivalence pullback. The proof applies `map_eq_of_iso` to the
natural comparison and `map_comp` to both composites. It therefore holds on
every virtual class, not just classes of a selected family of objects. The
carrier universe is unsaturated `uV`; specializing it to `max uG uV` gives the
universe used by the geometric-term assembly.

The provenance is internal and uses only the published definitions and the
named comparison and transport lemmas above. The standard restricted
preservation premises can be extracted from the literal Levi-family
`ParabolicFiniteLength` assumptions already present in the final target. The
structural subgroup identities, scheme-to-point index transport, target
intersection induction comparison, normalized stages, Weyl conjugacy and
geometric expansion still require their own proofs. No new premise is added
to the final compatibility proposition and no classification or external
literature theorem is invoked.
