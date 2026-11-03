# Actual point comparisons from root-span Coxeter reflections

This internal construction works over every field for the actual maximal split
torus of a connected reductive group. It uses the representative-preserving
equivalence between the actual scheme normalizer/full-centralizer quotient and
the actual point-image quotient, with the same literal simple-character labels.

`pointCoxeterSystem_rootLengthComparison_of_rootLength` transports the scheme
root-sign length criterion to the actual point Coxeter system by preservation of
length and compatibility of the character action with `weylEquiv`.

`pointCoxeterSystem_simplePairing_of_reflections` starts with actual root-span
simple reflections. The whole-character reflection pairing theorem applies to
every character and every cocharacter annihilating the corresponding root.
The same quotient-action comparison gives `SimpleReflectionPairingInvariance`
for the transported point system.

`exists_rootSpanPointCoxeterSystem` constructs a finite Coxeter system from the
given `HasRelativeRootSystem` witness and generic cocharacter. It transports the
length and pairing laws just described, then applies Worker 165's
`actualLeviWeylIdentification_of_simplePairing`. Thus the image of the actual
Levi Weyl inclusion equals the standard Coxeter subgroup for every finite face,
including the empty and full face. Finite labels and finite point Weyl group
are conclusions, with no positive-rank or reduced-root assumption.

`RootSpanPointCoxeterData` packages this matrix, actual point system, finiteness,
and the three proved comparisons. `rootSpanPointCoxeterData` chooses one such
package from the existence theorem. Its fields keep every proof attached to the
same system and the same literal simple-character labels.

The proof derives its conclusions from the actual root-span Coxeter
construction, whole-character pairing invariance, and the actual quotient and
descent adapters. No stronger full-character Coxeter realization is assumed.
This unit does not establish positive simple-reflection conjugacy, identify an
arbitrary supplied Coxeter system, or prove any geometric expansion or final
Aubert compatibility equation.
