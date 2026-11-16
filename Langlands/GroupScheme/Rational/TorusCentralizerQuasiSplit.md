# A geometric Borel from a supplied torus centralizer

This internal construction starts with a connected reductive group `G` over an
arbitrary field `k : Type u`, a split commutative torus `A`, a homomorphism
`a : A → G`, and supplied `C : TorusCentralizerTorusData a`. The latter records
an actual closed torus representing the entire centralizer of `a` on every test
scheme. The construction proves that `G` is quasi-split. Maximality of `A` and a
chosen factorization through the centralizer are unnecessary.

`C.borelScheme hA` and `C.borelHom hA` are the affine dynamic parabolic scheme
and its inclusion for the original-field cocharacter
`C.regularCocharacter hA` composed with `C.inclusion`.
`borelHom_isRepresentedBy` gives representation of that whole dynamic parabolic.

The proof of `borelHom_isGeometricBorel` passes to `AlgebraicClosure k`.
The published finite Galois splitting theorem makes the base change of the
supplied torus split. The published self-centralizing criterion makes its
inclusion a maximal torus after this field extension.
`regularCocharacter_baseChange_isRegular` proves that the base change of the
same original-field cocharacter is regular. Dynamic parabolics commute with
base change, so `regularCocharacterBorel` proves that the base-changed inclusion
is Borel. The closed inclusion then satisfies the geometric Borel predicate by
`isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure`.
`C.isQuasiSplit` packages this actual geometric Borel with the supplied
connected reductivity.

The adapter `IsSplitTorus.isQuasiSplit_of_torusCentralizer` accepts an arbitrary
group scheme `Z`, a homomorphism `j : Z → G` representing the entire centralizer
of `a`, and a proof that `Z` is a torus. It derives the required closedness by
identifying the centralizer with that of a separating cocharacter using
`centralizingCocharacter_spec`, then applying
`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer`.
The torus property provides the commutative structure.
Connected reductivity supplies affineness and smoothness, hence the local finite
type instance, so this adapter needs no separately supplied geometry hypotheses.

All ingredients are published Library theorems. The provenance is the internal
composition of `Rational.TorusCentralizerRegularCocharacter`,
`Absolute.RegularCocharacterBorelProof`, `Absolute.GeometricBorelDescent`,
`Dynamic.RepresentedStructure`, `Torus.FiniteGaloisSplittingProof`, and
`Torus.SplitReflection`. This unit assumes neither quasi-splitness nor a Borel
existence premise. It does not construct coherent rank-one coordinates or prove
the algebraic rank-one coordinate existence statement.
