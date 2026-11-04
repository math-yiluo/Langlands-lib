# Strict Jacquet square integrability from one joint geometric witness

Author: Worker 19. The actual chamber-cover and quotient-volume proofs used here
are by Worker 349, credited in their own paired files.

`rationalStrictJacquetSquareIntegrabilityReduction` proves the complete
`RationalStrictJacquetSquareIntegrabilityReductionStatement.{u,v}` with independent
field and representation universes and no additional outer parameters. Its
premise is `JointSpecialCompactBasisExistenceStatement.{u}`. Its conclusion is the
unmodified original strict normalized Jacquet square-integrability criterion.
This intermediate theorem does not prove the geometric existence premise.

Apply that premise to the actual group, torus and generic cocharacter supplied
by the criterion. It gives one apartment datum, one special point and its
subgroup `K0`, along with a represented torus centralizer, the compatible
standard-Levi Cartan comparisons and the simultaneous standard compact-open
basis, all attached to the same point. The compact and open clauses of
`SpecialCompactProperties` make this same `K0` an open subgroup with compact
underlying set; no refinement of the Cartan subgroup is needed.

`exists_isFiniteLatticeTransversal` extracts a finite centralizer lattice
transversal from those same Levi comparisons. Then
`rationalFiniteChamberCartanCover` supplies one integral cocharacter generator
for each actual `SimpleRoot`, a finite middle translating set, and a cover by
`K0` double cosets times the full actual group center. A generator pairs
positively with its own simple root and vanishes on the others. Root finiteness
comes from `IsSplitTorus.finite_simpleRelativeRoots` for the specified maximal
split torus and the smooth connected-reductive group.

Index the ray family by `SimpleRoot i ν` and attach to a root `a` the face
`Finset.univ.erase a`. The covering generators therefore vanish on their faces
and pair strictly positively with every root outside their faces; the root `a`
itself is the required outside witness. Apply
`rationalCompactTranslateCoefficientBound` to the original admissible
representation and strict normalized Jacquet exponent hypothesis, using the
supplied simultaneous basis. It chooses actual full-center Levi points equal
to these literal uniformizer powers, and then gives uniform coefficient bounds
on `K0`, the finite middle set and `K0`.

Define each volume weight to be the reciprocal real value of
`HaarModulus.closedRestrictCharacter` for the corresponding actual standard
unipotent radical, evaluated at that same chosen central Levi point. These
weights are nonnegative. Apply `rationalLatticeQuotientVolume` with precisely the
same faces, generators, points, subgroup and finite middle set. It proves an
upper measure bound in the quotient by the full actual group center, with a
positive constant uniform over all lattice indices and middle elements. The
weight in every coordinate is definitionally the weight in the strict squared
coefficient bound; no comparison between different radicals is used.

Finally apply `Langlands.cartanLatticeL2`. Its lattice map is the actual
uniformizer power of the natural linear combination of the covering generators.
Use the genuine unitary central character supplied by the original criterion,
the supplied Borel Haar measure, the actual covering identity, and the preceding
coefficient and volume bounds. Weakening the positive constants and radii to
nonnegative ones gives exactly that theorem's premises. Its conclusion is
`IsSquareIntegrableModCenter` for the original representation and measure.

The empty-root case uses this same proof. The ray type is empty, the outside-root
witness condition is vacuous, the lattice has one tuple, and all coordinate
products are one. The geometric cover and volume theorem still apply. The
separate compactness conclusion included in the covering theorem is not needed.
There is no splitness, quasisplitness, characteristic-zero, finite-length or
irreducibility restriction added to the original criterion.

This is an internal composition of the named actual geometric and analytic
results. The coefficient chain is
`rationalCompactTranslateCoefficientBound`, `rationalLatticeCoefficientDecay`,
`haarNormalizedLatticeCoefficientBound`,
`normalizedJacquetCompressionSpectrum` and
`compressedLatticeCoefficientBound`. It uses admissibility on finite fixed-vector
spaces, the actual Jacquet power-kernel/compression formulas and the actual
normalized central exponents, rather than a global spectral decomposition. Its
linear-algebra inputs include the generic
`StrictCartanBound.exists_eigenvalue_bound_lt` and
`StrictCartanBound.dual_apply_eq_compressedAction`, whose full scope is not
restricted to the GL theorem housed in that module. The volume chain uses
`standardBasisMember_rayIndex` and `latticeCentralQuotientVolume`, which derive
their estimates from the displayed common basis. The integration chain is
`cartanLatticeL2` followed by `finiteLatticeCellL2`, together with regularity of
the genuine descended coefficient norm. These actual declarations introduce no
classification, geometric-lemma, adjointness, character-independence or
cuspidal-support premise. Constructing the joint geometric witness remains a
separate obligation before this implication can yield the unconditional
criterion.
