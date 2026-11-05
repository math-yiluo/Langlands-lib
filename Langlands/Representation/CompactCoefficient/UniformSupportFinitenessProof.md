# Finiteness from a common fixed-level coefficient support

This module proves the exact proposition
`Langlands.CompactCoefficientClass.UniformSupportFixedLevelFinitenessStatement`.
It is the general coefficient-space reduction used in the argument for Renard
VI.3.4, printed pp.145–146 / PDF pp.151–152, French edition dated 9 July 2026.
It assumes the published common-support predicate and proves finiteness of the
published actual compact irreducible class quotient at the specified level. It
does not prove the common-support predicate for the rational norm kernel, and
it does not complete the separate norm-kernel finiteness or category-decomposition
targets. The arbitrary left-Haar scope is a derived formulation, implemented
using the published compact-coefficient separation machinery rather than
requiring the unimodularity appearing in Renard's surrounding framework.

The group universe `uG` and representation-carrier universe `uV` are independent.
The group is an arbitrary topological group with its Borel measurable structure
and a supplied left Haar measure. The level N is an actual compact open subgroup.
No admissibility, second countability, finite dimension of representations,
unimodularity, algebraic group, characteristic or rank premise is added.

The submodule `supportedBiInvariant K C` consists of the published complex
Schwartz–Bruhat functions invariant on both sides under K and whose ordinary
function supports are contained in C. For compact C and open K, finitely many
right K-cosets cover C. The proof of
`finiteDimensional_supportedBiInvariant` obtains a finite subcover by the open
sets `{x | r⁻¹ * x ∈ K}`. Evaluation at their representatives is an injective
complex linear map into a finite product of copies of ℂ: right invariance
determines values on C and support containment forces zero outside C. This
proves finite dimension without any measure or separation axiom. The same
compact set is used for every function in this space.

`exists_separating_corner_element_supported` retains the coefficient provenance
in the published construction `exists_separating_corner_element` from
`CompactCoefficient.FixedLevelFiniteness`. It starts with an actual compact
irreducible smooth representation and a nonzero N-fixed vector v₀. An algebraic
dual functional nonzero on v₀ is averaged over N; the average is smooth and
still nonzero on v₀. Integrating its inverse coefficients against their complex
conjugates gives the published invariant Hermitian form using left invariance
of Haar measure. Its functional Λ at v₀ is invariant under N and hence is a
smooth algebraic-dual vector for the contragredient action. The test function
is the actual inverse coefficient `g ↦ Λ (ρ g⁻¹ v₀)`. It is bi-N-invariant by
the fixedness of v₀ and invariance of Λ, and it has compact support because
compactness in the published class definition tests every smooth algebraic-dual
vector. The assumed common support therefore contains this particular test
function's support.

The nonzero integral of the squared modulus makes its Haar Hecke corner action
nonzero on its own fixed-vector space. For an inequivalent compact irreducible
representation, integrated action of these inverse coefficients defines an
actual intertwining map from the first representation to the second. The
published vanishing theorem for intertwining maps between distinct classes
makes the corner action zero on the second fixed-vector space. This is the same
implemented separation route as the imported theorem, with the additional
support conclusion; all analytic lemmas, averaging and intertwining-class
comparisons are imported by Lean name.

The proof of `fixedStratum_finite_of_uniformSupport` chooses one representative
of each class in the exact published `fixedStratum`. The relation
`ofRep c.out = c` and `hasFixedVector_ofRep` identify its membership with the
actual nonzero fixed-vector condition. Select one supported separating corner
element per class. `supportedToCorner` only changes the test-function wrapper
into the existing Haar Hecke corner and is complex linear. The selected test
functions form a linearly independent family in `supportedBiInvariant N C`:
apply the corner action of one class to equality of two finite linear
combinations; every other term vanishes, and its own nonzero action forces the
two scalar coefficients to agree. Finite dimension of the one common function
space then gives a finite indexing type. `Set.finite_coe_iff` returns finiteness
of the original class set, not of a substitute class type or inertia quotient.
The final theorem `uniformSupportFixedLevelFiniteness` instantiates this result
with precisely the published generic proposition's binders.

The source's compact coefficient orthogonality is IV.3.3, printed pp.101–102 /
PDF pp.107–108, and condition (KF) is IV.1.7, printed p.95 / PDF p.101. The
finite-evaluation and separating-corner formulation above is internal derived
content implementing the finite-dimensional coefficient-space step of VI.3.4.
The substantial class-uniform compact-support bound, actual ambient-extension
and smooth-dual transport, and any use of ambient compact open subgroups in
proving that bound remain obligations of the rational norm-kernel application.
