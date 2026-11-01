# Half-twisted smooth sections for actual adelic block parabolics

Author: Worker 2. Provenance: internal construction from the published actual
adelic matrix, block parabolic, scalar twist and covariant-function APIs, extended
by the accompanying actual block determinant character and vector smooth-function
constructions. This unit makes no new identification with an original source.

The number field `F` has arbitrary universe `uF`. Every natural rank `n` and
positive ordered block shape `B` is allowed, including the empty shape in rank
zero. The groups are the actual matrix units over the number-field full, finite
and infinite adele rings; the Levi is the actual product of its diagonal matrix
blocks. No topology on the number field itself is chosen.

## Algebraic sections and finite smoothness

For an actual complex representation `σ` of the full adelic Levi on an arbitrary
complex module `V : Type uV`, `inducingRepresentation` inflates `σ` through the
actual Levi projection and twists by `parabolicHalfCharacter`. This is the
constructed positive complex square root of the block determinant character.
The direction of the half is positive. Identification of that determinant
character with an adelic Haar modulus remains a separate obligation.

`Sections` is the actual module of functions `f : AdelicGL F n → V` satisfying

`f(p * g) = leviHalfCharacter(leviProjection(p)) • σ(leviProjection(p))(f(g))`.

The implementation reuses Mathlib's `Representation.coindV`, `coind` and
`coindMap` through the existing induction API. `evaluate`, `covariance` and
`evaluate_rightAction` expose actual function evaluation, the displayed
covariance and right translation `f(x) ↦ f(x * g)`.

`inducingRepresentation_scalar` uses the actual scalar-valued parabolic
inclusion and its Levi projection to show that the positive half contributes
one on common scalars. `evaluate_scalar` gives left scalar covariance on the
actual values. Ambient scalar centrality gives `evaluate_rightAction_scalar`.
If an actual idele character `ω : Ideles F →* ℂˣ` acts on the coefficients
through the common-scalar Levi inclusion, `rightAction_scalar` proves that
it acts by the same scalar on all sections. The premise is an explicit
identity of the supplied representation; no scalar character is postulated.

`finiteSmoothSubrepresentation` requires one open subgroup of the finite adelic
matrix group to fix the entire section. Conjugation by the finite projection of
the translating full matrix proves stability under full adelic right translation.
`FiniteSmoothSections` and `finiteSmoothInduced` restrict to that subspace. The
finite-factor restriction is proved smooth; every finite slice is proved locally
constant by using the open neighborhood `b * K` at a finite matrix `b`.
`finiteSmoothSectionOf` constructs a section from actual covariance and an
explicit common open finite stabilizer.
`finiteSmoothInduced_scalar` inherits the proved scalar-character law on this
actual subspace.

A Levi intertwiner induces `inducingMap`, `sectionMap` and
`finiteSmoothInducedMap` by actual coefficient postcomposition. It preserves the
same finite stabilizer. Evaluation, identity and composition laws are proved.
The source and target module universes `uV`, `uW`, `uX` are independent.

## Normed coefficients and full smooth sections

For the remaining constructions the coefficient modules are complex normed
spaces; completeness and continuity of the supplied Levi representations are not
assumed. `infiniteSlice` evaluates a section at `(a,b)` with the finite matrix
`b` fixed. `infiniteSmoothSubrepresentation` requires every such slice to be real
smooth in the actual mixed real/complex matrix coordinates. Full right
translation preserves this: its infinite projection acts by smooth right
translation on a slice, and its finite projection changes the slice parameter.

`smoothSubrepresentation` intersects that subspace with the common finite
stabilizer subspace. `SmoothSections` is its actual function carrier and
`smoothInduced` its full adelic right action. `smoothInclusion` is a faithful
intertwiner into the original covariant functions; evaluation is still actual
right translation. The finite-factor restriction is proved smooth.
`smoothSectionOf` accepts explicit covariance, a common open finite stabilizer
and real smoothness of every infinite slice.
`smoothInduced_scalar` likewise inherits the same proved scalar-character
law on the full smooth subspace.

`smoothSection_continuous` proves that every smooth section is continuous in the
original full adelic matrix topology. At a matrix `x`, take the open neighborhood
where `finite(x)⁻¹ * finite(y)` belongs to the common stabilizer `K`. On this
neighborhood, right invariance identifies the section at `y` with its fixed
finite slice at `finite(x)`, evaluated at `infinite(y)`. The latter is continuous
by real smoothness of the infinite slice and continuity of the infinite
projection. Neighborhood equality therefore gives continuity at every `x`.
`smoothToContinuousMap` is the resulting injective complex linear realization
in actual continuous vector valued functions. No topology on the smooth
section space itself is assigned.

For a Levi intertwiner `T` with `Continuous T`, `smoothInducedMap` is actual
coefficient postcomposition preserving both regularity conditions. The
continuous complex linear map is real smooth, so it preserves infinite slice
smoothness; the same finite stabilizer still works. Evaluation, identity and
composition laws are proved. General algebraic intertwiners above do not need
this continuity premise.

## Scope

These constructions use the actual covariant function subspaces and prove their
intrinsic regularity, representation and map laws. They supply no whole-group
open stabilizer condition, smooth function-space topology, completed or unitary
induction, Haar-modulus identification, nonzero section existence, local tensor
decomposition, admissibility, irreducibility, isobaric classification or
automorphic existence theorem. Those are separate construction or theorem
obligations. In particular, the term half-twisted does not assert an unproved
identification with normalized induction defined through Haar scaling.
