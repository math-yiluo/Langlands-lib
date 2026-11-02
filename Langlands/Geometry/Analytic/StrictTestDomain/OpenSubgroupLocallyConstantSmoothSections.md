# Full smooth local sections on the finite rational transport site

Author: Worker 13.

This internal construction proves smoothness of the entire locally constant
section module of the actual sheaf on
`OpenSubgroupTransport.finiteTopology`. It constructs the full category of
module sheaves with smooth sections at every original test, its finite limits,
and smooth restriction intertwiners along every original labelled arrow. The
entry declaration is
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport.locallyConstantSmoothSheafFunctor`.

The base is a complete ultrametric normed field `K` with a presented strict
affinoid algebra `P`, and `ρ : RationalSpectralAction G P` is an action of an
actual topological group. Each object `X` retains its original open subgroup,
invariant rational presentation and rational locus with its spectrum subspace
topology. A commutative ring `R` supplies the coefficients. The field, group,
coefficient ring and coefficient carrier universes `u`, `v`, `r`, `w` are
independent. Coefficient modules carry no topology and need not be finite,
admissible or nonzero.

## The original point and section actions

`locusMulAction X` restricts the original point action to the invariant locus:

```text
k • x = ρ.toMonoidHom(k) • x.
```

Its subtype membership follows from the original locus invariance, and its
action laws follow from the ambient group action. This named action is a local
instance in the file; consumers can enable it explicitly.
`locusContinuousSMul X` proves joint continuity by restricting
`continuous_globalSpectrumAction` to the actual subgroup and locus subspaces.
The existing `locusCompactSpace` gives compactness of each full locus, including
the empty locus.

`locallyConstantSectionRepresentation_apply` computes the action obtained by
evaluating the original module sheaf, using the inverse-labelled transport
operator:

```text
(k • s)(x) = M.ρ(k)(s(k⁻¹ • x)).
```

`locallyConstantSectionRepresentation_eq_diagonal` proves equality with
`CompactAction.LocallyConstantModule.diagonalRepresentation` on all of
`LocallyConstant X.domain.obj.locus M`. The coefficient action is the original
ambient representation restricted along `SubgroupClass.subtype X.subgroup`.

For ambient smooth coefficients,
`locallyConstantSectionRepresentation_isSmooth` applies continuous pullback
of coefficient smoothness and the published compact diagonal smoothness
theorem. That theorem uses the open spatial stabilizer of a locally constant
function and the open coefficient stabilizers of its finitely many values.
Their finite intersection fixes the complete section. This proves
smoothness of every original section without replacing the section module
by a smooth submodule.

## Actual sheaves with smooth local sections

`locallySmoothProperty F` requires that the actual section representation of
`F` be smooth at every original `OpenSubgroupTransport` object.
`LocallySmoothModuleSheaf` is its full subcategory of actual Mathlib module
sheaves, and `locallySmoothInclusion` keeps the underlying sheaf and every
original sheaf morphism.

This property is closed under subobjects: finite-limit-preserving section
evaluation sends a sheaf monomorphism to an injective representation
intertwiner, and smoothness transfers through that injection. The property
is therefore invariant under sheaf isomorphisms.

The property is also closed under finite limits. At each test, lift a finite
diagram of qualifying sheaves to smooth representations. The inclusion of
smooth representations preserves finite limits, using the existing
`smoothRepToRep_preservesHomology` instance. Ordinary section evaluation
preserves those limits as well. Uniqueness of limits identifies the evaluated
limit with the underlying smooth-representation limit and transfers its
smoothness. Thus the full subcategory has finite limits, and its inclusion
preserves them.

`smoothSectionRepresentation X` evaluates a qualifying sheaf as a smooth
representation of its own actual subgroup, retaining the complete section
module. The identity `smoothSectionRepresentationForgetIso` recovers the
original algebraic section representation. This evaluation is additive and
preserves finite limits; the latter assertion follows by forgetting to
algebraic representations and reflecting the resulting limit.

## Every original labelled restriction

For `f : X ⟶ Y`, `smoothConjugationRestriction f` restricts a smooth
`Y.subgroup` representation along the original continuous homomorphism
`f.groupHom`, which sends `k` to `f.label * k * f.label⁻¹`. Smoothness is
proved by continuous pullback.

`smoothRepresentationRestriction f` is a natural transformation from
smooth evaluation at `Y`, followed by this conjugation restriction, to
smooth evaluation at `X`. Its underlying linear map is exactly
`(F.obj.obj.map f.op).hom`. Naturality is the naturality of the original
algebraic restriction transformation. The identity and composition lemmas
retain the underlying linear equalities, with composite restriction equal
to restriction along `f` composed after restriction along `g`. They do not
assert strict equality of the group-change functors.

`locallyConstantSmoothSheafFunctor` lifts the constructed full locally
constant sheaf functor from ambient smooth representations to this actual
locally smooth category. `locallyConstantSmoothSheafForgetIso` forgets
the proved local smoothness and recovers the same module sheaf functor.
`locallyConstantSmoothSections X` composes this with smooth evaluation.
The action formula above holds for its full section module, and every
coefficient intertwiner acts by pointwise postcomposition.

`locallyConstantSmoothRestriction f` is natural in ambient smooth
coefficients and has the original formula

```text
(f* s)(x) = M.representation(f.label⁻¹)(s(f.locusMap x)).
```

These section modules have carrier universe `max u w`, independently of
the group and ring universes. The definitions also retain empty loci,
distinct labels acting identically, and distinct rational presentations
with the same locus.

## Provenance and retained obligations

This is internal derived mathematics from the actual rational transport
category and finite covering topology, the full locally constant module
sheaf, its algebraic section representations, the proved global spectrum
continuity, compact diagonal smoothness and continuous pullback of smooth
representations. Finite-limit closure follows the existing full-subcategory
and representation-limit interfaces in the pinned Mathlib and project
Library. No new original-literature claim or assumed smoothness of the
constructed locally constant sheaf enters the argument.

The general locally smooth category imposes its displayed condition on
actual sheaves; the coefficient functor supplies a constructed family of
objects satisfying it. This unit does not identify the rational transport
site with a full analytic or etale site, or construct structure-sheaf
descent, compact-support or derived cohomology, arithmetic coefficient
systems, or the Harris specialization. These remain obligations of the
broader task. No arbitrary-limit or colimit preservation claim is made
for the locally smooth inclusion or its evaluation functors.
