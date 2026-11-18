# Smooth Hilbert realizations and inverse-transpose pairings

Worker 322. This is derived interface vocabulary for actual `GL_n(ℝ)` and
`GL_n(ℂ)`. It uses the published `GKModule`, `SmoothVectors`, `SmoothDerivative`,
`SmoothDerivativeTopology`, `TransposePairing`, and `GeneralLinear.inverseTranspose`
constructions. It proves no globalization, character theorem, category comparison,
or pairing existence. The companion proposition definitions request those analytic
consequences. All names below lie in `Langlands.Archimedean`.

## Actual action and compact-finite vectors

For a real smooth Lie group and a homomorphism `R` into bounded complex linear
operators, `DerivativeSmoothVectors.representation` is the conjugate of
`smoothRepresentation` by `DerivativeSmoothVectors.toSmooth`. In formulas, with
`e = toSmooth`, it is `y ↦ e⁻¹(smoothRepresentation(g)(e(y)))`.
`toSmooth_representation` records this equality. This transports the existing
action rather than choosing a new group action or a topology. No continuity of
the transported action is claimed by this definition.

The subsequent definitions use `F : Type` with `RCLike F`, a size `n`, and a
complex inner product space `H`. The real and complex statement families specialize
`F` to the actual fields, and require `CompleteSpace H`. The model is
`matrixModel F n`, the underlying real matrix space even when `F = ℂ`.
`smoothHilbertCompactRepresentation` restricts the transported action along
`Unitary.toUnits` from `Matrix.unitaryGroup (Fin n) F` into actual `GL_n(F)`.
`smoothHilbertKFinite` is the submodule of its finite vectors as defined by
`FiniteVectors.subrepresentation`: the complex span of each vector's actual
compact orbit is finite-dimensional. This is not a supplied finite-dimensional
ambient model.

Given `e : V ≃ₗ[ℂ] smoothHilbertKFinite F n R`,
`smoothHilbertGlobalizationMap` is the composite of `e` and that submodule's
inclusion. It is complex linear and injective because both factors are. Surjectivity
of `e` identifies `V` with all compact-finite vectors of this smooth carrier.
There is no topology on the algebraic `V`.

## The two topologies and genuine derivatives

The norm topology on `H` supplies the bounded operators, joint action continuity,
closed invariant subspaces, and compact admissibility. The dedicated smooth carrier
`D = DerivativeSmoothVectors (matrixModel F n) R` has its published topology induced
by the injective map

`y ↦ (W ↦ iteratedLieDerivative (matrixModel F n) R W (toSmooth y))`.

Here `W` ranges over every finite word of real matrix directions, including the
empty word. Thus convergence is convergence in the Hilbert norm of every genuine
word derivative. This is the topology of the published word seminorms, not the
inherited norm topology on `smoothVectors`. The topology, the continuous coordinate
maps `derivativeCLM`, and the continuous genuine operators `operatorCLM` are already
constructed in `SmoothDerivativeTopology`.

`generalLinearRealExp F n X t` is the actual invertible matrix `exp(t • X)`,
with inverse `exp(-(t • X))`. The matrix exponential identities prove the two
inverse laws; `generalLinearRealExp_val` exposes its matrix. The curve parameter is
real for both fields.

`HasSmoothHilbertExponentialDerivatives F n R` is the explicit scalar property

`(d/dt)|₀ L(R∞(exp(t X)) y) = L(dR(X)y)`

for every real matrix direction `X`, every `y : D`, and every continuous complex
linear functional `L : D →L[ℂ] ℂ`. Its right side uses the published genuine
`DerivativeSmoothVectors.operator`, not a chosen algebraic derivative.
It is a condition in the globalization conclusion, not an extra hypothesis on
representations in the smooth pairing statement, and not a theorem asserted here.
It deliberately tests all functionals continuous for the stronger smooth topology,
including those that do not extend continuously to the Hilbert norm topology.

For its future analytic proof, the word coordinate of `dR(X)y` is the coordinate
of `y` indexed by `W ++ [X]`, by `derivativeCoordinates_operator`. The needed
vector derivative can therefore be checked coordinatewise: the difference
quotients of the `W` coordinate of `R∞(exp(tX))y` must converge in `H` to the
`W ++ [X]` coordinate of `y`. Continuity of `L` then gives the displayed scalar
derivative. The published finite-word continuity equivalence alternatively
expresses every such `L` by a bound involving finitely many genuine word norms.
These observations supply concrete derivative data; the exponential orbit
comparison itself is still to be proved.

## Globalization and pairing predicates

`IsIrreducibleAdmissibleHilbertRepresentation F n R` requires exactly the existing
`IsContinuousRepresentation R`, `IsTopologicallyIrreducible R`, and
`IsAdmissible R (unitaryCompact F n)`. This reusable helper and the other
predicates in this module accept a possibly incomplete complex inner product
space: their elaborated types do not require `CompleteSpace H`.
The real and complex globalization statements supply an explicit existential
`CompleteSpace H` witness, and the smooth pairing statements quantify with an
explicit `[CompleteSpace H]` binder. Those statement boundaries therefore concern
complete complex Hilbert spaces. Joint continuity concerns `GL_n(F) × H → H`.
Irreducibility includes nontriviality of `H` and excludes proper nonzero closed
invariant complex subspaces. Admissibility means finite-dimensional intertwiner
spaces from every continuous finite-dimensional compact representation.
No preservation of the inner product is required.

`IsSmoothHilbertGlobalization F n R ρ π e` requires that representation predicate,
density of `smoothHilbertGlobalizationMap e` in `D`, and the two explicit identities

`j(ρ(k)v) = R∞(Unitary.toUnits k)(j(v))`,

`j(π(1 ⊗ X)v) = dR(X)(j(v))`.

The direction `X` is any matrix over `F` regarded as a real direction. Complex
linearity then controls the whole complexified real Lie algebra. The predicate
also requires `HasSmoothHilbertExponentialDerivatives`. Substituting `j(v)` and
using the second identity gives, for every continuous smooth functional `L`,

`(d/dt)|₀ L(R∞(exp(tX))j(v)) = L(j(π(1 ⊗ X)v))`.

This is the scalar comparison used by dense restriction of an ambient pairing.
The density is in the genuine word topology, as needed to detect a nonzero
separately continuous form after restriction.

`IsSmoothHilbertTransposePairing` requires a complex bilinear form on `D`,
continuous in either variable with the other fixed, and satisfying

`B(R∞(g)y, R∞(inverseTranspose(g))x) = B(y,x)`.

The second group element is the published ordinary inverse transpose, including
over `ℂ`; it is not conjugate transpose. `HasNonzeroSmoothHilbertTransposePairing`
adds existence of such a form with `B ≠ 0`. The form is a conclusion to request,
not data in the Hilbert representation predicate. No algebraic dual replaces the
smooth topology or its continuous functionals.

## Sources, derivation and remaining comparisons

The registered original sources are:

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), source
  `getz-hahn-2024-automorphic-representations`, SHA256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Section 4.4, printed pp.115–120 (PDF pp.130–135), especially Proposition 4.4.7,
  Theorem 4.4.9, Definitions 4.4.11–12, Lemma 4.4.13, Theorem 4.4.14 and the
  following globalization discussion. The compact orbit-span characterization is
  Lemma 4.4.8. Proposition 4.4.7 and its proof give density of smooth compact-finite
  vectors, with printed p.118 explicitly treating density in the smooth topology.
- Getz–Hahn, October 2026 errata, source `getz-hahn-2024-errata-2026-10`, SHA256
  `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`, p.1,
  both Section 4.4 corrections: continuity on compact finite-dimensional pieces,
  and compact-finite vectors in the p.120 comparison. Our identification is with
  compact-finite vectors inside the smooth carrier, not with all smooth vectors.
- Aizenbud–Gourevitch, *Generalized Harish-Chandra descent and applications to
  Gelfand pairs*, arXiv v7 (2009), source
  `aizenbud-gourevitch-2009-generalized-harish-chandra-descent-v7`, SHA256
  `a789936fffe560b9295c666f420a3cf7c69a475192bace2e5c2c4c3d975d7dfd`.
  Definition 8.1.1, p.22, uses admissible smooth Fréchet representations at
  archimedean places. Theorem 8.2.1, p.23, identifies the smooth contragredient
  with the inverse anti-automorphism twist. Corollary 7.6.3, p.22, provides
  transpose invariance for `GL_n`. Its character-rigidity argument and the
  alternative regularity argument in Remark 8.2.2 are substantial proof inputs.

These are derived Hilbert/smooth-vector interfaces, not verbatim source statements.
For the following category comparisons, completeness of `H` must be supplied
separately, as it is at both companion statement boundaries.

## Passage to the smooth Fréchet and moderate-growth categories

The intended application of Aizenbud–Gourevitch is to the usual smooth
representation `H∞` of a complete Hilbert representation. Its topology is
generated by the Hilbert norms of all iterated genuine derivatives. The
dedicated carrier `D` already has a topology generated by precisely the
published word derivatives, but the analytic identification with that standard
smooth Fréchet realization remains to be proved. The comparison has the
following specific obligations.

1. The real matrix Lie algebra has a finite basis: real matrix units for
   `F = ℝ`, and matrix units together with their multiples by `i` for `F = ℂ`.
   Words in this finite basis form a countable set. Multilinearity of genuine
   iterated differentiation must show that their word seminorms generate the
   same topology as all words of arbitrary real matrix directions. In
   particular, each arbitrary-word seminorm is bounded by a finite combination
   of basis-word seminorms. The converse inclusion uses that basis words are
   among all words. This supplies countable seminorm generation and
   metrizability, not completeness by itself.
2. The standard theorem on smooth vectors of a complete Hilbert representation
   must identify the carrier and topology above with a complete smooth-vector
   space. Equivalently, one needs a closedness or derivative-limit argument for
   compatible word coordinates, not merely completeness of the ambient
   product `List 𝔤 → H`: a subspace of that product need not be complete.
   Combined with the countable-seminorm comparison and the already published
   Hausdorff locally convex structure, this yields a Fréchet space. These
   completeness and topology identifications are analytic obligations.
3. The transported action must be jointly continuous on `GL_n(F) × D`, and
   its orbit maps must be smooth as maps into that Fréchet topology. Smoothness
   of the underlying `H`-valued orbits alone is not this assertion. Word
   derivative and adjoint-action formulas supply the standard comparison.
   Getz–Hahn printed p.119, following Definition 4.4.11, describes the smooth
   Hilbert construction. No Fréchet-valued smoothness or continuity theorem
   is established by the algebraic transport definition here.
4. One must compare compact-finite vectors in `H` and `D`, using admissibility
   and Proposition 4.4.7, and transfer compact admissibility and irreducibility
   to the smooth realization. Finite-dimensional compact intertwiner images,
   their smoothness and their compatible topologies must be justified.
   Theorem 4.4.9 relates admissible Hilbert irreducibility to the underlying
   GK module; passage back to the smooth representation also uses the
   compact-finite/globalization comparison. Hilbert topological
   irreducibility alone is not a definition of irreducibility in `D`.
5. Lemma 4.4.13 supplies the moderate-growth theorem for Hilbert smooth
   vectors. To use it with this `D`, one must transport the source's topology
   and its estimates: for every continuous seminorm `p`, there are a
   continuous seminorm `q` and an exponent `d` with
   `p(R∞(g)y) ≤ height(g)^d q(y)`, with the group height from
   Getz–Hahn (4.17). Theorem 4.4.14 and the corrected globalization
   discussion on p.120 then compare this smooth realization with the
   canonical moderate-growth globalization of its compact-finite module.
   Hilbert realization of an arbitrary abstract module, the relevant
   existence and uniqueness comparisons, and the compact/derivative/density
   compatibilities in `IsSmoothHilbertGlobalization` remain obligations.
6. With the smooth, admissible, irreducible Fréchet realization and these
   comparisons available, Definition 8.1.1 of Aizenbud–Gourevitch places it
   in the category of Theorem 8.2.1. Its smooth contragredient must be
   identified with the appropriate smooth part of the continuous dual.
   One must transport the theorem's continuous equivariant isomorphism and
   the separately continuous evaluation pairing to this exact `D`.
   An algebraic dual alone supplies neither this topology nor continuity.

These steps explain the route into the source category. The module supplies
their concrete carriers, actions and derivative data, and asserts none of
these analytic comparison results as a theorem or as a consequence of naming
a predicate.

After these comparisons and Theorem 8.2.1, a continuous equivariant isomorphism
`T : D^θ → D^vee`, where `θ(g) = transpose(g⁻¹)`, yields
`B(y,x) = (T x)(y)`. Evaluation is complex bilinear, separately continuous and
nonzero; contragredient equivariance gives the exact displayed invariance.
Globalizing an abstract module additionally needs Hilbert realization of every
irreducible admissible module satisfying the existing GK hypotheses and the
explicit compact, derivative and density comparisons above. None of these
analytic results is made true by a definition here. No global multiplicity-one
or Rankin–Selberg input is used.
