# The horizontal differential on actual automorphic operator quotients

This internal construction restricts the existing actual coefficient Lie
differential to the horizontal full-compact-equivariant reduced cochains
with coefficients in the quotient carrier `Q.Space` of an actual
`Q : OperatorSubquotient F n`. It is the quotient analogue of the published
numerator modules `HorizontalDifferential`, `HorizontalFiniteAction`,
`HorizontalDifferentialFinite`, `HorizontalTransportCore` and
`HorizontalEquivalence`, and it relates the two by the canonical projection.

Throughout, `F : Type uF` is a number field, `n` is any natural rank and
coefficients are complex. Write `K = standardInfiniteCompact F n`, including
every component, `𝔯 = ReducedComplexLieAlgebra F n`, and
`H q = horizontalEquivariantSubmodule F n Q.compactRepresentation q` for the
published submodule of alternating maps `𝔯 [⋀^Fin q]→ₗ[ℂ] Q.Space` that
vanish whenever an argument lies in `compactInReducedSubmodule F n` and are
equivariant for the full group `K` (acting on `𝔯` by
`reducedCompactRepresentation F n`). The carrier, the projection
`Q.projection`, the finite representation `Q.finiteRepresentation` and the
quotient compact representation `Q.compactRepresentation` are the published
ones of `OperatorSubquotient` and `OperatorSubquotientArchimedean`. The
complex and compact Lie actions `Q.complexLieAction` and
`Q.compactLieAction` are those of the companion module
`OperatorSubquotientLieAction`. No hypothesis is imposed on `Q`.

## The reduced Lie action

`reducedLieAction` is the restriction of `Q.complexLieAction` along
`reducedComplexInclusion F n`; it is defined in every rank. The instances
`quotientReducedLieRingModule` and `quotientReducedLieModule` pull back the
quotient complex Lie module along the same inclusion, and `reduced_lie_eq`
identifies the bracket with `reducedLieAction`. On representatives,
`reducedLieAction_projection` states

```text
Q.reducedLieAction X (Q.projection f) = Q.projection (Q.upper.reducedLieAction X f),
```

where `Q.upper.reducedLieAction` is the published numerator action, so
`projectionReducedLieHom` is the canonical projection as a map of reduced
Lie modules. `reducedLieAction_compact` proves that restricting further
through `compactToReducedComplex F n` gives `Q.compactLieAction`, using the
published `reducedComplexInclusion_compact`.
`finiteRepresentation_reducedLieAction` proves that the reduced action
commutes with every finite adelic translation, and
`compactRepresentation_reducedLieAction` proves full compact covariance

```text
Q.compactRepresentation k (Q.reducedLieAction X f)
  = Q.reducedLieAction (reducedCompactRepresentation F n k X)
      (Q.compactRepresentation k f),
```

from the quotient complex-action covariance of `OperatorSubquotientLieAction`
and the published equivariance `reducedComplexInclusion_conjugation` of the
reduced inclusion.

## The horizontal differential

The remaining constructions of this section require `[NeZero n]`, as does
the reduced compact differentiation they use.

`horizontalCochain_infinitesimal q f hf` proves, for `f ∈ H q`, every
`Y ∈ compactInReducedSubmodule F n` and every tuple `X : Fin q → 𝔯`,

```text
⁅Y, f X⁆ = ∑ i, f (Function.update X i ⁅Y, X i⁆).
```

It takes a preimage `Z` of `Y` under `compactToReducedComplex F n`,
identifies the reduced coefficient action of `Y` with `Q.compactLieAction Z`
by `reducedLieAction_compact`, and applies the quotient theorem
`OperatorSubquotient.reducedCochain_compact_complex` of
`OperatorSubquotientCompactDifferentiation` to the full compact
equivariance of `f`. The insertion identity is therefore a proved
consequence, including in degree zero, where the sum is empty.

`horizontalDifferential q : H q →ₗ[ℂ] H (q + 1)` instantiates the generic
`Langlands.Cohomology.Lie.horizontalEquivariantDifferential` with the
actual compact image, the actual reduced compact action (which preserves
brackets by `reducedComplexLieConjugation`), the quotient compact
representation, the covariance above and the preceding insertion identity.
`horizontalDifferential_val` and `horizontalDifferential_apply` state that
its value is exactly the generic coefficient differential
`Langlands.Cohomology.Lie.differential q f.val` for the quotient reduced Lie
module.

## Finite adelic translation

`finiteCompactIntertwiner d` is the quotient finite translation
`Q.finiteRepresentation d` viewed as an intertwiner of the quotient compact
representation with itself, using the published commutation
`finiteRepresentation_compactRepresentation`; `finiteReducedLieHom d` is the
same map as a reduced Lie module homomorphism. In every rank,
`horizontalFiniteRepresentation q` is the representation of
`FiniteAdelicGL F n` on `H q` by postcomposition with these intertwiners
through the published `horizontalMapCoefficients`;
`horizontalFiniteRepresentation_apply` gives its value
`Q.finiteRepresentation d (f.val X)`.

With `[NeZero n]`, `horizontalDifferential_finite` proves that the
differential commutes with every finite translation, using the published
naturality `Langlands.Cohomology.Lie.map_differential` for
`finiteReducedLieHom d`. Hence `horizontalDifferentialIntertwiner q` is a
finite adelic intertwiner from degree `q` to degree `q + 1` whose
underlying linear map is `horizontalDifferential q`.

## The canonical projection

`horizontalProjection q` is the finite adelic intertwiner from the
published numerator `Q.upper.horizontalFiniteRepresentation q` to the
quotient `Q.horizontalFiniteRepresentation q` given by postcomposition with
the published compact projection `Q.compactProjection`; its value is
`Q.projection (f.val X)`. `horizontalProjection_eq_zero_iff` states that a
projected numerator cochain is zero exactly when all its values lie in the
denominator `Q.lower`. With `[NeZero n]`, `horizontalProjection_differential`
proves

```text
Q.horizontalProjection (q + 1) (Q.upper.horizontalDifferential q f)
  = Q.horizontalDifferential q (Q.horizontalProjection q f),
```

for the published numerator differential, by naturality of the differential
along `projectionReducedLieHom`, and
`horizontalProjection_differential_comp` states the same square as an
equality of finite adelic intertwiners with the published
`Q.upper.horizontalDifferentialIntertwiner q`. Surjectivity of
`horizontalProjection` is not claimed.

## Quotient intertwiners and equivalences

For quotients `Q`, `T`, `U` and a whole-operator intertwiner
`L : Q.representation.IntertwiningMap T.representation`,
`reducedLieRestrictionMap L` is the same linear map as a reduced Lie module
homomorphism; its Lie equation specializes the intertwining equation at the
actual differential operator of each reduced direction. `horizontalMap L q`
postcomposes horizontal cochains with the compact restriction
`compactRestrictionMap L` of `OperatorSubquotientTensorHorizontal` and is a
finite adelic intertwiner, by the
intertwining equation at the actual finite operators.
`horizontalMap_apply`, `horizontalMap_id` and `horizontalMap_comp` give its
value and its compatibility with identities and composition. With
`[NeZero n]`, `horizontalMap_differential` and
`horizontalMap_differential_comp` prove that it commutes with the quotient
horizontal differentials, by naturality along `reducedLieRestrictionMap L`.

For a quotient equivalence `e : Q.Equivalence T`,
`Equivalence.reducedLieRestriction e` is the underlying linear equivalence
as an equivalence of reduced Lie modules, and `Equivalence.horizontalEquiv e
q` is the equivalence of finite adelic representations on `H q` built from
the published `horizontalCoefficientEquiv` of
`Equivalence.compactRestriction e`; its value is `e (f.val X)`, its
underlying linear map is `horizontalMap e.toIntertwiningMap q`, and, with
`[NeZero n]`, `Equivalence.horizontalEquiv_differential` proves that it
commutes with the quotient horizontal differentials.

## Scope and provenance

This module does not prove that the differential squares to zero and
constructs no cycles, boundaries or cohomology, no relative (g,K)-module
structure, no quotient evaluation as a function, and no local factor,
admissibility or existence statement.

The provenance is internal composition and restriction of the published
`OperatorSubquotient`, `OperatorSubquotientArchimedean`,
`ArchimedeanRelativeAdjoint`, `ArchimedeanSplitCenter`,
`ArchimedeanHorizontal`, the generic `Cohomology.Lie.HorizontalDifferential`
and `Cohomology.Lie.CoefficientCochains`, and the numerator modules
`HorizontalDifferential`, `HorizontalFiniteAction` and
`HorizontalDifferentialFinite`, together with the companion quotient modules
`OperatorSubquotientLieAction`, `OperatorSubquotientCompactDifferentiation`
and `OperatorSubquotientTensorHorizontal` (the last for the compact
restrictions of quotient intertwiners and equivalences). No external source
assertion is introduced.

Authorship: Worker 2.

The inherited additive group instances have explicit names specific to this
module, as in the published neighbouring modules; their definitions are
unchanged. `LieRing.ofAssociativeRing` is a local instance only for the
commutator Lie algebra on `Module.End ℂ Q.Space`, as in the imported Lie
action modules.
