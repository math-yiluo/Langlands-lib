# Actual complex Lie actions on automorphic operator quotients

This internal construction works with every number field `F : Type uF`,
every natural rank `n`, complex coefficients and an actual
`OperatorSubquotient F n`. The carrier is the original module quotient
`Q.Space = Q.upper.Space ⧸ Q.lower.toSubmodule`. Its denominator is
already invariant under the whole concrete automorphic operator algebra.
No additional invariance, covariance or finiteness hypothesis is supplied.

## Global and compact Lie actions

`complexLieAction` composes the quotient's genuine induced enveloping
action, viewed as a Lie algebra homomorphism into the commutator Lie
algebra of `Module.End ℂ Q.Space`, with the actual generator map
`envelopingGenerator F n`. Thus

```text
Q.complexLieAction :
  ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ Q.Space.
```

`compactLieAction` restricts this along the actual complexified compact
Lie inclusion `compactComplexInclusion F n`. The two application lemmas
identify these operators with the quotient enveloping action of the
inserted generator. The named instances `quotientComplexLieRingModule`,
`quotientComplexLieModule`, `quotientCompactLieRingModule` and
`quotientCompactLieModule` are the induced Lie module structures on the
same `Q.Space`. `complex_lie_eq` and `compact_lie_eq` state that their
brackets are these actions. As in the published numerator module
`OperatorLieAction`, the compact module structure is obtained from the
complex one by pulling back along the compact inclusion.

## Projection, denominator and Mathlib's Lie quotient

On a projected numerator representative, `complexLieAction_projection`
and `compactLieAction_projection` identify the quotient operators with
the projection of the published numerator operators
`Q.upper.complexLieAction` and `Q.upper.compactLieAction`.
`complexLieProjection` and `compactLieProjection` are the original
canonical projection, with linear map exactly `Q.projection.toLinearMap`,
as Lie module homomorphisms. Both are surjective.

`lowerComplexLieSubmodule` and `lowerCompactLieSubmodule` are the actual
denominator `Q.lower.toSubmodule`, with the Lie stability supplied by its
existing invariance under the corresponding differential operators. The
membership lemmas state that membership is exactly membership in
`Q.lower`. The kernel theorems prove that the kernel of each Lie
projection is exactly the corresponding denominator Lie submodule.

`complexLieQuotientEquiv` and `compactLieQuotientEquiv` are Lie module
equivalences from `Q.Space` to Mathlib's Lie module quotient of
`Q.upper.Space` by the respective denominator Lie submodule. Their linear
equivalence is `Submodule.quotEquivOfEq` for the equality of underlying
submodules, which holds by definition. Their compatibility with brackets
is proved on representatives from Mathlib's Lie module homomorphism
`LieSubmodule.Quotient.mk'`. The `_projection` lemmas send a projected
representative to its Mathlib quotient class.

## Finite and compact compatibility

`finiteRepresentation_complexLieAction` and its compact analogue prove
that every finite adelic translation commutes with every quotient Lie
operator. They specialize the published quotient finite/enveloping
commutation law.

`compactRepresentation_complexLieAction` proves the actual covariance law:
for every `k : standardInfiniteCompact F n` and complex Lie element `X`,
compact translation by `k` of `X` acting on `f` equals the action of
`complexLieConjugation F n k.val X` on the compact translate of `f`. Its
proof combines the published quotient compact/enveloping covariance law
with `envelopingConjugation_generator`.

## Archimedean places

`realPlaceLieAction v` and `complexPlaceLieAction v` restrict
`Q.complexLieAction` along the published injective per-place complex Lie
inclusions, with domains `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ` and
`ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ`. At a complex place the full underlying
real matrix Lie algebra is complexified. They are the quotient analogues
of the published numerator actions in `PlaceLieAction`.

The application lemmas identify these operators with the quotient
enveloping action of the inserted global generator. The `_projection`
lemmas identify each place operator on a projected representative with
the projection of the published numerator place operator. Finite adelic
translations commute with both place actions.

`complexify_action_eq_sum_place` proves that, for every genuine real
global Lie generator `X`, the quotient action of its complexification is
the sum over real places and over complex places of the place operators
of the pure tensors `1 ⊗ₜ` of its place projections. The proof applies the
quotient action to the published decomposition `sum_placeLieInclusions`
and then uses linearity and the pure-tensor inclusion formulas.

For every `p : ArchimedeanCompactFactors F n`,
`compactRepresentation_realPlaceLieAction` proves that translation by its
standard compact element conjugates the real-place operator of `X` into
the real-place operator of `unitaryMatrixComplexLieConjugation ℝ n (p.1 v) X`.
`compactRepresentation_complexPlaceLieAction` is the complex-place
version, with `p.2 v`. Both combine the global covariance law above with
the published place-adjoint compatibilities
`complexLieConjugation_realInclusion` and
`complexLieConjugation_complexInclusion`.

## Equivalences

For a supplied whole-operator quotient equivalence `e : Q.Equivalence T`,
`Equivalence.complexLieRestriction` and
`Equivalence.compactLieRestriction` are Lie module equivalences with
underlying linear equivalence exactly `e.toLinearEquiv`; the application
lemmas evaluate them as `e`. `map_realPlaceLieAction` and
`map_complexPlaceLieAction` prove that `e` intertwines every place
operator. These are evaluations of the existing intertwining property on
the corresponding differential operators.

## Provenance and scope

Provenance is internal. The construction reuses `OperatorSubquotient`,
`OperatorSubquotientArchimedean`, `OperatorLieAction`, `PlaceLieAction`,
`ArchimedeanPlaceLie`, `ArchimedeanAdjoint`, `ArchimedeanPlaceAdjoint` and
Mathlib's Lie module quotient. It introduces no new identification with an
external source or normalization convention.

These actions retain the entire quotient carrier. They do not construct a
`(g, K)`-module structure, select irreducible archimedean tensor factors,
or prove admissibility, tensor factorization, local Langlands
attachments, automorphic existence or spectral existence. No topology,
analytic differentiability or evaluation of a quotient class as a
function is constructed.
