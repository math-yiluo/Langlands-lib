# Infinite right translation of the actual group-scheme forms

Fix a number field `F`, an affine group scheme `G` over `F`, and a proof
`hsmooth` that `G` is smooth of relative dimension `d`. The infinite adelic point
group `G(𝔸_{F,∞})` carries the published smooth atlas and Lie group structure.
`AdelicEnvelopingAlgebra F G hsmooth` is the universal enveloping algebra of
the complexified identity tangent space, and `actualAdelicEnvelopingAction` is
its published action on the original finite plot-smooth rational functions.
`R(x)` denotes the published right translation `R(x) f (y) = f (y x)`.

Getz–Hahn (6.11)–(6.14) (printed pp. 163–164) equip the automorphic forms with
an action of `(𝔤, K_∞)` and of `G(𝔸_F^∞)`. They remark that `G(F_∞)` does not
act: a translate by `g ∈ G(F_∞)` is only finite under `g K_∞ g⁻¹`. This module
proves the infinite-place part of that structure for the Library's actual form
spaces, with `K_∞` replaced by any specified subgroup `Kinf`.

## The adjoint automorphism of the enveloping algebra

- `Langlands.Algebra.ComplexLieExtension.extendLieHom` extends a real Lie
  algebra homomorphism `L → L'` complex-linearly to `ℂ ⊗ L → ℂ ⊗ L'`. The bracket
  law is checked on pure tensors with `LieAlgebra.ExtendScalars.bracket_tmul`.
- `adelicEnvelopingConjugation F G hsmooth g` is the enveloping algebra
  endomorphism induced by the complexified tangent conjugation
  `groupTangentConjugationLieEquiv` (module `SmoothGroupConjugationLie`). On
  pure generators it sends `ι(z ⊗ X)` to `ι(z ⊗ Ad(g) X)`.
- It satisfies `Ad(g k) = Ad(g) ∘ Ad(k)` and `Ad(1) = id`, by
  `UniversalEnvelopingAlgebra.hom_ext` and the corresponding tangent laws. So
  `adelicEnvelopingConjugationEquiv` is an algebra automorphism with inverse
  `Ad(g⁻¹)`.
- `adelicEnvelopingConjugation_mem_center`: it preserves the center, because it
  is surjective. `adelicCenterConjugation` is its restriction to the center.

## Covariance

`finitePlotSmoothRightAction_actualAdelicEnvelopingAction`: for every infinite
adelic point `g`, every enveloping element `a` and every function `f`,
`R(g) (D_a f) = D_(Ad(g) a) (R(g) f)`. The proof lifts `a` to the tensor algebra
and inducts over scalars, generators, products and sums. The generator case is
the published real covariance `finitePlotSmoothDifferentialAction_infiniteRightAction`,
extended complex-linearly.

## Stability of the form conditions

- `IsAdelicCenterFinite.infiniteRightAction`: right translation by any infinite
  adelic point preserves finiteness of the actual center orbit. The center
  orbit span of `R(g) f` is the image under `R(g)` of the center orbit span of
  `f`, because `Ad(g)` permutes the center.
- `IsAdelicInfiniteFinite.subgroupAction`: an element of `Kinf` preserves
  finiteness of the `Kinf` orbit (published `IsFiniteVector.action`).
- `HasAdelicUniformPolynomialGrowth.infiniteRightAction`: right translation by
  any infinite adelic point preserves uniform growth with the same exponent.
  For each `a`, `D_a (R(g) f) = R(g) (D_(Ad(g⁻¹) a) f)`. The published height
  submultiplicativity multiplies the constant by `H(g)^e`. This needs `0 < N`.
- `IsAdelicAutomorphicForm.subgroupAction`: the published form conditions are
  preserved by right translation by elements of `Kinf`. Moderate growth uses the
  published `adelicGrowthSubrepresentation`.

## Invariant subspaces

- `adelicUniformGrowthInfiniteSubrepresentation`: the uniform-growth subspace is
  invariant under right translation by all of `G(𝔸_{F,∞})`.
- `adelicAutomorphicInfiniteSubrepresentation` and
  `uniformAdelicAutomorphicInfiniteSubrepresentation`: the published form space
  and uniform form space are invariant under `Kinf`.
- `uniformAdelicAutomorphicInfiniteSubrepresentation_envelopingAction`: on the
  uniform forms, the `Kinf` action and the published enveloping action
  `uniformAdelicAutomorphicEnvelopingAction` satisfy
  `R(k) D_a = D_(Ad(k) a) R(k)`.
- `adelicCuspidalInfiniteSubrepresentation` and
  `uniformAdelicCuspidalInfiniteSubrepresentation`: the published cusp form
  spaces are invariant under `Kinf`. Cuspidality is preserved because the
  published normalized parabolic cusp space is invariant under all adelic right
  translations. These need `LocallyOfFiniteType` and the parabolic dynamic
  statement `hPD`, as the published cusp forms do.

The published hypotheses on the form spaces (connected reductivity, closed
embedding, maximal compactness of `Kinf`) are carried as parameters. The
stability proofs do not use them. They use only `0 < N`, for the growth
conditions.

## Provenance

The content is internal: it is derived from published Library constructions.
They are the actual enveloping action, its real covariance
(`GroupSchemeFiniteVectorDifferential`), the form and cusp form spaces
(`GroupSchemeForms`, `GroupSchemeCuspidalForms`), uniform growth
(`GroupSchemeAdelicUniformGrowth`) and the uniform enveloping action
(`GroupSchemeFormDifferential`). It also uses the bracket preservation of
`SmoothGroupConjugationLie`. Getz–Hahn is cited for the action (6.14) whose
infinite part is constructed here.

## Scope

The module does not prove:

- that the enveloping action preserves cuspidality. So the cusp form spaces are
  invariant under `Kinf` but not shown to be invariant under the enveloping
  action.
- that the form space is invariant under infinite points outside `Kinf`. As
  Getz–Hahn note, this fails in general.
- any comparison with the literal tensor space of Getz–Hahn (6.1).
- admissibility, or that `Ad(g)` acts trivially on the center.
