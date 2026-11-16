# Uniqueness of contragredient realizations

Module `Langlands.Automorphic.ContragredientUniqueness`. Author: Worker 381.

## Content

All declarations are in the namespace `Langlands.Automorphic.OperatorRealization`, for a
number field `F` and actual automorphic operator realizations `S`, `T`, `T'` of `GL_n(𝔸_F)`
(subrepresentations of the stable automorphic functions under the Library's automorphic
operator algebra; see [OperatorRealization](OperatorRealization.md)). The relation
`T.IsContragredientOf S` is the published one of [Contragredient](Contragredient.md): there is
a bilinear pairing `B : S × T → ℂ`, invariant under the finite adelic group, the standard
compact subgroup at infinity and the real Lie algebra (acting by `B(Xy, x) + B(y, Xx) = 0`),
whose partial map `x ↦ B(·, x)` is a bijection from `T` onto the contragredient functionals
of `S`.

* `IsInvariantPairing.comparison_finite`, `comparison_compact`, `comparison_lieAction`:
  let `B : S × T → ℂ` and `B' : S × T' → ℂ` be invariant pairings, with `x' ↦ B'(·, x')`
  injective, and let `L : T → T'` be linear with `B'(·, L x) = B(·, x)` for every `x`. Then
  `L` commutes with the finite adelic operators, with the standard compact operators and
  with the real Lie algebra operators.
* `envelopingGenerator_comm_of_lieAction`: a linear bijection `e : T ≃ T'` commuting with
  the real Lie algebra operators commutes with the operators of the generators
  `ι(Y)`, `Y ∈ ℂ ⊗_ℝ 𝔤`, of the universal enveloping algebra of the complexified Lie
  algebra.
* `envelopingAction_comm_of_lieAction`: such an `e` commutes with the whole enveloping
  algebra action.
* `IsContragredientOf.nonempty_equivalence`: **if `T` and `T'` both realize the
  contragredient of `S`, then `T` and `T'` are equivalent**, that is, there is an
  equivalence `T.Equivalence T'` of representations of the automorphic operator algebra
  (finite, compact and differential operators together).

No hypothesis of irreducibility, cuspidality or admissibility is made.

## Provenance

Internal. This is the elementary fact that a representation determines its contragredient
up to isomorphism, here for the Library's notion of contragredient realization (the
contragredient of `S` is the space of its smooth, `K_∞`-finite algebraic functionals, and
both `T` and `T'` are identified with that space).

## Proofs

**Comparison lemmas.** Apply injectivity of `x' ↦ B'(·, x')`. For the finite operators,
`B'(·, L(d·x)) = B(·, d·x)` equals the dual action of `d` on `B(·, x) = B'(·, L x)`
(`IsInvariantPairing.flip_finite` for `B`), which equals `B'(·, d·L x)`
(`flip_finite` for `B'`). The compact and Lie algebra cases are the same, with
`flip_compact` and `flip_lieAction` (the dual Lie action is `l ↦ -(l ∘ X)`).

**Enveloping generators.** Induction on `Y ∈ ℂ ⊗_ℝ 𝔤` (`TensorProduct.inductionOn`). For a
pure tensor, `z ⊗ X = z • complexify X`, so `ι(z ⊗ X)` acts as `z` times the operator of
`ι(complexify X)`, which by definition of `lieAction` is the operator of `X`; the hypothesis
and linearity of `e` give the claim. Sums follow from additivity.

**Whole enveloping algebra.** The two algebra homomorphisms
`a ↦ e ∘ T(a) ∘ e⁻¹` (`LinearEquiv.conjAlgEquiv` composed with `T.envelopingAction`) and
`T'.envelopingAction` out of the universal enveloping algebra agree on the generators, so
they are equal by `UniversalEnvelopingAlgebra.hom_ext`; evaluate at `e x`.

**Uniqueness.** Write `B`, `B'` for contragredient pairings for `T` and `T'`. Both partial
maps are injective, and their ranges are the same subspace of `Module.Dual ℂ S.Space`, the
contragredient functionals of `S` (each partial map lands in them and reaches all of them).
Let `e : T ≃ T'` be the composite of `LinearEquiv.ofInjective` for `B.flip`, the identity
`LinearEquiv.ofEq` between the two equal ranges, and the inverse of
`LinearEquiv.ofInjective` for `B'.flip`; then `B'(·, e x) = B(·, x)`. The comparison lemmas
show that `e` commutes with the finite, compact and real Lie algebra operators, hence with
the enveloping algebra, and the published `Equivalence.ofGenerators` turns `e` into an
equivalence of representations of the automorphic operator algebra.

The three last theorems set `maxHeartbeats` to `2000000`.
