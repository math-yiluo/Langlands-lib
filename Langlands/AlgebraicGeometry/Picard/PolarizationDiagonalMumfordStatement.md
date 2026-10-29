# The Mumford map of the diagonal Poincare pullback of a polarization

This module states a theorem target only; its proof is a separate task. It
imports only `Langlands.AlgebraicGeometry.Picard.MumfordLineBundle` and
`Langlands.AlgebraicGeometry.Picard.RelativePolarization`, and it adds two
auxiliary definitions and one proposition. No existing declaration is changed.

## Definitions

`relativeDiagonal A` is the diagonal `A → A ×_S A`, written as
`pullback.lift (𝟙 A.X.left) (𝟙 A.X.left) rfl` into the relative space
`(relativeSpace A.X.hom).obj A.X`. In the Library,
`relativeSpace f T` is `pullback T.hom f`, so the first factor is the parameter
factor and the second is the copy of `A` on which the bundle lives.

`poincareDiagonalBundle A hA f` is the line bundle `(1, f)^* P` on `A`, built
from the Library's actual Poincare family `poincareFamily A hA`, a rigidified
line bundle on `(relativeSpace A.X.hom).obj (dualScheme A hA)`, that is, on
`dualScheme ×_S A` with the parameter first. It is built in three steps:

1. pull the Poincare family back along `f : A.X ⟶ dualScheme A hA` in its
   parameter variable with `RigidifiedLineBundle.relativePullback`, which gives
   a rigidified line bundle on `A ×_S A`;
2. forget the rigidification (`RigidifiedLineBundle.forget`);
3. pull back along `relativeDiagonal A` with `LineBundle.pullback`.

Since the diagonal is symmetric, this is GIT's `(1_X, λ)^* P`, read with the
factors written in the Library's parameter-first order.

## The statement

`PolarizationDiagonalMumfordStatement` says the following. Fix the nine
published constructor propositions (`pullbackTensorComparisonIsIsoStatement`,
`MumfordBundlePicardZeroStatement`, `PicardZeroUniversalBaseChangeStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`, `PullbackTensorSymmetryStatement`,
`PicardZeroPullbackStatement`). They are universally quantified parameters
because the published dual abelian scheme, Mumford map and `IsPolarization`
take them as inputs. Then take any quasi-separated base `S`, any abelian scheme
`A` over `S`, a dual-scheme witness `hA` with its geometry `geometryA`, an
inverse `MA` of the Poincare family with its evaluation `evaluationA`, and any
homomorphism `lam : A ⟶ DA` into the published dual abelian scheme
`dualAbelianSchemeFromEvaluation ...` that satisfies the published
`IsPolarization`. Write `L = poincareDiagonalBundle A hA (groupHom lam).hom.hom`.
Then there exist:

- a line bundle `B` on `S` with an evaluation `e^* L ⊗ B ≅ O_S` (normalization
  data along the unit section `e = unitSection A`);
- a line bundle `M` on `A` with an evaluation `N ⊗ M ≅ O_A`, where `N` is the
  normalized bundle `LineBundle.normalize ... L B evaluationB`;

such that the published `mumfordSchemeMapOfLineBundle` of these data equals
`(groupHom (2 • lam)).hom.hom`, the underlying scheme map of `2 • lam`. Here
`2 • lam` is the natural-number multiple in the Library's pointwise additive
group of homomorphisms of abelian schemes.

The conclusion is an equation of morphisms of schemes `A.X ⟶ dualScheme A hA`,
so it holds on all test schemes, including nonreduced ones. The statement does
not assume any representability, geometry or symmetry beyond the displayed
binders and `IsPolarization`.

## Source

Mumford, Fogarty, Kirwan, *Geometric Invariant Theory*, 3rd ed., Chapter 6,
Section 2, printed pages 120-121 (PDF pages 133-134; literature id
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`):

- Definition 6.2: the homomorphism `Λ(L) : X → X^` classifying
  `m^* L ⊗ p_1^* L^{-1} ⊗ p_2^* L^{-1}`, regarded as a family over `X`;
- the universal sheaf `P` on `X × X^`, normalized so that its restriction along
  `e × 1 : X^ → X × X^` is trivial, and `L^Δ(λ) = (1_X, λ)^* P`;
- Proposition 6.10: if `λ` is a polarization, then `Λ(L^Δ(λ)) = 2λ`.

GIT proves Proposition 6.10 over a field, reducing to an algebraically closed
one, and deduces the relative case from rigidity (Corollary 6.2). The proof of this statement is a
later task.

## Comparison with the source

- **Normalization data.** GIT normalizes `P` along the identity section, so
  `L^Δ(λ)` is already normalized (`e^* L^Δ(λ) ≅ O_S`, GIT p. 121). The Library's
  Poincare family carries its rigidification separately, and this statement
  forgets it before pulling back along the diagonal. The published Mumford
  construction takes explicit normalization data `(B, evaluationB)` and an
  explicit inverse `(M, evaluation)` as inputs, so the statement asserts that
  such data exist and that the equation holds for them. Mathematically one can
  take `B = O_S`, and the Mumford map does not depend on the choice of data.
  The Lean statement claims neither of these facts; it claims only the
  existence of some data satisfying the equation.
- **Polarizations.** GIT Definition 6.3 defines polarizations of projective
  abelian schemes by requiring `λ = Λ(L)` for an ample `L` at every geometric
  point. The statement uses the Library's published `IsPolarization` instead:
  `lam` is an isogeny, and for every algebraically closed field `K` and every
  morphism `Spec K → S`, the base change of `lam` satisfies
  `HasFieldAmpleMumfordPresentation` (it is the Mumford map of an ample line
  bundle after some extension of `K`). This statement does not compare the two
  notions.
- **Dual scheme.** GIT's `X^` is the Picard scheme component. Here it is the
  Library's `dualScheme A hA` with its chosen Poincare family, underlying the
  published dual abelian scheme `dualAbelianSchemeFromEvaluation`.
