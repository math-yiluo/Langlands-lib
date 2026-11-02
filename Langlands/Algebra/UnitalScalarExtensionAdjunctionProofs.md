# Renard A.V.2: proof of the scalar-extension adjunction

Module `Langlands.Algebra.UnitalScalarExtensionAdjunctionProofs`.
Namespace `Langlands.Algebra.UnitalScalarExtensionAdjunction`.
Entry theorem `scalarExtensionAdjunctionStatements`.

Worker 1171 wrote the Lean proof and this explanation.

## Target

The theorem proves exactly the published closed proposition
`ScalarExtensionAdjunctionStatements.{uB,uA,uM}` from the unchanged module
`Langlands.Algebra.UnitalScalarExtensionAdjunctionStatements`. Its type keeps
the three independent universe parameters. The proposition says: for all
`B : Type uB`, `A : Type uA`, `[Ring B]`, `[Ring A]` and `phi : B →+* A`,
there is one native adjunction `adj : E ⊣ R` with
`AdjunctionProperties phi adj`. Here E is
`Langlands.Algebra.UnitalScalarExtension.functor.{uB,uA,uM} phi` and R is
`Langlands.Algebra.UnitalScalarExtension.restriction.{uB,uA,max uA uM} phi`.

The proof module imports only the statement module. That module imports the
published construction `Langlands.Algebra.UnitalScalarExtension` and pinned
Mathlib `Mathlib.CategoryTheory.Adjunction.Basic`. The proof does not change
the statement pair or anything it imports. It assumes no tensor object,
balancing law, adjunction or Hom equivalence. B and A are arbitrary rings
and may be noncommutative. phi is any unital ring homomorphism and may fail
to be injective.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.V.2. The proof
follows the scalar-extension example on printed pp.260–261 (one-based
PDF266–267). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

In the source, A is a unital complex algebra and B is a subalgebra. The
example defines theta(f)(x) = f(1 tensor x) and
sigma(g)(a tensor x) = a g(x). It checks that both maps give module
morphisms, leaves their naturality to the reader, and checks the two
inverse laws on generators. The source then remarks that the second
viewpoint underlies this argument. That viewpoint uses the B-morphism
eta_X(x) = 1 tensor x and the A-morphism epsilon_Y(a tensor y) = a y,
which satisfy the two triangle identities (A.V.2.1) and (A.V.2.2):
x goes to 1 tensor x and then to 1 x = x, and a tensor x goes to
a tensor 1 tensor x and then to a (1 tensor x) = a tensor x.
The Lean proof takes this second route.

The supplementary older-edition corrections are registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
PDF18–19 correct the old scalar example's "B-morphism" to "A-morphism" and a
parenthesization error. The governing 2026 example already contains both
corrections. As in the published construction, "subalgebra" means a unital
subalgebra: restriction lands in unital B-modules and theta uses 1.

The source case is the specialization `S : Subalgebra ℂ A` with B = S and
`phi = S.val.toRingHom`. The generalization to any unital ring homomorphism
between possibly noncommutative rings is internal derived infrastructure.
So are the native `Adjunction` packaging and the explicit repetition of the
intrinsic adjunction laws in the seven property predicates. The helper
declarations of this module are internal infrastructure for the proof.
None of this is a new numbered theorem attributed to the source.

## Universes and the direction of theta

B lies in `Type uB` and A in `Type uA`. Both module categories have carrier
universe `max uA uM`. Tensoring such a carrier with A gives a quotient in
`Type (max uA (max uA uM)) = Type (max uA uM)`. B only indexes balancing
relations and does not raise this universe. The proof uses the explicit
instances `functor.{uB,uA,uM}` and `restriction.{uB,uA,max uA uM}`. It imposes
no relation between uB and the other two parameters.

For X in `ModuleCat B` and Y in `ModuleCat A`, the native Hom equivalence of
`adj : E ⊣ R` goes from `E.obj X ⟶ Y` to `X ⟶ R.obj Y`. The scalar
example's theta is this native **forward** map, and sigma is its inverse.
The initial two-variable natural isomorphism of A.V.1 (printed p.258 /
PDF264) has the reverse direction: its theta goes from `Hom(Y,F(X))` to
`Hom(G(Y),X)`. After identifying G with E and F with R, it is the inverse of
the native forward map. The comparison with that general Hom-bifunctor
formulation is not part of this proof.

## Proof

### Quotient helpers

The published quotient `Tensor phi M` is the noncommutative balanced
integer tensor product `NonUnitalModuleTensor.Tensor B A M`. Its right
B-action on A is `rightModule phi`, and its left B-module M is
`NonUnitalModule.ofModule B M`. Three helpers expose published facts about
this quotient in the notation `tmul phi M a m`:

- `tmul_add_right` is additivity of pure tensors in the module variable,
  from `NonUnitalModuleTensor.tmul_add`.
- `addMonoidHom_ext` says that two additive maps out of `Tensor phi M` are
  equal when they agree on all pure tensors. It is
  `NonUnitalModuleTensor.hom_ext`.
- `liftAddHom` descends a biadditive map `b : A →+ M →+ Z` to an additive
  map on `Tensor phi M`, when `b (a * phi c) m = b a (c • m)` for all c, a
  and m. It is `NonUnitalModuleTensor.lift`. Its value on `tmul phi M a m`
  is `b a m` by definition (`liftAddHom_tmul`).

### The unit

For X in `ModuleCat B`, `unitMap phi X` is the morphism
`X ⟶ R.obj (E.obj X)` sending x to `tmul phi X 1 x`. Additivity is
`tmul_add_right`. For B-linearity, b acts on `R.obj (E.obj X)` through
`phi b`. The published balancing law `tmul_balanced` gives
`tmul 1 (b • x) = tmul (1 * phi b) x`, which is `tmul (phi b) x` by
`one_mul`. By the residual action, `phi b • tmul 1 x` is
`tmul (phi b * 1) x`, which is also `tmul (phi b) x` by `mul_one`.
This is the source's check that theta(f) is a B-morphism, done once for
the unit.

### The counit

For Y in `ModuleCat A`, `actionBiadditive phi Y` is Mathlib's `smulAddHom A Y`,
the pairing a, y ↦ a • y, with y read in the restricted module `R.obj Y`.
It is balanced (`actionBiadditive_balanced`): since c acts on `R.obj Y`
through `phi c`, `mul_smul` gives `(a * phi c) • y = a • (c • y)`.
`counitAddHom phi Y` is its descent by `liftAddHom`. On pure tensors it
sends `tmul a y` to `a • y` by definition (`counitAddHom_tmul`).

The descended map is A-linear (`counitAddHom_smul`). For fixed a, compare
the additive maps t ↦ counit(a • t) and t ↦ a • counit(t). On a pure
tensor a' ⊗ y, the residual action gives a • (a' ⊗ y) = (a * a') ⊗ y. So
both values are `(a * a') • y = a • (a' • y)` by `mul_smul`. Hence the two
maps agree by `addMonoidHom_ext`. This is the source's check that sigma(g)
is an A-morphism, done once for the counit. `counitMap phi Y` packages the
counit as the morphism `E.obj (R.obj Y) ⟶ Y`.

### The adjunction

`adjunction phi` is a term of Mathlib's `Adjunction` structure built from
these data:

- Unit naturality, u ≫ eta_X = eta_X' ≫ R(E(u)) for u : X' ⟶ X, holds
  pointwise by definition: both sides send x to `tmul 1 (u x)`.
- Counit naturality, E(R(v)) ≫ epsilon_Y' = epsilon_Y ≫ v, is checked with
  the published `UnitalScalarExtension.hom_ext`: A-linear maps out of the
  extended module agree when they agree on pure tensors. On a ⊗ y the two
  sides are `a • v y` and `v (a • y)`, which agree by A-linearity of v.
- The left triangle E(eta_X) ≫ epsilon_E(X) = identity is checked with the
  same extensionality. a ⊗ x goes to a ⊗ (1 ⊗ x) and then to
  a • (1 ⊗ x) = (a * 1) ⊗ x, which is a ⊗ x by `mul_one`.
- The right triangle eta_R(Y) ≫ R(epsilon_Y) = identity sends y to
  1 ⊗ y and then to 1 • y = y, by `one_smul`.

These are the two source triangles (A.V.2.1) and (A.V.2.2).

### The seven properties

In pinned Mathlib (commit `5ed2965256430c3649e86755f9576b54eca72435`),
`Adjunction.homEquiv adj X Y` is defined from the unit and counit. Its
forward map is f ↦ `adj.unit.app X ≫ R.map f`, and its inverse is
g ↦ `E.map g ≫ adj.counit.app Y`. Theta and sigma in the published
predicates are this forward map and its inverse. `adjunction_properties`
proves the seven predicates for `adjunction phi`, in the published
right-associated order:

1. `HomFormulas` holds by definition. theta(f)(x) unfolds to
   `f (tmul 1 x)`. sigma(g)(a ⊗ x) unfolds through the published tensor map
   and the counit's lift to `a • g x`.
2. `HomInverseLaws` are the inverse laws `symm_apply_apply` and
   `apply_symm_apply` of the Mathlib equivalence `homEquiv`. Mathlib derives
   these laws from the unit and counit naturality and the two triangles. This matches the source's remark that
   the inverse laws come from (A.V.2.1) and (A.V.2.2).
3. `HomNaturality` rewrites with Mathlib's
   `Adjunction.homEquiv_naturality_left`, `homEquiv_naturality_right` and
   their `_symm` versions. These are general consequences of the unit and
   counit naturality. They replace the naturality check that the source
   leaves to the reader.
4. `UnitCounitFormulas` holds by definition: eta_X(x) = `tmul 1 x`, and
   epsilon_Y(`tmul a y`) = `a • y` with the tensor formed from R(Y).
5. `UnitCounitNaturality` is the naturality field of the unit and counit.
6. `TriangleIdentities` are the two triangle fields of the structure.
7. `HomUnitCounitRelations` holds by definition, since homEquiv is defined
   from the unit and counit.

All seven properties concern the same adjunction `adjunction phi`. The
entry theorem `scalarExtensionAdjunctionStatements` gives it as the
existential witness for every B, A and phi.

## Checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, the module compiles
with no errors and no warnings. The entry theorem depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. The proof
uses no `sorry`, no new axioms and no native evaluation.

## Scope

This module proves only the published A.V.2 scalar-extension aggregate. The
general Hom-bifunctor/native comparison stays with task
`5257557e-f55e-4001-a9de-88afdaf47d6b`. The original nonunital-module
adapters, other scalar-change assertions and the rest of Appendix A keep
their separate obligations. This proof does not complete A.V, Appendix A or
the whole-book program.
