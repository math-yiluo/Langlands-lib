# The finitely generated Galois character functor

Author: Worker 3483.

This derived construction restricts the published actual Galois character
functor to actual commutative groups split by a specified field extension, and
bundles its finitely generated values using Mathlib's existing action category.
The construction retains torsion.

## Source and target

Let `k L : Type u` be fields with `Algebra k L`. The source is
`(SplitMultiplicativeType k L)ᵒᵖ`. An object of the underlying category is an
actual commutative group scheme `T` over `Spec k` whose pullback to `L` is
isomorphic to `D_L(M)` for some finitely generated abelian `M`. All actual
ground-field homomorphisms are morphisms; no splitting model is part of the
object or the morphism.

The target is exactly Mathlib's
`Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L)`. Its objects are finitely generated
integral modules with an action of the field automorphism group. Its morphisms
are integral linear maps commuting with that action. The explicit action
category allows the module universe `u` independently of the universe of the
integers. No parallel category of representations is defined.

No finite-dimensional, separability or Galois hypothesis is needed to construct
this functor. If `L/k` is finite Galois, its acting group is the usual finite
Galois group. No smoothness, freeness, connectedness, reducedness or
characteristic assumption is imposed.

## Objects, action and morphisms

`characterAction k L T` has underlying object exactly the previously published
`characterModule k L T`. Its carrier is the actual character group

```text
X*(T_L) = Hom_CommGroupScheme(Spec L)(T_L, Gm_L).
```

The existing finite-generation theorem for this group supplies its
`FGModuleCat` membership. Its action is precisely the existing
`characterLattice.galoisRepresentation k L T.obj`, transported only through
Mathlib's equivalences between linear endomorphisms and categorical
endomorphisms. `characterAction_ρ_apply` identifies the action pointwise.
Addition is the actual pointwise product of characters.

For an actual ground-field map `f : H → G`, `characterPullback k L f` has
underlying map the already published `characterLattice.galoisPullback`:

```text
X*(G_L) → X*(H_L),   χ ↦ f_L ≫ χ.
```

`characterPullback_apply` gives this formula. The intertwining law is supplied
by the published `galoisRepresentation_naturality`, rather than assumed of a
map. Every character is a morphism of actual group schemes and hence is
defined on all test schemes, including nonreduced tests.

The entry definition `characterFunctor k L` sends `op T` to
`characterAction k L T` and an opposite morphism to `characterPullback` along
its underlying morphism. Its identity and composition laws follow from those
of actual scheme base change and associativity of composition. The theorem
`characterFunctor_map_apply` records the precomposition formula on morphisms.

## Forgetful compatibility

`forgetCharacterFiniteness k L` is the composite of Mathlib's functor forgetting
finite generation, applied to actions, with `Rep.ActionToRep`. The equality
`characterFunctor_forget` states

```text
characterFunctor k L ⋙ forgetCharacterFiniteness k L =
  (inclusion k L).op ⋙ characterLattice.galoisFunctor k L.
```

Thus the restricted construction recovers the published unrestricted functor on
both objects and maps. The equality is definitional, including the canonical
action and actual character pullbacks.

## Provenance and scope

This is internal packaging of the published
[specified-extension category and character modules](MultiplicativeTypeSplitCategory.md)
and [actual Galois character functor](GaloisCharacterFunctor.md). The finite
generation, canonical action and naturality are reused from those constructions.
The short laws here express this restriction and its forgetful compatibility.

Their registered original source is J. S. Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 12.g and Theorem 12.23, printed pp.239–240 / PDF pp.255–256,
describe the canonical contravariant character functor and the classification
using finitely generated Galois modules. The proof of Corollary 12.25 on the
latter page uses a common finite Galois splitting field. The specified-extension
restriction here is a derived construction; the classification assertion is
not used as a Lean proof. The original pages and the complete retained official
2017 errata snapshot were read; no correction affects these passages.

This unit constructs the actual functor and its intrinsic laws. Full
faithfulness, essential surjectivity, an equivalence, compatibility with exact
sequences and absolute-Galois continuity require separate statements and proofs.
