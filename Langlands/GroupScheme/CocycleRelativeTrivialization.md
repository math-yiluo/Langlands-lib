# Trivializations of cocycles relative to a base

Authors: Worker 303.

This internal helper works with the natural cocycles of
`Langlands.GroupScheme.TorsorCocycle`. It imposes no field, reductivity or
smoothness hypothesis. Fix a base scheme `S`, a group scheme `G` over `S`, a
cover `U : Over S` and a cocycle `ξ : Cocycle G U`. Write `⊗` for the fibre
product over `S`, i.e. the cartesian monoidal structure of `Over S`, with
projections `fst` and `snd`.

## Definition

`Cocycle.IsTrivialOver ξ P g`, for `P : Over S` and `g : U ⊗ P ⟶ G.X`, says
that

```
ξ.toFun (a ≫ fst U P) (b ≫ fst U P) = (a ≫ g) * (b ≫ g)⁻¹
```

for every test object `Z` and all `a b : Z ⟶ U ⊗ P` with
`a ≫ snd U P = b ≫ snd U P`. If `P` is itself a scheme over `S`, this says that
`g` trivializes the base change of `ξ` to `P`, tested on pairs of points of
`U ⊗ P` that lie over the same point of `P`. This is exactly the conclusion of
`LocalSimplyConnectedUnramifiedSplittingStatement` with `P = Spec E`.

## Results

Below, a morphism of `Over S` is *fpqc* if its underlying scheme morphism is
quasi-compact, flat and surjective. Such morphisms are epimorphisms of schemes,
and they are stable under base change.

- `Cocycle.IsTrivialOver.of_whiskerLeft`: let `t : P' ⟶ P` be fpqc and
  `g : U ⊗ P ⟶ G.X`. If `(U ◁ t) ≫ g` trivializes `ξ` relative to `P'`, then
  `g` trivializes `ξ` relative to `P`. So relative trivializations descend
  along fpqc morphisms of the base.
- `Cocycle.exists_isTrivialOver`: let `V : Over S` have morphisms `r : V ⟶ U`
  and an fpqc morphism `s : V ⟶ P`. Let `f : V ⟶ G.X` satisfy
  `ξ.toFun (a ≫ r) (b ≫ r) = (a ≫ f) * (b ≫ f)⁻¹` whenever `a ≫ s = b ≫ s`.
  Then some `g : U ⊗ P ⟶ G.X` trivializes `ξ` relative to `P`.
- `Cocycle.baseChange b ξ V r`: for `b : S' ⟶ S`, `V : Over S'` and
  `r : (Over.map b).obj V ⟶ U`, this is a cocycle of
  `(GroupScheme.baseChange b).obj G` on `V`. Its value at `x y : Z ⟶ V` is
  the base-change adjunction point (`baseChangePointsEquiv`) corresponding to
  `ξ.toFun ((Over.map b).map x ≫ r) ((Over.map b).map y ≫ r)`. Naturality and
  the cocycle identity follow from those of `ξ`, because the adjunction
  bijection is natural and multiplicative. `Cocycle.baseChange_toFun` records
  the defining equation.
- `Cocycle.exists_of_baseChange_isTrivial`: if `ξ.baseChange b V r` is trivial,
  some `f : (Over.map b).obj V ⟶ G.X` satisfies
  `ξ.toFun (x ≫ r) (y ≫ r) = (x ≫ f) * (y ≫ f)⁻¹` for all
  `x y : Z ⟶ (Over.map b).obj V` over `S` with
  `x.left ≫ V.hom = y.left ≫ V.hom`. This is the input of
  `exists_isTrivialOver` with `s = Over.homMk V.hom`.

## Proofs

*Lifting lemma (private).* Let `c : Z ⟶ P` and an fpqc morphism `s : V ⟶ P`
be given. Put `Z' = Z.left ×_{P.left} V.left`, viewed over `S` through `Z`.
Then the projection `p : Z' ⟶ Z` is an epimorphism, since it is a base change
of `s.left`. The second projection `q : Z' ⟶ V` satisfies `q ≫ s = p ≫ c`.

*Descent along the base.* Let `a b : Z ⟶ U ⊗ P` have the same image in `P`.
Lift the common image along `t` to `q : Z' ⟶ P'` over an epimorphism
`p : Z' ⟶ Z`. Set `a' = lift (p ≫ a ≫ fst) q` and `b' = lift (p ≫ b ≫ fst) q`.
These maps `Z' ⟶ U ⊗ P'` have the same image `q` in `P'`. They satisfy
`a' ≫ (U ◁ t) = p ≫ a` and `b' ≫ (U ◁ t) = p ≫ b`. The hypothesis on `a'` and
`b'` is the required identity precomposed with `p`, and `p` is cancelled.

*Čech step.* The morphism `U ◁ s : U ⊗ V ⟶ U ⊗ P` is fpqc, as a fibre
product of the identity of `U` with `s` (`MorphismProperty.pullbackMap`).
Hence it is an effective epimorphism of schemes. On `U ⊗ V` put

```
φ = ξ(fst, snd ≫ r) * (snd ≫ f).
```

Let `x y` be points of `U ⊗ V` with the same image in `U ⊗ P`. Then they have
the same first coordinate `u`, and their second coordinates `v` and `w` have
the same image in `P`. The cocycle identity and the hypothesis give

```
ξ(u, r v) f(v) = ξ(u, r w) ξ(r w, r v) f(v) = ξ(u, r w) f(w) f(v)⁻¹ f(v).
```

So `φ` has equal values on such points. Effective descent then gives
`g : U ⊗ P ⟶ G.X` with `(U ◁ s) ≫ g = φ`. It lies over `S` because
`(U ◁ s).left` is an epimorphism. For `a b` with the same image in `P`, lift
that image along `s` to `q` over an epimorphism `p`, and form `a'` and `b'`
as above. Then, after precomposition with `p`,

```
g(a) g(b)⁻¹ = ξ(a₁, r q) f(q) f(q)⁻¹ ξ(b₁, r q)⁻¹ = ξ(a₁, r q) ξ(r q, b₁) = ξ(a₁, b₁),
```

where `a₁` and `b₁` are the first coordinates of `p ≫ a` and `p ≫ b`. The
inversion `ξ(y, x) = ξ(x, y)⁻¹` is the private `toFun_swap`, from the cocycle
identity and `toFun_self`.

*Base change.* Let `f₀` trivialize `ξ.baseChange b V r`, and set
`f = baseChangePointsEquiv b G V f₀`. Take `x y : Z ⟶ (Over.map b).obj V` with
`x.left ≫ V.hom = y.left ≫ V.hom`. View `Z.left` over `S'` through
`x.left ≫ V.hom`; this gives `Z₀`, and `x`, `y` become morphisms
`x₀ y₀ : Z₀ ⟶ V` over `S'`. The identity of `Z.left` gives a morphism
`e : Z ⟶ (Over.map b).obj Z₀` with `e ≫ (Over.map b).map x₀ = x` and
`e ≫ (Over.map b).map y₀ = y`. Apply the multiplicative and natural bijection
`baseChangePointsEquiv` to the trivialization identity at `x₀, y₀`. Then
precompose with `e`, and use the naturality of `ξ`.

## Provenance

Internal. These are elementary descent manipulations for Čech cocycles along
fpqc morphisms, implemented with Mathlib's effective-epimorphism descent for
quasi-compact, flat and surjective morphisms of schemes. They follow the
pattern of `Langlands.GroupScheme.CocycleDescent` and
`Cocycle.IsTrivial.of_refine` in `Langlands.GroupScheme.CocycleRefinement`.
`Cocycle.baseChange` is the restriction of a cocycle to a cover of a base
change, through the pullback adjunction on points from
`Langlands.AbelianScheme.KernelBaseChange`. The module is used in
`Langlands.GroupScheme.SimplyConnected.LocalUnramifiedSplittingReduction`. It
proves no cohomology vanishing.
