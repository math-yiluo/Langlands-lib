# Lifting stabilizers of a selected lift to a cover fundamental group

This module fixes a finite étale cover `Y` of `S` and a lift `x` of a point
`s` to `Y`. Every element of the fundamental group at `s` that fixes `x` lifts
to the fundamental group of `Y.obj.left` at `x.left`. The module constructs
this lift and proves that the induced homomorphism sends it back to the given
element. It then characterizes the image of that homomorphism as the
stabilizer of `x`.

All declarations are in the namespace `Langlands.AlgebraicGeometry.FiniteEtale`
and live in universe `u`. They use the existing finite étale category `Cover`,
the fibres `Fiber`, the groups `FundamentalGroup` (natural automorphisms of the
fibre functors `fiberFunctor`) and the action lemma `smul_naturality`, all from
`Langlands.AlgebraicGeometry.FiniteEtale.Definitions`. They also use
`pullbackFunctor`, `pullbackFiberEquiv`, `fundamentalGroup_ext`,
`fundamentalGroupMap` and `fundamentalGroupMap_smul_left` from
`Langlands.AlgebraicGeometry.FiniteEtale.Pullback`, and
`fundamentalGroupMap_fixes_lift` from
`Langlands.AlgebraicGeometry.FiniteEtale.CoverPointStabilizer`. The module
imports `CoverPointStabilizer`, which imports `Pullback`. It introduces no new
axiom, abstract replacement group or supplied equivalence.

## Setting and hypotheses

- `S : Scheme.{u}` is an arbitrary scheme, `Ω : Type u` is an arbitrary field
  and `s : Spec (.of Ω) ⟶ S` is an arbitrary point.
- `hs : ∀ Z : Cover S, Finite (Fiber s Z)` is the finite-fibre witness needed
  to form `FundamentalGroup s hs`.
- `Y : Cover S` is a finite étale cover and `x : Fiber s Y` is a lift of `s`.
  Thus `x.left : Spec (.of Ω) ⟶ Y.obj.left` satisfies
  `x.left ≫ Y.obj.hom = s`, and this equation is `Over.w x`.
- `ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z)` is the finite-fibre
  witness needed to form `FundamentalGroup x.left ht`.

The induced homomorphism is the published
`fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs`, from the group at
`x.left` to the group at `s`. The module assumes no connectedness, no local
noetherianity and no algebraic closure of `Ω`. The finite-fibre witnesses
remain explicit inputs and are never derived. Since they are proofs, the
groups do not depend on which witnesses are supplied.

## Provenance

The provenance is internal. The module adds no literature assertion. It is a
generic prerequisite for the Harris raw-level comparison owned by task
`6eac742d-7f56-403d-8f08-f535a1ca289c`. Every construction is built from the
published finite étale definitions listed above, and every law is proved
below.

For context, `Pullback.md` reports that the source of `fundamentalGroupMap`
also states an isomorphism `π₁(Y, ȳ) ≅ Stab(ȳ)` for an étale covering, and
that this statement is not formalized there. The present module proves only
the image part: the image of the induced homomorphism equals the stabilizer.
It proves nothing about injectivity, and it does not claim the isomorphism.

## Composite covers

For a cover `Z : Cover Y.obj.left`, the composite `Z.obj.hom ≫ Y.obj.hom` is
finite and étale, by Mathlib's composition instances for `IsFinite` and
`Etale`.

- `compCover Y Z : Cover S` is `cover (Z.obj.hom ≫ Y.obj.hom)`, the cover
  `Z → Y → S`. The simp lemmas `compCover_obj_left` and `compCover_obj_hom`
  record its total scheme `Z.obj.left` and structure morphism.
- `compCoverProj Y Z : compCover Y Z ⟶ Y` is the morphism of covers of `S`
  with underlying morphism `Z.obj.hom` (`compCoverProj_hom_left`).
- `compCoverMap Y k : compCover Y Z ⟶ compCover Y Z'` regards a morphism
  `k : Z ⟶ Z'` of covers of `Y.obj.left` as a morphism of covers of `S`. It
  has the same underlying morphism `k.hom.left` (`compCoverMap_hom_left`). The
  over-`S` equation follows from `Over.w k.hom`.
- `compCoverPullbackFst Y W` is defined for a cover `W : Cover S`. It is the
  morphism of covers of `S` from `compCover Y ((pullbackFunctor Y.obj.hom).obj W)`
  to `W`, with underlying first projection `pullback.fst W.obj.hom Y.obj.hom`
  (`compCoverPullbackFst_hom_left`). The source cover is `W ×_S Y → Y → S`.
  The over-`S` equation is `pullback.condition`.

## Lifts over `x` in a composite cover

- `compFiber x Z z : Fiber s (compCover Y Z)` keeps the underlying morphism of
  a lift `z : Fiber x.left Z` (`compFiber_left`). Its over-`S` equation is
  `z.left ≫ Z.obj.hom ≫ Y.obj.hom = x.left ≫ Y.obj.hom = s`.
- `compFiber_comp_proj` proves
  `compFiber x Z z ≫ (compCoverProj Y Z).hom = x`, so these lifts lie over
  `x`.
- `compFiber_comp` proves that `compFiber` is natural:
  `compFiber x Z' (z ≫ k.hom) = compFiber x Z z ≫ (compCoverMap Y k).hom`.
  This holds by definition.
- Conversely, `fiberOfCompFiber x Z w hw : Fiber x.left Z` is defined for
  `w : Fiber s (compCover Y Z)` with `hw : w ≫ (compCoverProj Y Z).hom = x`.
  It has the same underlying morphism as `w` (`fiberOfCompFiber_left`). Its
  over-`Y.obj.left` equation is the underlying-morphism component of `hw`.

So `Fiber x.left Z` is identified with the lifts of `s` to the composite cover
that lie over `x`.

## The stabilizer action on fibres over `x.left`

Fix `g : FundamentalGroup s hs` with `hg : g • x = x`.

- `smul_compFiber_comp_proj` proves
  `(g • compFiber x Z z) ≫ (compCoverProj Y Z).hom = x`. By `smul_naturality`
  for `compCoverProj Y Z`, the left side equals
  `g • (compFiber x Z z ≫ (compCoverProj Y Z).hom)`. By `compFiber_comp_proj`
  this is `g • x`, and `hg` turns it into `x`. Hence `g` preserves the lifts
  over `x`.
- `stabilizerLiftFun g hg Z z` is
  `fiberOfCompFiber x Z (g • compFiber x Z z) (smul_compFiber_comp_proj g hg Z z)`.
  It is the restriction of the action of `g` on `Fiber s (compCover Y Z)` to
  the lifts over `x`.
- `compFiber_stabilizerLiftFun` proves
  `compFiber x Z (stabilizerLiftFun g hg Z z) = g • compFiber x Z z`.
- `stabilizerLiftFun_mul` and `stabilizerLiftFun_one` prove that restriction
  respects products and the identity. Both follow from
  `compFiber_stabilizerLiftFun` together with `mul_smul` and `one_smul`.
- `stabilizerLiftEquiv g hg Z : Fiber x.left Z ≃ Fiber x.left Z` has forward
  map `stabilizerLiftFun g hg Z`. Its inverse is `stabilizerLiftFun g⁻¹ _ Z`,
  where `g⁻¹ • x = x` comes from `hg` by `inv_smul_eq_iff`. The two inverse
  laws reduce, through `compFiber_stabilizerLiftFun`, to `inv_smul_smul` and
  `smul_inv_smul` on the composite fibre.
- `stabilizerLiftFun_comp` proves naturality:
  `stabilizerLiftFun g hg Z' (z ≫ k.hom) = stabilizerLiftFun g hg Z z ≫ k.hom`
  for `k : Z ⟶ Z'`. On underlying morphisms, `compFiber_comp` rewrites the
  left side as the action of `g` on `compFiber x Z z ≫ (compCoverMap Y k).hom`.
  Then `smul_naturality` for `compCoverMap Y k` moves `g` inside.

## The lift

`stabilizerLift s hs Y x ht g hg : FundamentalGroup x.left ht` is the natural
automorphism of `fiberFunctor x.left ht` built by `NatIso.ofComponents`. Its
component at `Z` is the bijection `stabilizerLiftEquiv g hg Z`, packaged as an
isomorphism of finite types with `ObjectProperty.isoMk`. Naturality is
`stabilizerLiftFun_comp`. Its action is recorded by two lemmas that hold by
definition:

- `stabilizerLift_smul` (a simp lemma):
  `stabilizerLift s hs Y x ht g hg • z = stabilizerLiftFun g hg Z z`;
- `stabilizerLift_smul_left`:
  `(stabilizerLift s hs Y x ht g hg • z).left = (g • compFiber x Z z).left`.

## The lifting equation

`fundamentalGroupMap_stabilizerLift s hs Y x ht g hg` proves

```lean
fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs
  (stabilizerLift s hs Y x ht g hg) = g.
```

By `fundamentalGroup_ext`, it suffices to compare the actions on each
`w : Fiber s W` for every `W : Cover S`, using underlying morphisms. Let
`p := pullbackFiberEquiv Y.obj.hom x.left s (Over.w x) W w` be the
corresponding lift into the pulled-back cover `W ×_S Y → Y`. Then
`fundamentalGroupMap_smul_left` and `stabilizerLift_smul_left` turn the left
side into
`(g • compFiber x _ p).left ≫ pullback.fst W.obj.hom Y.obj.hom`.
The lift `compFiber x _ p` maps to `w` under `compCoverPullbackFst Y W`, by
`pullbackFiberEquiv_apply_left_fst`. So `smul_naturality` for this morphism
identifies the right side `(g • w).left` with the same expression.

## The homomorphism on the stabilizer and the image

- `stabilizerLiftHom s hs Y x ht` is the group homomorphism
  `MulAction.stabilizer (FundamentalGroup s hs) x →* FundamentalGroup x.left ht`
  with `g ↦ stabilizerLift s hs Y x ht g g.2` (`stabilizerLiftHom_apply`). Its
  multiplicativity and unit laws are proved fibrewise with
  `fundamentalGroup_ext` from `stabilizerLiftFun_mul` and
  `stabilizerLiftFun_one`.
- `fundamentalGroupMap_comp_stabilizerLiftHom` states that composing it with
  the induced homomorphism gives the inclusion of the stabilizer subgroup. It
  is a pointwise application of `fundamentalGroupMap_stabilizerLift`.
- `exists_fundamentalGroupMap_eq_iff s hs Y x ht g` proves the image
  characterization

  ```lean
  (∃ σ : FundamentalGroup x.left ht,
    fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs σ = g) ↔ g • x = x.
  ```

  The forward direction is the published `fundamentalGroupMap_fixes_lift`.
  The reverse direction uses the witness `stabilizerLift s hs Y x ht g hg` and
  `fundamentalGroupMap_stabilizerLift`.
- `range_fundamentalGroupMap` restates this as the subgroup equality
  `(fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs).range =
  MulAction.stabilizer (FundamentalGroup s hs) x`.

## Scope

The image characterization identifies the image with the stabilizer of `x`. It
does not assert that the induced homomorphism is surjective onto the whole
group at `s`, and it says nothing about injectivity. The lift is a specific
construction. The module does not claim that it is the only preimage of `g`.
