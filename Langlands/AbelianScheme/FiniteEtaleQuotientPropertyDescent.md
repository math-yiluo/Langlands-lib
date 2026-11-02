# Abelian-scheme properties descend along finite étale surjections of the source

`Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent`.

Authors: Worker 1224.

This module shows that separatedness, smoothness, properness and geometrically
connected fibres pass from a composite `q ≫ g` to `g` when `q` is a finite étale
surjection and the base is locally Noetherian. It then uses this to make an abelian
scheme from a commutative group scheme that receives a finite étale surjection over `S`
from an abelian scheme. It supports the quotient `A → A/K` of an abelian scheme by a
finite étale subgroup in the proof of
`Langlands.AbelianScheme.FiniteEtaleQuotientExistenceStatement`.

## Provenance

The separatedness lemma is part (4) of Stacks Project Lemma 09MQ
(`lemma-image-universally-closed-separated` in `morphisms.tex`, Section "Proper
morphisms"). The registered source
`stacks-affine-morphisms-relative-vanishing-a04446e5` holds `morphisms.tex` at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, where the label is at line 10114. The Lean
proof follows the Stacks proof.

The other declarations are derived infrastructure for this task. They combine the
separatedness lemma with existing results: Mathlib's `UniversallyClosed.of_comp_surjective`
and `IsProper` API, the Library's
`Langlands.AlgebraicGeometry.FiniteFlatSourceDescent.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective`,
and the smooth source descent
`AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`
ported from the Anthropic FLT formalisation in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`.
The descent of geometric connectedness is a short direct argument written for this
module.

## Declarations

All schemes are in one universe `u`. Except for `ofFiniteEtaleSurjective` and its simp
lemma, the declarations are in `Langlands.AbelianScheme.FiniteEtaleQuotientPropertyDescent`.

### `isSeparated_of_comp_of_surjective_of_universallyClosed`

Let `p : X ⟶ Y` be surjective and universally closed, and let `g : Y ⟶ S` be such that
`p ≫ g` is separated. Then `g` is separated.

Proof. Let `π : X ×_S X ⟶ Y ×_S Y` be the map `p × p`, built as the pullback lift of
`fst ≫ p` and `snd ≫ p`. It is universally closed by `MorphismProperty.pullbackMap`, as
`p × p` is a composite of two base changes of `p`. Composing with the diagonals gives
`Δ_{p ≫ g} ≫ π = p ≫ Δ_g`, checked on the two pullback projections. Since `p` is
surjective, the range of `Δ_g` equals the image under `π` of the range of `Δ_{p ≫ g}`.
That range is closed because `Δ_{p ≫ g}` is a closed immersion, and `π` is a closed
map, so the range of `Δ_g` is closed. A diagonal is always an immersion
(`IsPreimmersion`), so `IsClosedImmersion.of_isPreimmersion` makes `Δ_g` a closed
immersion.

### `geometricallyConnected_of_comp_of_surjective`

Let `p : X ⟶ Y` be surjective, and let `g : Y ⟶ S` be such that `p ≫ g` has
geometrically connected fibres (Mathlib's `GeometricallyConnected`). Then so does `g`.

Proof. Take a field `K`, a point `y : Spec K ⟶ S` and a pullback square of `g` along
`y` with corner `Z`. Pasting it with the pullback of `p` along `Z ⟶ Y` shows that
`X ×_Y Z` is a pullback of `p ≫ g` along `y`, so it is connected. Its projection to `Z`
is surjective as a base change of `p`, so `Z` is connected as a continuous surjective
image. The option `backward.isDefEq.respectTransparency.types false` is set for this
declaration only.

### `smooth_isProper_geometricallyConnected_of_comp`

Let `S` be locally Noetherian, let `q : X ⟶ Y` be finite, étale and surjective, and let
`g : Y ⟶ S` be such that `q ≫ g` is smooth, proper and has geometrically connected
fibres. Then `g` is smooth, proper and has geometrically connected fibres. No
separatedness or group structure is assumed on `g`.

Proof.

1. `g` is locally of finite type by the Library's finite flat source descent, and so
   locally of finite presentation because `S` is locally Noetherian.
2. `g` is universally closed by `UniversallyClosed.of_comp_surjective`.
3. `g` is separated by the first lemma, applied to `q`, which is finite and so
   universally closed.
4. These give properness through `isProper_iff`.
5. Smoothness comes from the ported FLT smooth source descent, since `q` is smooth,
   surjective and quasi-compact.
6. Geometric connectedness comes from the second lemma.

### `Langlands.AbelianScheme.ofFiniteEtaleSurjective`

Let `S` be locally Noetherian. Given an abelian scheme `A`, a commutative group scheme
`B` over `S`, and a scheme morphism `q : A.X.left ⟶ B.X.left` with
`q ≫ B.X.hom = A.X.hom` that is finite, étale and surjective,
`ofFiniteEtaleSurjective A B q hq` is the abelian scheme with underlying commutative
group scheme `B`. The morphism `q` need not respect the group laws. The fields `smooth`,
`proper` and `geometricallyConnected` come from the previous lemma, after rewriting
`A.X.hom` as `q ≫ B.X.hom`.

The simp lemma `ofFiniteEtaleSurjective_toCommGroupScheme` records that the underlying
commutative group scheme is `B`. It holds by `rfl`.
