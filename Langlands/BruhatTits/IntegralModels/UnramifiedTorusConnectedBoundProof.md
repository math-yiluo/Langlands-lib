# Integral points of connected torus models lie in the Iwahori subgroup

`Langlands.BruhatTits.IntegralModels.unramifiedTorusConnectedBound` proves
the unchanged published proposition
`UnramifiedTorusConnectedBoundStatement.{u}` at arbitrary universe `u`.
For every nonarchimedean local field `F`, put `K = inertiaFixedField F`
and `O = fixedFieldIntegers F`. Given an actual affine commutative group
scheme `T` over `Spec K` split by a finite Galois intermediate field `L`
of `SeparableClosure F / K`, every `M : IntegralModel O K T.toGrp`
that is smooth and has geometrically connected fibres satisfies

```text
M.integralPoints ≤
  torusNormIwahori K L (intermediateValuation F L) T.
```

The subgroup on the right is the image of the character-valuation kernel
of `T_L(L)` under the actual norm to `T(K)`. The result holds for each
supplied splitting field `L`; no independence of that choice is needed.

## Implemented proof

The Lean proof applies the published theorem
`unramifiedTorusConnectedBoundAssembly` to three published proofs, in the
order required by `UnramifiedTorusConnectedBoundAssemblyStatement`:

1. `unramifiedTorusBoundedModel` proves
   `UnramifiedTorusBoundedModelStatement`: each affine torus over `K`
   has a smooth model whose integral-point image is its full
   character-valuation kernel.
2. `unramifiedTorusNeutralSurjectivity` proves
   `UnramifiedTorusNeutralSurjectivityStatement`: a scheme-surjective
   homomorphism of affine tori with torus full kernel lifts target neutral
   integral-point images to source neutral integral-point images, for
   supplied smooth models with the full character-kernel point images.
3. `unramifiedTorusNormPresentation` proves
   `UnramifiedTorusNormPresentationStatement`: there is an affine torus
   `S` and a scheme-surjective `q : S → T` with torus full kernel whose
   image of the character-valuation kernel lies in the stated norm subgroup.

The four imported modules are the assembly and these three proof modules.
Every application explicitly uses the same universe `u`. All three
premises are discharged, so the resulting theorem has exactly the
published target, with no additional assumptions.

The assembly chooses the norm presentation and smooth bounded models of
`S` and `T`, then forms their relative identity components. Character
valuations place `M.integralPoints` inside the full target model's point
image. The smooth homomorphism extension theorem extends the generic
identity to a morphism from `M` to that full model. Geometric connectedness
factors this morphism through its relative identity component. Neutral
lifting then places these points in the image under `q` of the source
neutral points. Those points lie in the source full model's point image,
which is the source character-valuation kernel. The norm-presentation
bound gives the desired inclusion. These constructions and their proof
details remain in the imported assembly and its prerequisites.

## Provenance

This module supplies a proof of an existing statement and introduces no
new definitions or statements. Its provenance is composition of the four
named Library theorems above.

The mathematical target is the connected-model consequence of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Corollary B.8.7
and the proof of Proposition B.8.8(3), printed pp. 683–684 / PDF pp. 714–715,
using Remark B.8.5 and Corollary B.8.6, printed pp. 682–683 / PDF pp. 713–714.
The norm subgroup is Definition 2.5.13, printed p. 90 / PDF p. 121.
The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The statement's paired Markdown explains its precise supplied-model scope
and the corrections consulted. The neutral-lifting proof's paired
Markdown explains its Henselian connected-generation route in place of
the source's completion and lft-Néron-model route.
