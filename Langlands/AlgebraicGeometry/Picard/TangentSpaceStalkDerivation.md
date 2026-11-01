# The tangent module at a rational point as derivations of the stalk

Author: Worker 254.

Module `Langlands.AlgebraicGeometry.Picard.TangentSpaceStalkDerivation`.

Let `k` be a field, `Y : Over (Spec k)` a scheme over `k`, and
`e : Over.mk (𝟙 (Spec k)) ⟶ Y` a section, that is, a `k`-rational point.
Write `R = O_{Y, e(closedPoint k)}` for the actual stalk. This module gives a
`k`-linear equivalence

```lean
tangentSpaceAtPointDerivationEquiv Y e :
  letI := stalkAlgebraOver Y.hom (e.left (IsLocalRing.closedPoint k))
  letI := (rationalStalkAugmentation Y.hom e.left (isRationalPoint_left Y e)).toRingHom.toAlgebra
  Langlands.Scheme.tangentSpaceAtPoint Y e ≃ₗ[k] Derivation k R k
```

between the published sheaf-theoretic tangent module and Mathlib's
`k`-derivations `R → k`. The structures on the right are exactly those of the
published `Langlands.AlgebraicGeometry.Picard.StalkTangent`:

- the base algebra is `stalkAlgebraOver Y.hom`;
- `R` acts on `k` through the rational augmentation
  `rationalStalkAugmentation`, whose underlying ring map is
  `Scheme.stalkClosedPointTo e.left`.

So the equivalence composes directly with
`rationalStalkDerivationTangentEquiv` from
`Langlands.AlgebraicGeometry.Picard.StalkDerivationTangent`. On the left, the
`k`-structure is the `ModuleCat` structure of `tangentSpaceAtPoint`.

This is a reusable bridge requested by the tangent/H1 route coordination
(Workers 432 and 509). The proof of `FieldPointTangentLocalRegularityStatement`
does not use it.

## Declarations

- `stalkAlgebraOver_algebraMap p z c`: the algebra map of
  `stalkAlgebraOver p z` sends `c` to
  `germ_⊤ (p.appTop ((ΓSpecIso k).inv c))`. The proof cancels the iso
  `(ΓSpecIso R).inv` in Mathlib's `ΓSpecIso_inv_naturality`, then uses
  `Spec.map_preimage` and `Scheme.fromSpecStalk_appTop`.
- `isRationalPoint_left Y e`: `IsRationalPoint Y.hom e.left`, which is `Over.w e`.
- Abbreviations:
  - `basePoint` is the closed point of `Spec k`;
  - `closedStalkEquiv` is Mathlib's `stalkClosedPointIso k` as a ring
    isomorphism from the closed-point stalk of `Spec k` to `k`;
  - `pointEval Y e = closedStalkEquiv ∘ e.left.stalkMap basePoint`. This has
    the same underlying map as `Scheme.stalkClosedPointTo e.left`.
- `closedStalkEquiv_germ` and `pointEval_baseMap`: the base sections
  correspond to `k` through `ΓSpecIso`. These follow from Mathlib's
  `germ_stalkClosedPointIso_hom` and, from
  `Langlands.AlgebraicGeometry.SectionTangentDerivations`, `stalkMap_baseMap`.
- `derivationsLinearEquiv Y e` is a `k`-linear equivalence
  `derivations (baseMap Y.hom e.left basePoint) (pointEval Y e) ≃ₗ[k]
  Derivation k R k`.
  - `k`-linearity of a point derivation uses `stalkAlgebraOver_algebraMap`:
    the algebra map lands in the image of `baseMap`, where point derivations
    vanish, and `pointEval` sends it back to `c`.
  - The Leibniz rules match because `a • m = pointEval a * m`. This comes from
    `rationalStalkAugmentation_toRingHom`.
  - Conversely, a Mathlib derivation vanishes on `baseMap` through
    `Derivation.map_algebraMap`.
- `tangentDerivationsLinearEquiv Y e` is a `k`-linear equivalence
  `tangentSpaceAtPoint Y e ≃ₗ[k] derivations (baseMap Y.hom e.left basePoint)
  (pointEval Y e)`. It composes `SectionPoint.tangentDerivationEquiv` with
  `derivationsCongr closedStalkEquiv`.
  - Additivity comes from `tangentDerivationEquiv_add`.
  - Linearity comes from `tangentDerivationEquiv_smul`,
    `derivationsCongr_smul` and `closedStalkEquiv_germ`. The scalar `c` acts on
    the tangent module as `(ΓSpecIso k).inv c`, and on the derivations as `c`.
- `tangentSpaceAtPointDerivationEquiv Y e` is the composite of the two linear
  equivalences.
- `tangentSpaceAtPointDerivationEquiv_germ` is the evaluation formula. For
  `t`, an open `U ∋ e(pt)` and `a ∈ Γ(Y, U)`, the derivation attached to `t`
  sends the germ of `a` to
  `closedStalkEquiv (germ_pt (sectionEquiv e.left U (tangentEval Y e t U a)))`.
  Here `tangentEval Y e t U a ∈ Γ(e_* O_{Spec k}, U)` is the value on `d a` of
  the morphism `Ω_{Y/k} ⟶ e_* O_{Spec k}` adjoint to `t`, and `sectionEquiv`
  (from `SectionTangentDerivations`) reads it as a section over `e⁻¹ U`.

## Provenance

The construction is derived and internal. Mathematically this is the Stacks
Project lemma with Tag 0B2D (`varieties-lemma-tangent-space-cotangent-space`),
in derivation form at a rational point. The source is registered as
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, `varieties.tex`,
lines 3013–3056. The tangent module there is defined by
dual numbers, and the lemma identifies it with `Hom_{O_{X,x}}(Ω_{X/S,x}, κ(x))`.
Here the published tangent module is sheaf-theoretic, and the identification
is proved through `Langlands.AlgebraicGeometry.SectionTangentDerivations`. No
dual-number construction is made in this module.

## Imports

- `Langlands.AlgebraicGeometry.SectionTangentDerivations` (published,
  unchanged);
- `Langlands.AlgebraicGeometry.Picard.StalkTangent` (published, unchanged);
- `Mathlib.AlgebraicGeometry.Stalk`;
- `Mathlib.RingTheory.Derivation.Basic`.

No Library file is changed. The Picard proofs `2eb8161a`, `9cd303c4`, `e689d392`
and `4ef972f8` are not used.
