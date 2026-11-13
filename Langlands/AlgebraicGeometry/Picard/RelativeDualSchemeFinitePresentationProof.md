# Proof: local finite presentation of the chosen dual parameter scheme

Author: Worker 1407.

Module `Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationProof` proves

```text
theorem relativeDualSchemeFinitePresentation :
    RelativeDualSchemeFinitePresentationStatement.{u}
```

The statement says: for every `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`, every
`A : AbelianScheme S` and every `hA : HasDualScheme A`, the morphism `(dualScheme A hA).hom` is
locally of finite presentation. No hypotheses are added. The proof does not use
quasi-separatedness of `S`.

## Route

The statement's Markdown cites Lan's thesis, Theorem 1.3.2.3, and describes two possible routes.
This proof uses neither the comparison with `Pic⁰_e(A/S)` nor any representability theorem.
It is a direct, internal limit argument that uses only the universal property recorded in
`HasDualScheme`:

1. Over an affine base `Spec R`, `dualScheme_locallyOfFinitePresentation_affine` (module
   `Langlands.AlgebraicGeometry.Picard.DualSchemeQuotientFactorization`) proves local finite
   presentation for every ring `R`. It combines three inputs:
   - the published local finite type result `dualScheme_locallyOfFiniteType`;
   - descent of Picard-zero rigidified families from `Spec (D ⧸ I)` to `Spec (D ⧸ J)` with `J`
     finitely generated (`LineBundleQuotientDescent`, using the ported FLT directed-limit descent
     of invertible sheaves);
   - a retract criterion for finite presentation (`QuotientFactorizationFinitePresentation`).
2. The general case reduces to the affine case by base change.

## Proof of the theorem

Let `𝒰 = S.affineOpenCover`, with charts `b : Spec (𝒰.X i) ⟶ S`. Local finite presentation is
local on the target (`HasRingHomProperty.instIsZariskiLocalAtTarget`). By
`IsZariskiLocalAtTarget.of_openCover`, it suffices to show for each `i` that
`pullback.snd (dualScheme A hA).hom b` is locally of finite presentation.

The published theorem `picardZeroUniversalBaseChange` and `hasDualScheme_baseChange` give
`hA₁ : HasDualScheme ((baseChange b).obj A)`. The published `dualSchemeBaseChangeIso` gives an
isomorphism `e : (Over.pullback b).obj (dualScheme A hA) ≅ dualScheme ((baseChange b).obj A) hA₁`
in `Over (Spec (𝒰.X i))`. Its underlying morphism `e.hom.left` is an isomorphism of schemes. The
triangle `Over.w e.hom` writes `pullback.snd (dualScheme A hA).hom b` as `e.hom.left` followed by
the structure morphism of `dualScheme ((baseChange b).obj A) hA₁`. That structure morphism is
locally of finite presentation by `dualScheme_locallyOfFinitePresentation_affine` with
`R = 𝒰.X i`. An isomorphism is an open immersion, hence locally of finite presentation.
Composites of morphisms locally of finite presentation are locally of finite presentation. This
proves the claim for every chart, and so the theorem.

## Helper modules

- `Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleQuotientDescent`
- `Langlands.AlgebraicGeometry.QuotientFactorizationFinitePresentation`
- `Langlands.AlgebraicGeometry.Picard.DualSchemeQuotientFactorization`

Each module's Markdown documents its results. The kernel check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
