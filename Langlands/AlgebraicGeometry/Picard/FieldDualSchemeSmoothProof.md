# Smoothness of a chosen dual parameter scheme over a field: proof

Module `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSmoothProof` proves the
published proposition `Langlands.AbelianScheme.FieldDualSchemeSmoothStatement` by the
theorem

```text
Langlands.AbelianScheme.fieldDualSchemeSmooth : FieldDualSchemeSmoothStatement.{u}
```

whose type is exactly the statement, for an arbitrary universe `u`. For every field
`k : Type u`, every `A : AbelianScheme (Spec k)` and every `hA : HasDualScheme A`, it gives
`Smooth (dualScheme A hA).hom`. No hypothesis is added: there is no perfectness or
algebraic-closedness assumption on `k`, no ample bundle, projectivity, coherence,
inverse-bundle or finiteness input, and no representability premise. The statement's
Lean/Markdown pair and its imports are unchanged. The parent geometry target
`FieldDualSchemeGeometryStatement` is not used.

## Proof

Fix `k`, `A` and `hA`, and write `D = dualScheme A hA`.

1. **Algebraic closure.** Let `Ω = AlgebraicClosure k` (also in universe `u`) and
   `b : Spec Ω ⟶ Spec k` the morphism induced by `algebraMap k Ω`. Let
   `A' = (baseChange b).obj A`, the actual pulled-back abelian scheme over `Spec Ω`.
2. **The base-changed dual.** The published `hasDualScheme_baseChange`, applied to the
   published theorem `picardZeroUniversalBaseChange`, gives `hA' : HasDualScheme A'`. The
   published `dualSchemeBaseChangeIso` gives an isomorphism in `Over (Spec Ω)` from the
   pullback `(Over.pullback b).obj D` to `dualScheme A' hA'`. It is the unique isomorphism
   compatible with the Poincaré families, obtained from the universal property on all
   test schemes, including nonreduced ones. It is not a bijection of geometric points.
   Its underlying morphism `e` is an isomorphism of schemes satisfying
   `e ≫ (dualScheme A' hA').hom = pullback.snd D.hom b`.
3. **The algebraically closed case.** `A'.X` is connected because `A'` is geometrically
   connected over a field (Mathlib's
   `GeometricallyConnected.connectedSpace_of_subsingleton`). The published
   `smoothConnectedRelativeDimension` therefore gives some `g` with
   `A'.HasRelativeDimension g`. The published unconditional theorem
   `algClosedFieldDualSchemeRelativeDimension` (module
   `Picard.AlgClosedFieldDualSchemeRelativeDimensionProof`) then gives
   `SmoothOfRelativeDimension g (dualScheme A' hA').hom`, so this morphism is smooth.
4. **Transport along the isomorphism.** Because `e` is an isomorphism, the identity in
   step 2 shows that `pullback.snd D.hom b` is smooth.
5. **Descent.** The morphism `b` is surjective, since `Spec k` has a single point.
   It is flat by `Flat.SpecMap_iff` and `RingHom.Flat.of_isField`. It is quasi-compact
   because it is a morphism of affine schemes. Smoothness descends along surjective,
   flat, quasi-compact morphisms. Mathlib's
   `MorphismProperty.of_pullback_snd_of_descendsAlong` therefore gives `Smooth D.hom`.
   This is the same descent instance used in Mathlib's proof of `smooth_of_grpObj`.

The axioms of the theorem are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

The statement's source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(preliminary draft), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Theorem (6.18), printed p.96 (PDF p.100), states that `Pic⁰_{X/k}` is reduced, hence an
abelian variety, of dimension `dim X = dim_k H¹(X, 𝒪_X)`. Its proof uses the finite kernel
`K(L)` of `ϕ_L` for an ample `L`, together with (6.6) and (6.15).

This proof does not repeat that argument over `k`, and it makes no separate comparison
with the source's `Pic⁰`. The source-style argument (an ample bundle, a finite-kernel
Mumford classifier giving the lower bound for the origin stalk dimension, and the tangent
identification with `H¹(A, 𝒪_A)`) is already carried out for the Library's chosen dual over
algebraically closed fields in the published `algClosedFieldDualSchemeRelativeDimension`;
see its Markdown. Here the arbitrary-field case follows from that theorem by two steps:
the canonical scheme isomorphism with the base-changed chosen dual, which comes from
universality on all test schemes, and fpqc descent of smoothness.

## Provenance

Worker 1383 wrote this proof. It replaces Worker 1383's earlier shared assembly draft for
this task, which kept the unproved premise `FieldRigidifiedPicardRepresentabilityStatement`.
That premise is no longer used.
