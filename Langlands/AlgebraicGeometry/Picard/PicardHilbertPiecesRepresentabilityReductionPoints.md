# Picard classes and the fppf Picard class sheaf

Authors: Worker 22.

Worker 22 wrote this helper module for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It is part of the proof
of `PicardHilbertPiecesRepresentabilityReductionStatement`; the main theorem
and the full route are in `PicardHilbertPiecesRepresentabilityReductionProof.md`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`.

Provenance: internal. The key lemma `scl_sym_eq_iff` restates the Library
theorem `properFlatIntegralSheafClassTwist`, which proves S-cls (Kleiman,
*The Picard scheme*, Theorem 2.5, p.18 and Exercise 3.11, p.25), in terms of
Picard-group classes on `X ×_S T`.

## Pullbacks of classes

- `isInvertible_pullback`: pullbacks of invertible modules are invertible.
- `pb_id_apply`, `pb_iso_inv_hom`, `pb_iso_hom_inv`, `pb_iso_injective`:
  `Group.pullback` along an isomorphism is a bijection.
- `exists_icl`: every class is `icl N` for an invertible `N`
  (`Group.lineBundleRepresentative`).
- `icl_lineBundleOfIsInvertible`: the definitional unfolding of `icl`.

## The fppf class of a Picard class

Let `f : X ⟶ S` and `T : Over S`, and write `T ×_S X = (relativeSpace f).obj T`.

- `scl f T x`: the image of a class `x ∈ Pic(T ×_S X)` in the fppf Picard
  class sheaf `RelativePicard.classSheafPresheaf f`, via
  `RelativePicard.toClassSheaf`. `sheafClassOf_eq_scl`: for a line bundle
  `L`, `sheafClassOf f T L = scl f T L.classOf`.
- `map_scl`: restriction along `k : T' ⟶ T` is `scl` of the pulled-back
  class. The proof uses `RelativePicard.map_sheafClassOf`.
- `sym f T`: the isomorphism `relativeSpaceSymmetry f T` from `T ×_S X` to
  `X ×_S T`. `sym_hom_fst`, `sym_hom_snd` give its projections.

## S-cls in group form

`scl_sym_eq_iff`: let `f` be proper, flat, locally of finite presentation and
geometrically integral, with a section. For classes `z, z'` on `X ×_S T`,

```
scl f T (sym^* z) = scl f T (sym^* z')  ↔  ∃ n ∈ Pic(T), z = z' + pr_T^* n.
```

The proof chooses line bundles `L`, `L'` with classes `sym^* z`, `sym^* z'`.
S-cls says that `sheafClassOf f T L = sheafClassOf f T L'` if and only if
`L ≅ L' ⊗ g^* N` for an invertible `N` on `T`. Each side is converted with
`icl_eq_iff`, `icl_tensor` and `icl_pullback`. The projection `g` from
`T ×_S X` is identified with `pr_T ∘ sym` (`sym_hom_snd`), and `pb_iso_injective`
removes `sym^*`.
