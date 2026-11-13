# The section lies in the smooth locus, given a local closed embedding into a smooth scheme

Author: Worker 9.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4). It turns the global statement of `Core.lean`
(`exists_smooth_open_of_closedImmersion`) into a pointwise criterion. Near `s` and `e s`, the
morphism must be a closed subscheme of a scheme smooth of relative dimension `n`.

The declaration is in the namespace `Langlands.GroupScheme.ReducedBaseSmooth`, and all schemes
lie in one universe `u`.

## Declaration

`mem_smoothLocus_of_closedImmersion_chart`. Data and hypotheses:

- `S` is a reduced scheme, `q : Y ⟶ S` is locally of finite presentation, `e : S ⟶ Y`
  satisfies `e ≫ q = 𝟙 S`, and `n : ℕ`;
- `U : S.Opens` is an open such that `q.fiberToSpecResidueField t` is
  `SmoothOfRelativeDimension n` for every `t ∈ U`;
- `ιV : V0 ⟶ S` and `ιY : Y0 ⟶ Y` are open immersions, `g : Y0 ⟶ V0` satisfies
  `g ≫ ιV = ιY ≫ q`, and `p0 : Z0 ⟶ V0` is `SmoothOfRelativeDimension n`, quasi-compact and
  quasi-separated;
- `i0 : Y0 ⟶ Z0` is a closed immersion with `i0 ≫ p0 = g`;
- `s ∈ U`, `s` lies in the range of `ιV`, and `e s` lies in the range of `ιY`.

Conclusion: `e s ∈ q.smoothLocus`.

## Provenance

This is an internal lemma with a derived name. It is the localisation step of the route of
`Core.lean`, which does not follow SGA 3's flatness argument.

## Proof

Let `V'` be the open `ιV(V0) ∩ e⁻¹(ιY(Y0)) ∩ U` of `S`; it contains `s`. Lift its inclusion
through `ιV` to `a : V' ⟶ V0` and the restricted section `V' → Y` through `ιY` to
`eT : V' ⟶ Y0` (`IsOpenImmersion.lift`). Since `ιV` is a monomorphism, `eT ≫ g = a`.

Base-change along `a`. Write `p : Z0 ×_{V0} V' ⟶ V'` for the second projection and
`i : Y0 ×_{V0} V' ⟶ Z0 ×_{V0} V'` for the map induced by `i0`. Then `i ≫ p` is the second
projection of `Y0 ×_{V0} V'`, and `i` is a closed immersion (`MorphismProperty.pullbackMap`).
The morphism `p` is smooth of relative dimension `n`, quasi-compact and quasi-separated, since
these properties are stable under base change. The pair `(eT, 𝟙)` defines a section
`eY` of `i ≫ p`.

Let `t ∈ V'`. The residue fibre of `i ≫ p` at `t` is smooth of relative dimension `n`, by two
applications of `smoothOfRelativeDimension_fiber_of_isPullback`. The first uses the pullback
square defining `Y0 ×_{V0} V'`. The second uses the square with `g` and the open immersion
`ιV`, a pullback because `ιV` is a monomorphism (`IsPullback.of_horiz_isIso_mono`). These
reduce the claim to the residue fibre of `ιY ≫ q` at `t`. That fibre is smooth of relative
dimension `n` by `smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion` and the hypothesis
on `U`.

Now `V'` is reduced, being an open subscheme of `S`, so `exists_smooth_open_of_closedImmersion`
gives an open `W` containing the range of `eY` on which `i ≫ p` is smooth. Let
`ψ : W ⟶ Y` be `W ↪ Y0 ×_{V0} V' → Y0 → Y`. Then `ψ ≫ q = (W.ι ≫ i ≫ p) ≫ V'.ι`, which is
smooth. Mathlib's `Scheme.Hom.preimage_smoothLocus_eq` gives
`ψ ⁻¹ᵁ q.smoothLocus = (ψ ≫ q).smoothLocus`, which is everything. Finally `ψ` sends the point
`eY s` of `W` to `e s`, so `e s` lies in the smooth locus of `q`.
