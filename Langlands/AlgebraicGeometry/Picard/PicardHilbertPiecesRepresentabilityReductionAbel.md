# The Abel map of an open of the divisor scheme

Authors: Worker 22.

Worker 22 wrote this helper module for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It is part of the proof
of `PicardHilbertPiecesRepresentabilityReductionStatement`; the main theorem
and the full route are in `PicardHilbertPiecesRepresentabilityReductionProof.md`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`.

Provenance: internal. It formalizes the Abel map `Z → P` of Kleiman's proof
of Theorem 4.8 (*The Picard scheme*, p.30), on an open `Z₀` of the divisor
scheme, and the computation of the opens `U` along it.

## Contents

- `cancel_add_right`: `a + c = b + c + e → a = b + e` in a Picard group.
- `hU2'`: the base-change hypothesis `HU2` for a morphism `h : T' ⟶ T` of
  `S`-schemes whose structure map is not literally `h ≫ s`.
- `Zo d Z₀`: an open `Z₀ ⊆ D` as the object `Z₀.ι ≫ d` of `Over S`.
- `abelMap … Z₀`: the Abel map
  `uliftYoneda.obj (Zo d Z₀) ⟶ RelativePicard.classSheafPresheaf f`. It
  corresponds by Yoneda (`uliftYonedaEquiv`) to the fppf class of the
  universal Abel class `ab (Zo d Z₀) Z₀.ι`. `abelMap_app` computes its value on
  a point `x : T ⟶ Zo d Z₀`. It is the fppf class of `ab T (x.left ≫ Z₀.ι)`,
  that is, of the pullback of `L_W` along `x`.
- `linsys_class`: `linsys_classify` for the twist `M = L(m)`. A divisor
  `W_Λ` with `O(W_Λ) ≅ pr^* L(m) ⊗ pr^* N_Λ` is classified by a point
  `y : Λ ⟶ D` with `pt y = l^*[L] + pr^*[N_Λ]`. The twists `m • cP` on both
  sides cancel.
- `tr f T L`: the module `σ_T^* L` on `X ×_S T`, where
  `σ_T = (relativeSpaceSymmetry f T).inv`. This is the transport used in the
  conclusion of `PicardHilbertPiecesRepresentabilityStatement`.
  `isInvertible_tr`, `icl_tr` and `pb_relativeSpace_map` relate its class to
  `L.classOf`.
- `class_open`: let `f` satisfy the hypotheses of S-cls, and let `T`, `T'` and
  `D` be locally noetherian. Let `k : T' ⟶ T`, let `L` be a line bundle on
  `T ×_S X`, and let `y : T'.left ⟶ D`. Suppose that the fppf class of
  `k^* L` equals the fppf class of `ab T' y`. Then
  `k⁻¹ U(T, σ_T^* L) = y⁻¹ U(D, L_W)`. The proof rewrites the left side with
  `hU2'`. S-cls in group form (`scl_sym_eq_iff`) gives `n` with
  `[k^* σ_T^* L] = pt y + pr^* n`. Then `U_eq_preimage` applies.
