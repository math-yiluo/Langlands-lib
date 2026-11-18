# Finiteness and geometric reducedness of the normalization model

Worker 6.

- `finite_geometricallyReduced_of_cover`: let `X` over `Spec R` be flat, quasi-compact and
  separated, and let `R'` be a DVR with an `R`-algebra structure. Write `A` for the global sections
  of the finite affine cover `coverOver X`. Suppose the integral closure `B` of `R' ⊗[R] A` in
  `(R' ⊗[R] A) ⊗[R'] FractionRing R'` is a finite module and `F ⊗[R'] B` is reduced for every field
  `F : Type u`; these are the conclusions of `DvrAffineReducedFibreStatement`. Then, for the base
  change `X'` of `X` along `Spec R' → Spec R`, the normalization map `map X'` is finite and
  `source X'` is geometrically reduced over `Spec R'`.

Proof outline:

1. `Z'' := Spec (R' ⊗[R] A)` is the base change of the cover (`isPullback_spec_tensor`). The induced
   map `p'' : Z'' → X'` is a base change of the covering map, hence smooth, surjective and
   quasi-compact.
2. `φ := pullback.snd (genericι X') p''` is the generic fibre inclusion of `Z''`; its sections are a
   localization of `Γ(Z'')` away from the uniformizer. `IntegralClosureTransfer.transfer` moves the
   hypotheses on `B` to the integral closure of `Γ(Z'')` in these sections. Then
   `finite_geometricallyReduced_normalization` gives finiteness and geometric reducedness of the
   normalization of `φ`.
3. Normalization commutes with the smooth base change `p''` (Mathlib `normalizationPullback`).
   Local finite type descends along the surjective, flat, quasi-compact `p''` (Mathlib flat descent
   instance). With integrality this gives finiteness of `map X'`. Reducedness of fibres descends
   along the flat surjective base change of `p''` (Library
   `GeometricallyReducedOfAlgClosedProof.isReduced_of_flat_of_surjective`).
