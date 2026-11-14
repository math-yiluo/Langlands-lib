# The flat proper relation of linear equivalence on an open of the divisor scheme

Authors: Worker 22.

Worker 22 wrote this helper module for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705). It is part of the proof
of `PicardHilbertPiecesRepresentabilityReductionStatement`; the main theorem
and the full route are in `PicardHilbertPiecesRepresentabilityReductionProof.md`.
All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction`.

Provenance: internal. It formalizes Kleiman's identification
`T' ×_P Z = LinSys_{L'}` (*The Picard scheme*, proof of Theorem 4.8, p.30),
which makes the relation `Z ×_P Z` a linear system over `Z`. The linear
system comes from the hypothesis `ProperFlatIntegralLinearSystemStatement`
(Kleiman Theorem 3.13).

## Contents

- `add_add_neg_aux`: `a + c = a + b + c + -b` in a Picard group.
- `HU3`: the third hypothesis on the opens in
  `PicardHilbertPiecesRepresentabilityStatement`, as a proposition. On a
  whole piece (`U T s L c n = ⊤`), `H¹` of `L(n)` vanishes and `H⁰` does not on
  every fibre.
- `flat_of_top`: if `U T s L c m = ⊤`, then the linear system
  `l : Λ ⟶ T` of `L(m)` from (b) is flat, locally of finite presentation and
  surjective. This is the last clause of (b), fed with `HU3`.
- `exists_relation`: let `Z₀ = U D d L_W c m`. There are `R : Over S` and
  `sR, tR : R ⟶ Zo d Z₀` with four properties:
  1. `sR` is flat;
  2. `sR` is proper;
  3. `sR` and `tR` have the same composite with the Abel map;
  4. for every locally noetherian `T`, two points `x, y : T ⟶ Z₀` with the
     same Abel class come from a unique `r : T ⟶ R` with `r ≫ sR = x` and
     `r ≫ tR = y`.

## Proof of `exists_relation`

Let `L₀` be the pullback of `L_W` to `X ×_S Z₀`. Apply (b) over the locally
noetherian scheme `Z₀` to the family `X ×_S Z₀ ⟶ Z₀`, which is proper, flat
and geometrically integral by base change, and to `L₀(m)`. This gives
`l : Λ ⟶ Z₀`, `W_Λ` and `N_Λ`.

- `l` is proper by (b). By `hU2'`, `U Z₀ L₀ c m` is the preimage of `Z₀`
  under `Z₀.ι`, that is, `⊤`. So `l` is flat and locally of finite
  presentation by `flat_of_top`, and `Λ` is locally noetherian.
- `linsys_class` gives `y₀ : Λ ⟶ D` classifying `W_Λ`, with
  `pt y₀ = pt (l ≫ ι) + pr^*[N_Λ]`. By `hU2'` and `U_eq_preimage`,
  `y₀⁻¹ Z₀ = l⁻¹ ι⁻¹ Z₀ = ⊤`. So `y₀` factors as `t' ≫ ι` through `Z₀`
  (`IsOpenImmersion.lift`).
- Put `R = Λ` over `S`, `sR = l`, `tR = t'`. Property 3 is S-cls in group
  form (`scl_sym_eq_iff`) applied to the class equation for `y₀`.
- Property 4. Let `x, y : T ⟶ Z₀` have the same Abel class. S-cls gives `n`
  with `pt x = pt y + pr^* n`. Let `E` be the divisor `y^* W`, moved to
  `(X ×_S Z₀) ×_{Z₀} T` along `bcIso`. It is relative effective Cartier by
  (a) and `flat_comap`. By `dcl_comap_mapX`, `icl_twist_pt` and the class
  equation, `O(E) ≅ x^* L₀(m) ⊗ pr^* N'` with `[N'] = -n`. The universal
  property of `Λ` in (b) gives `k : T ⟶ Λ` with `k ≫ l = x` and `k^* W_Λ = E`.
  Then `k ≫ y₀` and `y` pull `W` back to the same divisor (`bcIso_hom_map`
  and the classifying equation of `y₀`). So `k ≫ t' = y` by the uniqueness in
  (a) (`classifies_eq`) and since `ι` is a mono. The uniqueness of `k` is the
  uniqueness clause of (b).
