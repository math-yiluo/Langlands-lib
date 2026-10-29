# Spreading ample existence to a finite intermediate field

This module proves
`Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingStatement` as the
theorem `Langlands.AlgebraicGeometry.Picard.algebraicExtensionAmpleExistenceSpreading`, for an
arbitrary universe `u` and with no further hypotheses. Let `K` be a field, `Ω / K` an
algebraic extension, and `p : X ⟶ Spec K` proper. If the base change
`X_Ω = pullback p (Spec.map (algebraMap K Ω))` has an ample line bundle, then for some
finite-dimensional intermediate field `K ⊆ E ⊆ Ω`, the base change
`X_E = pullback p (Spec.map (algebraMap K E))` has an ample line bundle. The extension does not
have to be separable.

The proof follows steps 1-4 of the proof of Stacks Project Lemma 33.15.1 (tag 0BDB), as the
task contract describes. It does not use the general limit theory of finitely presented module
sheaves (Stacks, Limits, Lemmas 32.10.3 and 32.4.15). The finite-stage line bundle is built
directly by these helper modules:

- `Langlands.AlgebraicGeometry.Picard.LineBundleDescent`: a line bundle on `Y` glued inside
  `π_* F` from compatible sections of a module sheaf `F` on `Y'`, for `π : Y' ⟶ Y` injective on
  sections and surjective (`exists_lineBundle_of_descent`);
- `Langlands.AlgebraicGeometry.Picard.LineBundleLimitSpreading`: sections of a module sheaf on a
  cofiltered limit of schemes with affine transitions, with affine trivialization opens that
  cover, spread to a line bundle at some finite stage (`exists_lineBundle_of_isLimit`);
- `Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit`: `X_Ω` is the limit of
  the cofiltered diagram `E ↦ X_E` over finite intermediate fields, and the hypotheses of
  `exists_lineBundle_of_isLimit` hold for it.

It also uses these published results:

- `Langlands.SchemeModule.trivializationOpen_mapIso` (`AmpleIsoProof`): an isomorphism of module
  sheaves preserves trivialization opens of global sections;
- `Langlands.SchemeModule.trivializationOpen_sectionPow` (`PositiveSectionPowerGenerationLocusProof`):
  for a line bundle `L`, a global section `s` and `n > 0`, the trivialization open of
  `s^n` in `L^{⊗ n}` equals that of `s`;
- `tensorPow_isLocallyFreeRankOne` (`TensorRankOneProof`) and
  `tensorPowMulIso : (P^{⊗ n})^{⊗ k} ≅ P^{⊗ (n * k)}` (`TensorPowerIsomorphisms`).

## `exists_trivializationOpen_eq_of_dvd`

Take a line bundle `M` on `X`, a positive integer `N`, a divisor `n` of `N` and a global
section `s` of `M^{⊗ n}`. Then some global section `t` of `M^{⊗ N}` has the same
trivialization open as `s`.

Proof as implemented. Write `N = n * k`, so `k > 0`. The module `M^{⊗ n}` is a line bundle by
`tensorPow_isLocallyFreeRankOne`. Let `t` be the image of the power
`sectionPow (M^{⊗ n}) s k` under `tensorPowMulIso M n k`. By `trivializationOpen_mapIso`, the
open of `t` is the open of `s^k`. By `trivializationOpen_sectionPow`, applied to the line
bundle `M^{⊗ n}`, that open is the open of `s`.

## Main theorem `algebraicExtensionAmpleExistenceSpreading`

Proof as implemented. Let `p : X ⟶ Spec K` be proper, `Ω / K` algebraic, and `M` an ample
line bundle on `X_Ω`.

1. **Common power.** Ampleness gives a quasi-compact `X_Ω`. It also gives, for each point
   `x`, an exponent `n x ≥ 1` and a section `s x` of `M^{⊗ n x}` whose trivialization open
   contains `x` and is affine. Finitely many of these opens, indexed by a finset `T`, cover
   `X_Ω` (`IsCompact.elim_finite_subcover`). Let `N` be the product of the `n x` over `T`.
   Then `N > 0`, and each `n x` divides `N` (`Finset.dvd_prod_of_mem`). By
   `exists_trivializationOpen_eq_of_dvd`, each `s x` gives a section `t x` of `M^{⊗ N}` with
   the same open. So the opens of the `t x` cover `X_Ω` and are affine.
2. **Spreading.** By `isLimitBaseChangeCone`, `X_Ω` is the limit of the cofiltered diagram
   `E ↦ X_E` over finite intermediate fields. Its transition maps are affine. Since `p` is
   proper, it is quasi-compact and quasi-separated, so every `X_E` is quasi-compact and
   quasi-separated. Each projection `X_Ω ⟶ X_E` is injective on sections over every open
   (`baseChangeCone_π_app_app_injective`) and surjective (`baseChangeCone_π_app_surjective`).
   Apply `exists_lineBundle_of_isLimit` to `F = M^{⊗ N}` and the sections `t x`. It gives a
   finite intermediate field `E`, a line bundle `L` on `X_E`, and global sections `s' j` of `L`
   whose trivialization opens cover `X_E` and are affine. The bundle `L` is an actual module
   sheaf on `X_E`, constructed as a subsheaf of a pushforward in `LineBundleDescent`.
3. **Ampleness at exponent one.** `X_E` is quasi-compact. Each point `x` of `X_E` lies in the
   open of some `s' j`. Take the power `sectionPow L (s' j) 1`, a global section of
   `L^{⊗ 1}`. By `trivializationOpen_sectionPow` with exponent `1`, its trivialization open
   (the open `L.sectionOpen` of the definition of `IsAmple`) equals the open of `s' j`. So this
   whole generation open contains `x` and is affine. Hence `L` is ample on
   `X_E = pullback p (Spec.map (algebraMap K E))`, with `E` finite-dimensional over `K`.
