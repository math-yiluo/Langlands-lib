# Translation of Jacquet functionals by exterior powers

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetTranslationProof`.

## Result

`Langlands.Archimedean.complexJacquetTranslation : ComplexJacquetTranslationStatement`.

The statement `ComplexJacquetTranslationStatement` is defined in
`ComplexStandardJacquetExponentRoute` and is not changed here. It says: let
`ℓ ≠ 0` be a Jacquet functional on `X(d)` (the `U(n)`-finite principal series of
`d : Fin n → ComplexCharacterData`) with exponents `(a, b)`, let `k ≤ n` and `ε = ±1`. Then there
are a `k`-element set `S ⊆ Fin n`, characters `d'` that agree with `d` off `S` and have weight
`l(d_j) + ε` and exponent `t(d_j) + 1/2` on `S`, and a nonzero Jacquet functional `ℓ'` on
`X(d')` with exponents `a_j + λ_j` and `b_j + i ε λ_j`, where `λ` is the indicator of the last
`k` positions `{j | n ≤ j + k}`.

The theorem has no hypotheses beyond those of the statement and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Idea

`X(d) ⊗ Λ^k` (holomorphic for `ε = 1`, antiholomorphic for `ε = -1`) is modelled by tuples
`(F_T)` of functions of `X(d)` indexed by `k`-subsets `T` (module
`ComplexJacquetTranslationLift`). The functional `F ↦ ℓ(F_{T₀})`, `T₀` the last `k` positions,
is a Jacquet functional on tuples with exponents shifted by `λ` (the lowest weight of `Λ^k`).
Every tuple is a sum of lifts of functions of the shifted principal series `X(d + e_S)`, and the
lifts from `S` have vanishing components at all `U ≠ S` with `wt U ≥ wt S`. Restricting the
functional to lifts from a suitable `S` gives `ℓ'`. This replaces the filtration of
`X(d) ⊗ Λ^k` by principal series that a textbook proof would use.

## Proof

Fix `anti` (`false` for `ε = 1`, `true` for `ε = -1`) and write `T₀ = lowSub n k hk`.

1. **`coe_lie`.** The action of `1 ⊗ X` on `X(d)` is the right derivative `R(X)`
   (`kFiniteLie_one_tmul_apply_coe`).
2. **`ellS`.** For `S : Sub n k`, `ellS S h = ℓ((lift S h)_{T₀})` is a linear functional on
   `X(shiftChar anti d S)` (`lift_add`, `lift_smul`).
3. **`ell_decomp`.** For a tuple `G` and functions `h_S ∈ X(shiftChar anti d S)` that agree with
   the components `piS anti G S` on `U(n)`: `ℓ(G_{T₀}) = ∑_S ellS S h_S` (from `eq_sum_lift`).
4. **`exists_ellS_ne_zero`.** Some `ellS S` is nonzero: pick `f` with `ℓ f ≠ 0`, apply
   `ell_decomp` to the tuple equal to `f` at `T₀` and `0` elsewhere, with components from
   `exists_component`.
5. **Minimal choice.** Among the `S` with `ellS S ≠ 0`, choose one of minimal weight `wt S`
   (`Finset.exists_min_image`); then `ellS U = 0` whenever `wt U < wt S`.
6. **`key`.** For `X` upper triangular and `h ∈ X(shiftChar anti d S)`:
   `ellS S (R(X) h) = ℓ(R(X)(lift S h)_{T₀}) + (∑_{r ∈ T₀} phi anti X r r) · ellS S h`.
   Let `F = lift S h` and `G = act anti X F`. By `piS_act`, the components of `G` are the right
   derivatives of those of `F`; by `piS_lift` these are `R(X) h` at `S` and `0` at every
   `U ≠ S` with `wt U ≥ wt S`. With components `h_U` from `exists_component`, this gives
   `h_S = R(X) h` and `h_U = 0` for those `U` (`eq_of_eq_unitary`), while `ellS U = 0` for
   `wt U < wt S`. So `ell_decomp` gives `ℓ(G_{T₀}) = ellS S (R(X) h)`. On the other hand,
   `G_{T₀} = R(X) F_{T₀} + ∑_{T'} Dco anti T₀ T' X · F_{T'} = R(X) F_{T₀} + c F_{T₀}` with
   `c = ∑_{r ∈ T₀} phi anti X r r` (`Dco_low`).
7. **`exists_translate`.** `ellS S` is a Jacquet functional on `X(shiftChar anti d S)` with the
   shifted exponents:
   - for strictly upper triangular `X`, the diagonal of `X` vanishes, so `c = 0`, and `ℓ`
     kills `R(X)(lift S h)_{T₀}`;
   - for `X = E_jj` (`Matrix.single j j 1`), `c = λ_j` (`phi_single_diag`, `mem_lowSub`) and
     `ℓ(R(E_jj) v) = a_j ℓ(v)`, so the exponent is `a_j + λ_j`;
   - for `X = i E_jj`, `c = λ_j · fac anti i`, which is `i λ_j` (holomorphic) or `-i λ_j`
     (antiholomorphic), that is `i ε λ_j`; so the exponent is `b_j + i ε λ_j`.
8. **`complexJacquetTranslation`.** Split `ε = 1` (`anti = false`) and `ε = -1`
   (`anti = true`); take `S`, `d' = shiftChar anti d S` (`shiftChar_weight`,
   `shiftChar_exponent`; `S.card = k` is `S.prop`) and `ℓ' = ellS S`.

## Provenance

Internal. The statement is one of the three ingredients of the route
`ComplexStandardJacquetExponentRoute` to `ComplexStandardJacquetExponentStatement`. The idea
(tensoring a principal series with a finite-dimensional representation and following the lowest
weight) is the standard translation principle for Harish-Chandra modules; the tuple model, the
lifts and the minimal-weight argument are the implementation chosen here.
