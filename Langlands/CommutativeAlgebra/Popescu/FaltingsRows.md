# The Jacobi–Zariski rows for `ℤ → A → κ(A)` in characteristic `p`

Faltings' proof of Stacks, More on Algebra, Proposition 15.36.1 (07E5), (2) ⇒ (4), uses the
exact rows `0 → 𝔪/𝔪² → Ω_{A/𝔽_p} ⊗ K → Ω_{K/𝔽_p} → 0`. Their left exactness comes from
`H₁(L_{K/𝔽_p}) = 0` (Stacks, Algebra, Proposition 10.158.9). Lean works with `Ω_{−/ℤ}`, which is
the same module in characteristic `p`. The declarations below supply these facts and a naturality
statement for `δ`. All of them live in `Langlands.CommutativeAlgebra.Popescu.Faltings`.

Several lemmas take the `ℤ`-algebra structures as instance arguments
(`[Algebra ℤ R] [Algebra ℤ T] [@IsScalarTower ℤ R T …]`) instead of using the default
`Ring.toIntAlgebra`. Rings such as residue fields of localizations carry other, propositionally
equal, `ℤ`-algebra instances, and this makes the lemmas apply to them.

## `map_int_eq_zero_of_charP`

For a ring `R` of characteristic `p` and a field `T` over `R`, the map
`H₁(L_{T/ℤ}) → H₁(L_{T/R})` is zero. It factors through `H₁(L_{T/𝔽_p})`
(`Extension.H1Cotangent.map_comp_apply`, `map_eq`). That group vanishes because `𝔽_p = ZMod p` is
perfect (`FieldH1.subsingleton_h1Cotangent_of_perfectField`).

## `δ_injective_of_charP`

In the same setting, the connecting map `δ : H₁(L_{T/R}) → T ⊗_R Ω_{R/ℤ}` is injective. Its kernel
is the image of the zero map above (`exact_map_δ`).

## `mapBaseChange_surjective_of_surjective`

If `R → T` is surjective, then `T ⊗_R Ω_{R/ℤ} → Ω_{T/ℤ}` is surjective. In that case
`Ω_{T/R} = 0`, and the Jacobi–Zariski sequence is exact at `Ω_{T/ℤ}`.

## `defaultHom_base_toAlgHom`, `baseMap`, `δAux_map`, `aeval_map_eq_zero`, `δ_map_base`

Naturality of `δ` in the middle ring. For `S → S'` over `R` and an `S'`-algebra `T`:
- `defaultHom_base_toAlgHom`: the default hom of canonical presentations `S[T] → S'[T]` maps the
  coefficients along `S → S'`. The proof is by induction on polynomials.
- `baseMap R S S' T`: the `T`-linear map `T ⊗_S Ω_{S/R} → T ⊗_{S'} Ω_{S'/R}`,
  `t ⊗ ω ↦ t ⊗ ω|_{S'}`.
- `δAux_map`: `δAux` for `S'` of the coefficient-mapped polynomial equals `baseMap` of `δAux` for
  `S`. The proof is by induction on polynomials (`δAux_C`, `δAux_mul`, `δAux_X`).
- `aeval_map_eq_zero`: mapping coefficients preserves vanishing at the tautological point.
- `δ_map_base`: `δ_{S'}(H₁(map)(x)) = baseMap(δ_S x)` for `x ∈ H₁(L_{T/S})`. An element of `H₁` is
  the class of some `g ∈ S[T]`. `H₁(map)` sends it to the class of the mapped polynomial, and
  `δ_eq_δAux` together with `δAux_map` conclude.
