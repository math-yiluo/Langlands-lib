# The local Artin symbol of a cyclotomic extension and the abstract invariants

This module proves the local identity of the reciprocity proof for cyclic cyclotomic
extensions (task fb66219f). Fix a family `I` of local invariant maps satisfying the
class-formation axioms and the arithmetic normalization. On the local carry classes of a
cyclotomic extension, `I` agrees with the explicit cyclotomic Artin symbol.

All declarations are in the namespace
`Langlands.ClassField.Global.LocalSymbolIdentity`.

## Setting

- `L / F` is a Galois extension of number fields in `Type u`.
- `ζ ∈ L` is a primitive `m`-th root of unity.
- `hinj` says that `IsPrimitiveRoot.autToPow F : Gal(L/F) → (ℤ/m)ˣ` is injective. This holds
  when `L = F(ζ)`.
- `v` is a finite place of `F` and `u` a place of `L` above it.

Some results also assume `Gal(L/F)` commutative (`hcomm`), as for cyclotomic extensions.

## Definitions

- `placeAboveRational v` is `v` regarded as a place above its rational place
  `rationalPlace v`.
- `artinSymbol hζ hinj v : (v.adicCompletion F)ˣ →* Gal(L/F)` is the local Artin symbol. It
  sends `b` to the unique `σ` with `autToPow σ = normSymbolAt m (rationalPlace v) v b`, the
  explicit cyclotomic symbol of the local norm `N_{F_v/ℚ_p}(b)`. Such a `σ` exists by the
  Artin–Tate norm theorem `normSymbolAt_mem_galoisImage` with `K = F`, and it is unique by
  `hinj`. `autToPow_artinSymbol` states the defining property.
- `zmodClass e : ZMod e →+ ℚ/ℤ` is `z ↦ z.val / e`. It is additive by the carry identity
  `cyclicCarry_rational`.

## Theorems

- `autToPow_restrictScalars`: `autToPow` is unchanged by restricting scalars from an
  intermediate field `K` to `F`.
- `artinSymbol_norm_mem` (norms lie in the norm group): let `H ≤ Gal(L/F)` and let `b` be in
  the completion of the fixed field `L^H` at the place below `u`. The Artin symbol of the
  local norm of `b` lies in `H`. This applies the Artin–Tate norm theorem to `K = L^H`, with
  the compatibility of the symbol with local norms (`normSymbolAt_localNorm`). The Galois
  image of `Gal(L/L^H)` is `H` (`fixingSubgroup_fixedField`).
- `exists_nat_of_nsmul_eq_zero`: an element of `ℚ/ℤ` killed by `e > 0` is `k / e` for some
  `0 ≤ k < e`.
- `normal_of_comm`: every subgroup of a commutative Galois group is normal.
- `relative_cyclicClass_uniformizer` (the θ-trick). Let `U = L^{H_U}` have completion `U_w`
  with an arithmetic unramified coordinate `χ_U : Gal(U_w/F_v) ≃ ℤ/e`
  (`IsArithmeticUnramifiedCoordinate`). Let `π ∈ F_vˣ` have `ord π = 1`, and assume the Artin
  symbol of `π` restricts on `U` to the arithmetic Frobenius:
  `decompositionHom (χ_U⁻¹(1)) = (artinSymbol π)|_U`. Then for every character
  `ψ : Gal(L/F) → ℤ/e`,

  `I.relative (padicField v) L_u (cyclicClass F_v L_u (ψ ∘ decompositionHom v u) π) = ψ(Art π).val / e`.

  The proof runs as follows.
  1. The class of `ψ` is killed by `e`, so its invariant is `k/e` with `0 ≤ k < e`.
  2. The inflated coordinate `χ' = χ_U ∘ res` has invariant `1/e`, by
     `InflationCompatibility`, `relativeInflation_cyclicClass` and `ArithmeticNormalization`.
  3. Hence `θ = ψ · χ'^{-k}` has invariant `0` (bilinearity of carry classes).
  4. Let `H` be the global image of `ker θ`, and `K₁ = L^H`. Then `θ` factors injectively
     through `Gal((K₁)_{w₁}/F_v)` (`restrictNormal_eq_one_iff`, `exists_injective_factor`).
  5. Its class there also has invariant `0` (inflation). `I` is injective
     (`RelativeImages`), so the class vanishes, and `π` is a local norm from `(K₁)_{w₁}`
     (`cyclicClass_eq_zero_iff_of_injective`).
  6. By `artinSymbol_norm_mem`, `Art π ∈ H`, i.e. `Art π = decompositionHom σ₀` with
     `θ σ₀ = 1`.
  7. The restriction of `σ₀` to `U_w` is `χ_U⁻¹(1)`, by the Frobenius hypothesis and the
     injectivity of decomposition maps. So `ψ(Art π) = k`.
- `relative_cyclicClass` (the local identity): if the Frobenius hypothesis holds for every
  `π` with `ord π = 1`, then for every `a ∈ F_vˣ`

  `I.relative (padicField v) L_u (cyclicClass F_v L_u (ψ ∘ decompositionHom v u) a) = ψ(Art a).val / e`.

  Both sides are additive in `a`. Write `a = c · π₀^{n−1}`, where `π₀` has order `1` and
  `c = a π₀^{−n} π₀` also has order `1`. The previous theorem applies to `c` and `π₀`.

## Hypotheses still to be discharged

The unramified data (`H_U`, the coordinate `χ_U` and the Frobenius hypothesis) are
hypotheses here. For `L = F(ζ_m)` with `q^d − 1 ∣ m` (`q = |k_v|`), they come from
`U = F(ζ_{q^d − 1})`. The cyclotomic symbol acts on `ζ_{q^d−1}` as `ζ ↦ ζ^q` on elements of
order one. This is supplied by a separate unit.

## Sources and provenance

The identification of the local norm residue symbol with the explicit cyclotomic symbol is
Artin–Tate, Chapter VII §2, Theorem 5 (printed p.41, PDF p.50). Their argument compares
both maps on an unramified field, through norm groups. The θ-trick here is an adaptation of
that argument to an abstract family `I` given only by the class-formation axioms. It uses
injectivity, inflation and the arithmetic normalization in place of a constructed local
reciprocity map. Provenance is derived. The formulation through `cyclicClass`,
`decompositionHom` and fixed fields of the global cyclotomic field is internal.
