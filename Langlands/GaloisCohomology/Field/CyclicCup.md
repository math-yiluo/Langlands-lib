# Cup products of characters with units

`Langlands/GaloisCohomology/Field/CyclicCup.lean`, namespace `Langlands.GaloisCohomology`.

For a Galois extension `L/K`, a continuous character `χ : Gal(L/K) → ℚ/ℤ` and a unit `a ∈ Kˣ`,
the class `χ ∪ a ∈ H²(Gal(L/K), Lˣ)` is the cup product of the image of `χ` in `H²(Gal(L/K), ℤ)`
(through the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`) with `a ∈ H⁰(Gal(L/K), Lˣ)`. It vanishes
iff `a` is a norm from the cyclic extension cut out by `χ`. For a quadratic extension `Ω/F` this
gives an injective "invariant" `H²(Gal(Ω/F), Ωˣ) → ℚ/ℤ` with values in `{0, 1/2}`, under the
hypothesis that the product of two non-norms is a norm. These are the field-theoretic parts of
the source's cyclic cup product files; the group-theoretic parts are in
`Langlands/Cohomology/Profinite/Cyclic/`.

## Declarations

Characters and units.

- `unitsInvariant K L a`: a unit of `K` as a Galois-invariant element of `Lˣ` (over `ℤ`,
  `unitsModuleZ`), with `coe_unitsInvariant`.
- `galCupClass K L χ a ∈ H²(Gal(L/K), Lˣ)` (over `ℤ`): the cup product of the character class of
  `χ` with `a` (`cupCharClassProf`).
- `unitsModule_inflation_two_injective`, `unitsModuleZ_inflation_two_injective`: inflation from a
  finite quotient `Gal(L/K)/U` to `H²(Gal(L/K), Lˣ)` is injective (over `ULift ℤ` and over `ℤ`).
- `coe_norm_quotientToInvariants_unitsModuleZ`: the norm of `Gal(L/K)/U` on `(Lˣ)^U` is the field
  norm of `L^U/K`.
- `exists_coboundary_charCocycle_smul_iff_exists_norm`: the norm criterion on cocycles, with no
  coefficient ring: the `2`-cocycle `(g, h) ↦ c_χ(g, h) • a` with values in `Lˣ` (`c_χ` the integer
  cocycle `GroupCoh.charCocycle`) is the coboundary of a locally constant function
  `Gal(L/K) → Lˣ` iff `a` is a norm from the fixed field of the kernel of `χ`. Proof: on the finite
  cyclic quotient by the kernel of `χ`, in the cohomology of `unitsModule`, the cocycle is a
  coboundary exactly on norms (`GroupCoh.smul_norm_mem_coboundaries₂`,
  `GroupCoh.exists_norm_eq_of_mem_coboundaries₂`), and inflation is injective in degree `2`.
- `galCupClass_eq_zero_iff`, `galCupClass_eq_zero_iff_of_isSepClosure`: `χ ∪ a = 0` iff `a` is a
  norm from the fixed field of the kernel of `χ`. Proof: `χ ∪ a` is the class of that cocycle
  (`exists_cocycle_cupCharClassProf`), and a class of `H²` vanishes iff its cocycle is the coboundary
  of a locally constant function (`cohomologyπ_two_eq_zero_iff`).

Finite extensions.

- `coe_toMul_norm_unitsModuleZ`, `unitsInvariant_mem_normRangeInvariants_iff` (an invariant unit
  is in the Library's norm image `Langlands.Tate.normImage` iff it is a field norm),
  `exists_unitsInvariant_eq`, `unitsInvariant_mul`.
- `galCupClass_eq_zero_of_mem_range_norm`, `galCupClass_eq_zero_iff_of_injective` (for an injective
  character, `χ ∪ a = 0` iff `a` is a norm).

Quadratic extensions.

- `quadraticInvFun` (`0` on `0`, `1/2` elsewhere; `quadraticInvFun_zero`,
  `quadraticInvFun_of_ne_zero`), `quadraticInvFun_galCupClass` (its value on `χ ∪ a` is `χ(g)`
  for `g` trivial iff `a` is a norm).
- `card_gal_le_two`, `quadraticChar` (the character of order `≤ 2` of a quadratic extension,
  `quadraticChar_injective`).
- `quadraticInv h2 hN : H²(Gal(Ω/F), Ωˣ) →+ ℚ/ℤ` (additive when the product of two non-norms is a
  norm, `hN`), `quadraticInv_apply`, `quadraticInv_injective`, `quadraticInv_galCupClass`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`: the sections
"Galois" of `src/GroundTheory/ProfiniteCohomology/CyclicCupGaloisDefs.lean` and
`src/GroundTheory/ProfiniteCohomology/CyclicCupBrauer.lean`, and the sections "Quadratic",
"QuadraticInv" and "QuadraticHom" of
`src/GroundTheory/ProfiniteCohomology/LocalClassFormation/CupSymbolReal.lean` (whose name is
misleading: it is about any Galois extension of degree at most two). The repository has no
licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`).

Names are the source's, with `galUnits` → `unitsModule`, `galUnitsZ` → `unitsModuleZ`. The
source's `normRangeInvariants` is the Library's `Langlands.Tate.normImage` (through
`GroupCoh.mem_normRangeInvariants_iff`). The two lemmas `QZ.mk_half_ne_zero`,
`QZ.mk_half_add_mk_half` of the same source section are in
`Langlands/Cohomology/Profinite/Characters.lean`, and `cupCharClassProf_zero` (from the source's
`LocalClassFormation/CupSymbol.lean`, a statement about any group) is in
`Langlands/Cohomology/Profinite/Cyclic/Profinite.lean`. As in the source, the character classes
live in `H²(G, ℤ)` over `ℤ`; this cohomology exists for groups in universe `0` only, so `galCupClass`
and the statements about it are for fields in `Type`. `unitsInvariant`, `coe_unitsInvariant`,
`unitsModule_inflation_two_injective`, `coe_norm_quotientToInvariants_unitsModuleZ` and
`exists_coboundary_charCocycle_smul_iff_exists_norm` are for fields in any universe `u`.
`galCupClass_eq_zero_iff` has the source's statement; its proof, from
`exists_cocycle_cupCharClassProf` and `exists_coboundary_charCocycle_smul_iff_exists_norm`, is not the
source's.

## References

- J.-P. Serre, *Local Fields* (Springer GTM 67, 1979; translation of *Corps locaux*), chapter XIV,
  §1, Propositions 1 and 2 and Corollary 1, p. 204 (`(χ, b) = b.δχ ∈ H²(G, K_s^*)`; it vanishes iff
  `b` is a norm from the cyclic extension `L_χ/K`). Serre works with the Galois group of a separable
  closure.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VII, §2, Proposition (7.2.12), p. 385 (for a local field,
  `χ((a, k)) = inv(a ∪ δχ)`).
