# Cup products of characters with Kummer classes

`Langlands/GaloisCohomology/Local/Duality/KummerCup.lean`, namespaces
`Langlands.ProfiniteCohomology` (the Bockstein sequence, any profinite group),
`Langlands.GaloisCohomology` and `Langlands.GaloisCohomology.Local`.

For an open subgroup `U` of `Gal(Ksep/K)` with fixed field `E`, a character `χ : U → ℤ/n` and a unit
`a ∈ Eˣ`, the cup product of `χ ∈ H¹(U, ℤ/n)` with the Kummer class `δa ∈ H¹(U, μ_n)` vanishes in
`H²(U, μ_n)` exactly when `a` is a norm from the fixed field of the kernel of `χ`. The cup product is
compared, through the injection `H²(U, μ_n) → H²(U, Ksepˣ)`, with the cup product of the Bockstein
`δχ ∈ H²(U, ℤ)` (from `0 → ℤ → ℤ → ℤ/n → 0`) with `a ∈ H⁰(U, Ksepˣ)`, whose standard cocycle
`(g, h) ↦ c_χ(g, h) • a` is a coboundary exactly when `a` is a norm (the norm criterion on cocycles
of the field layer, `exists_coboundary_charCocycle_smul_iff_exists_norm`).

## Declarations

The cochain criteria in low degrees used here (`cochainOf_d_one_apply`,
`cohomologyπ_two_eq_zero_iff`, `cohomologyπ_one_eq_zero_iff_of_trivial`, `cocyclesOneOfHom`, …;
any topological group) are in `Langlands.Cohomology.Profinite.Cyclic.Profinite`.

The Bockstein sequence (`G : Type u`):

- `intRepTriv G` (trivial `ℤ`), `zmodReductionAdd`, `zmodReduction` (`ℤ → ℤ/n`,
  `zmodReduction_hom_apply`), `bockSeq G n` (`0 → ℤ → ℤ → ℤ/n → 0`), `bockSeq_shortExact`.
- `intMulPairing G A : ℤ ⊗ A → A` (`intMulPairing_tmul`).
- `zmodCocycleHom z` (the homomorphism `G → ℤ/n` of a 1-cocycle; `zmodCocycleHom_mul`,
  `isLocallyConstant_zmodCocycleHom`), `bockInt χ g h` (the carry `⌊(χ(g) + χ(h))/n⌋`;
  `natCast_mul_bockInt`), `charCocycle_eq_bockInt` (the source's cyclic character cocycle is the
  carry).
- `exists_cocycle_cupPairing_δ_bockSeq`: an explicit cocycle for `δχ ∪ a`.

Fields:

- `bockSeq_kummerSequenceRes_compat₁₂`, `bockSeq_kummerSequenceRes_compat₂₃`: the pairings of the
  Bockstein and Kummer sequences are compatible; `ne_zero_of_natCast_ne_zero'`;
  `cohomologyMap_cupPairing_zmodMul_δ`: `χ ∪ δa` maps to `δχ ∪ a` in `H²(U, Ksepˣ)`.
- `unitsInvariantOpen W a` (a unit of the fixed field as an invariant of `Ksepˣ`;
  `coe_unitsInvariantOpen`, `exists_unitsInvariantOpen_eq`, `unitsInvariantOpen_pow`),
  `δ_unitsInvariantOpen_pow_eq_zero` (`n`-th powers have trivial Kummer class).
- `exists_coboundary_iff_of_mulEquiv`: coboundaries correspond under a topological isomorphism of
  groups.

Local fields:

- `exists_δ_unitsInvariantOpen_eq hn U y`: every class of `H¹(U, μ_n)` is a Kummer class.
- `openChar n U z`: the character of `Gal(Ksep/E)` with values in `ℚ/ℤ` of a 1-cocycle of `U`
  (`openChar_apply`); `res_unitsModule_ρ_galFixedFieldEquivOpen`.
- `cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a`: `χ ∪ δa = 0` iff `a` is a norm from the
  fixed field of `ker χ`.
- `zmodCocycleHom_eq_zero_of_charKer_eq_top`, `exists_cocycle_charKer_eq`: characters with trivial
  kernel vanish, and every character `Gal(Ksep/E) → ℤ/n` with open kernel comes from a cocycle.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/LocalTateDuality/Bockstein.lean` and `KummerCup.lean`, with
the names `galUnits` → `unitsModule`, `galUnitsZ` → `unitsModuleZ`, `galRootsOfUnity` →
`rootsOfUnityModule`, `kummerSeqOpen` → `kummerSequenceRes`, `H0Iso` → `zeroIso`,
`res_galUnits_ρ_galFixedFieldEquivOpen` → `res_unitsModule_ρ_galFixedFieldEquivOpen`. The
repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

The source's `H¹` vanishing over open subgroups (from its local class formation) is the field
layer's Hilbert 90 here; the norm criterion of the source's cyclic cup product is the field layer's
`exists_coboundary_charCocycle_smul_iff_exists_norm` (the criterion of `galCupClass` on cocycles).
The theorems are for groups and fields in any universe `u` (`K Ksep : Type u`), with coefficients
`ULift.{u} ℤ`; the source states them in universe `0`.

## References

- J.-P. Serre, *Local Fields*, chapter XIV, §1, Proposition 2 and Corollary 1 (the cup product of a
  character with `b` vanishes iff `b` is a norm from the extension cut out by the character), p.
  204, and Proposition 3, p. 205.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §2 (the local
  duality theorem), pp. 378–390.
