# Square-summability of unitary Whittaker functions on the mirabolic torus

Authors: Worker 3657 (proof) and Worker 828 (verification and
submission). Module
`Langlands.Representation.RankinSelberg.UnitaryWhittakerTorusSum`, namespace
`Langlands.RankinSelberg.UnitaryGeneric`. Helper module of the proof candidate for
Task 6387 (`UnitaryGenericLPolynomialNonvanishingStatement`). It imports the
published module `Langlands.Representation.RankinSelberg.UnitaryCellMasses` and,
through it, `UnitaryCellBound`. It changes no published file.

## Main theorem

```lean
theorem summable_density_mul_norm_sq (k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (hadm : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) (hunit : IsUnitarizable ρ)
    (ℓ : glFunctionals ψ (k + 1) ρ) (v : V) (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ) :
    Summable (fun lam : Fin (k + 1) → ℤ =>
      QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam *
        ‖ℓ.val (ρ (Iwasawa.torus ϖ (Fin.snoc lam 0)) v)‖ ^ 2)
```

`F` is a p-adic field with its canonical topology. `density ϖ lam` is the
published inverse modulus `δ(ϖ^lam)⁻¹ = ∏_{i<j} |ϖ^(lam_i)/ϖ^(lam_j)|⁻¹`, where
`δ` is the modulus character of the upper Borel subgroup of `GL_(k+1)`, and `Iwasawa.torus ϖ (Fin.snoc lam 0)` is
`diag(ϖ^lam, 1)`. In words: for an irreducible admissible unitarizable `ρ`, every
Whittaker function `W(g) = ℓ(ρ(g) v)` satisfies

`Σ_{lam ∈ ℤ^(k+1)} δ(ϖ^lam)⁻¹ |W(diag(ϖ^lam, 1))|² < ∞`.

This is the torus-lattice form of the square-integrability of `W` on `N \ P`
(`P` the mirabolic subgroup).

## Declarations

- `density_mul_haar_le_quotientMeasure`: let `K'` be a measurable subset of
  `GL_(k+1)(O)` and `Y` a set of `N \ GL_(k+1)` containing the classes of
  `ϖ^lam x` for `x ∈ K'`. Then `δ(ϖ^lam)⁻¹ · haar(K') ≤ μ(Y)` for the published
  `unipotentQuotientHaar`. The published torus decomposition
  `QuotientTorusEnvelope.quotientMeasure_eq_sum_torus` writes `μ` as a sum over
  `lam` of `δ(ϖ^lam)⁻¹` times the pushforward of Haar measure on `GL_(k+1)(O)`;
  keep the `lam` term. This generalizes the published
  `UnramifiedUnitary.density_le_quotientMeasure` from `K' = GL_(k+1)(O)` to any
  measurable `K'`.
- `torusElement ϖ k lam = levi(ϖ^lam) ∈ P_(k+1)`; `torusElement_val`: its matrix
  is `diag(ϖ^lam, 1)` (published `levi_torus`).
- `leviIntegralSet k K = {x ∈ GL_(k+1)(O) : levi x ∈ K}`; it is open
  (`isOpen_leviIntegralSet`, from `Mirabolic.continuous_levi`) and contains `1`.
- `exists_mirabolicMeasure_torus`: a measure `ν` on `N \ P_(k+1)` that is finite
  on compacts, right invariant and positive and finite on compact-open orbits,
  such that for every open subgroup `K` of `P_(k+1)` the orbit of
  `torusElement lam · K · torusElement lam⁻¹` has mass at least
  `δ(ϖ^lam)⁻¹ · haar(leviIntegralSet k K)`. The measure is the published
  `unipotentQuotientHaar` transported along
  `MirabolicQuotient.quotientHomeomorph`, as in the published
  `UnramifiedUnitary.exists_mirabolicMeasure` (single rows only); the mass
  bound is the torus decomposition argument above.
- `torusElement_ne`: distinct exponents give distinct cells `N t K` for
  `K ≤ GL_(k+2)(O) ∩ P`, by the published Iwasawa uniqueness
  `Iwasawa.iwasawa_exponent_unique`.

## Proof of the main theorem

If `ℓ = 0` every term is zero. Otherwise:

1. `v` is smooth (admissibility), so an open subgroup `H` of `GL_(k+2)` fixes it.
   Put `K = (H ∩ P) ∩ (GL_(k+2)(O) ∩ P)`, a compact open subgroup of `P`
   fixing `v`.
2. The published `padicCellBound` (Jacquet–Shalika I, Proposition (1.3), in the
   algebraic form proved by Worker 1797) gives `C` such that for every finite
   family of pairwise distinct cells `N g_i K`,
   `Σ_i ν(orbit of g_i K g_i⁻¹) |ℓ(ρ(g_i) v)|² ≤ C`, for the measure `ν` of
   `exists_mirabolicMeasure_torus`.
3. Index the exponents by an injection `ℤ^(k+1) → ℕ` and take
   `g = torusElement lam`. For a finite set `u` of exponents the cells are
   distinct (`torusElement_ne`), and the masses are at least
   `δ(ϖ^lam)⁻¹ c` with `c = haar(leviIntegralSet k K) > 0` (open nonempty set)
   and `c < ∞` (inside the compact `GL_(k+1)(O)`).
4. Hence `Σ_{lam ∈ u} δ(ϖ^lam)⁻¹ |W(diag(ϖ^lam,1))|² ≤ C / c` for every finite
   `u`, and `summable_of_sum_le` concludes.

## Provenance

- H. Jacquet and J. A. Shalika, *On Euler products and the classification of
  automorphic representations I*, Amer. J. Math. 103 (1981), 499–558,
  registered as
  `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`
  (printed page = PDF page + 498): Proposition (1.3) and its proof,
  pp.505–507 (PDF 7–9); the bound
  `∫_{N\P} |W|²(pg) dp ≤ ‖A‖² ‖v‖²`, display (1.3.1), p.507 (PDF 9).
- The source works with the Hilbert-space completion. The Library's
  `padicCellBound` (module `UnitaryCellBound`) replaces it by finite sums over
  cells, and this module turns those finite sums into the torus-lattice series.
  The route generalizes the published `UnramifiedUnitary.rowSum_bounded`
  (module `UnitaryCellMasses`, Worker 1797), which treats single-row exponents
  and spherical vectors. It is internal to the project.

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`: check
cc69287f (this module alone) and the builds of the whole candidate listed in
`UnitaryGenericLPolynomialNonvanishingProof.md`; no errors or warnings. After the docstring notation edit
(`δ(ϖ^lam)⁻¹`), check 964ea5b2 rebuilt the whole candidate cleanly. The main
theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
