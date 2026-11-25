# Reduction of the Mumford Rosati trace formula to two degree statements

This module defines a reduction proposition and proves it.

## The proposition

`Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceReductionStatement` is

`IsogenyDegreeTateDeterminantStatement.{u} → MumfordEulerDegreeStatement.{u} → MumfordMixedEulerTraceStatement.{u}`.

The three propositions are the existing Library statements:

- `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantStatement` (S1): the degree of an endomorphism of an abelian scheme over an algebraically closed field is the determinant of its rational `p`-adic Tate map, and that determinant is `0` for a non-isogeny.
- `Langlands.AbelianScheme.Rosati.MumfordEulerDegreeStatement` (S2): for an ample Mumford presentation `lam` of `L` and an endomorphism `f`, the map `n • lam + f ≫ lam ≫ f^∨` is an isogeny of degree `χ(f^* L ⊗ L^n)^2` for all large `n`.
- `Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceStatement`: the Mumford Rosati mixed Euler trace formula, proved in the Library as `Langlands.AbelianScheme.Rosati.mumfordMixedEulerTrace` (module `MumfordRosatiMixedEulerTraceProof`).

All three are used at the same universe `u`. The theorem `Langlands.AbelianScheme.Rosati.mumfordMixedEulerTraceReduction` proves the reduction. It uses no premise beyond S1 and S2, and its axioms are `propext`, `Classical.choice` and `Quot.sound`.

Provenance: this is an internal reduction. It follows the idea of Milne, *Abelian Varieties* (author revision 2022), p. 23: there the trace of `α` is read off as the subleading coefficient of the polynomial `P_α`, whose values are the degrees `deg(α - r)`. Here the subleading coefficients of two expressions for the degree of an isogeny are compared. The comparison replaces the intersection-number computation of Milne's proof of Theorem 17.3 (pp. 35–36) and works in the Library's Euler-coefficient normalization. The argument itself is ordinary algebra and is described below.

## Proof

Fix the data of the target: `P`, `k` algebraically closed of characteristic zero, `A`, `W`, `hadd`, `lam` with `HasRationalInverse`, `g > 0` with `A.HasRelativeDimension g`, the ample Mumford presentation of `L`, and `f : A ⟶ A`. Write `V` for the actual rational `2`-adic Tate module `Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) 2`.

The helper results are in the namespace `Langlands.AbelianScheme.Rosati.MumfordTraceReduction`.

### Algebra

- `two_mul_coeff_pred_eq`: let `D` be monic of degree `2g` and `Q` of degree at most `g` over a field, with `c ≠ 0`, `g > 0` and `C r * Q ^ 2 = C c * D`. Then `2 * Q.coeff (g - 1) = Q.coeff g * D.nextCoeff`. Comparing coefficients of degree `2g` gives `r * Q.coeff g ^ 2 = c`, so `Q.coeff g ≠ 0`. Then `Q' = Q / Q.coeff g` is monic with `Q' ^ 2 = D`, and `Monic.nextCoeff_pow` finishes.
- `coeff_mem_range_of_eval_natCast`: a polynomial over a characteristic-zero field whose values at all natural numbers are rational has rational coefficients. The proof interpolates the values at `0, …, natDegree` with a rational Lagrange polynomial, then uses `eq_of_degree_sub_lt_of_eval_finset_eq`.
- `nextCoeff_charpoly_neg`: `(charpoly (-T)).nextCoeff = trace T`. `eval_charpoly_neg`: `(charpoly (-T)).eval t = det (algebraMap t + T)`.

### Tate modules

- `rationalEndAction_homToHom0`: the rational action of an integral endomorphism is its Tate map `rationalMap`.
- `rational_two_finrank`: `V` is finite-dimensional of dimension `2g`, by the published `geometricPrimeAdicRank` at the identity point; `2` is a unit of the global sections in characteristic zero (`isUnit_intCast_global`).
- `trace_rationalMap_mem_range` (uses S1): for an integral `α`, `charpoly (-V α)` takes the value `det (V (n • 𝟙 + α))` at every natural `n`. By both clauses of S1 this value is a rank or `0`, so it is rational. Its next coefficient, the trace of `V α`, is therefore rational.
- `primeEndomorphismTrace_mem_range`: this extends to every rational endomorphism by `Rationalization.exists_integral_multiple`.
- `algebraMap_geometricEndomorphismTrace`: the rational values define a `ℚ`-linear lift of the actual `2`-adic trace. By `geometricEndomorphismTrace_eq`, the Library's chosen trace equals this lift. So `algebraMap ℚ ℚ_[2] (geometricEndomorphismTrace A a) = primeEndomorphismTrace A 2 a` for every `a`.

### The polarization

- `exists_integral_inverse`: there are `N > 0` and `μ : W.dual P ⟶ A` with `homToHom0 μ = N • polarizationInverse P W lam` and `μ` an isogeny. One takes `n • μ₀` for an integral multiple `μ₀ = n · lam⁻¹`. Injectivity of `homToHom0` in characteristic zero gives `lam ≫ μ = (n n) • 𝟙` and `μ ≫ lam = (n n) • 𝟙`. Then `integralInverseData_finiteEtaleIsogenies` applies.
- `homToHom0_comp_inverse`: in `End0 A`, `homToHom0 ((n • lam + f ≫ lam ≫ f^∨) ≫ μ) = N • (n + β)` with `β = involution (homToHom0 f) * f`. The computation uses `dualHom0_homToHom0`, `polarization_comp_inverse` and associativity of `comp0`.
- `det_rationalMap_comp_inverse`: hence `det V((n • lam + f ≫ lam ≫ f^∨) ≫ μ) = N ^ (2g) * (charpoly (-V β)).eval n`.
- `finrank_eq_of_isIsogeny` and `finrank_comp_of_isIsogeny`: an isogeny over a field has constant rank on its connected target. A composite of isogenies has rank equal to the product of the ranks, by the published `finiteFlatConstantRankComposition`.

### Euler polynomials

- `euler_facts`: let `Q_N` be the canonical `coherentEulerPolynomial` of `N` twisted by `L`, truncated at `g`. `Q_N` evaluates to the actual Euler sequence, because `topologicalKrullDim ≤ g` by `fieldSmoothTopologicalKrullDim`. Its coefficient at `g` equals that of the pure polynomial `lineBundleEulerPolynomial`, by `topEulerCoefficientTwistInvariant` and `tensorLeftUnitor`. The mixed coefficient is `Q_N.coeff (g - 1) - P_L.coeff (g - 1)`.
- `mixed_pullback_id` and `mixed_self_eq`: the mixed coefficient of the identity pullback of `L` equals `g` times the top pure coefficient, by `mixedLineBundleEulerCoefficient_self`.

### Key identity and conclusion

`key_identity` uses S1 and S2. Take `n₀` from S2 for `f` and set `r = rank μ`. For every `n ≥ n₀`, compute the rank of `(n • lam + f ≫ lam ≫ f^∨) ≫ μ` in two ways. By S2 and the composite rank it is `χ(f^* L ⊗ L^n)^2 · r`. By S1 and `det_rationalMap_comp_inverse` it is `N ^ (2g) · det(n + V β)`. These values agree at infinitely many points, so `C r * Q^2 = C (N ^ (2g)) * charpoly (-V β)` as `ℚ_[2]`-polynomials, where `Q` is `Q_{f^* L}` mapped to `ℚ_[2]`. Then `two_mul_coeff_pred_eq` gives

`2 · Q_{f^* L}.coeff (g - 1) = Q_{f^* L}.coeff g · trace (V β)`.

For `f = 𝟙` we have `β = 1`, because the dual of the identity is the identity and `lam` composed with its inverse is the identity. Its trace is `dim V = 2g`. With `mixed_self_eq` this shows that the subleading pure coefficient `P_L.coeff (g - 1)` vanishes. For general `f`, the target's form is `geometricEndomorphismTrace (f * f†)`. By `geometricEndomorphismTrace_mul_comm` this equals the trace of `β`. Mapping to `ℚ_[2]` with `algebraMap_geometricEndomorphismTrace` and using the top-coefficient equality gives

`traceForm(f, f) · P_L.coeff g = 2 · (Q_{f^* L}.coeff (g - 1) - P_L.coeff (g - 1))`,

which is the target statement.

## Scope

The reduction proves nothing about S1 or S2. The target becomes unconditional only once both statements are proved. The trace used is exactly the Library's `geometricEndomorphismTrace`. Its rational lift exists by the argument above, so no trace-comparison premise is added.
