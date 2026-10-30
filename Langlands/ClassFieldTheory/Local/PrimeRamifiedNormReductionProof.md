# Prime ramified norm reduction proof

Authors: Worker 1047, with coauthors Worker 90, Worker 92 and Worker 110.
Some helper lemmas here are adapted from their published proofs; the
section Source and provenance lists each one.

The theorem `Langlands.LocalClassField.primeRamifiedNormReduction.{u,v}`
proves exactly the published proposition
`Langlands.LocalClassField.PrimeRamifiedNormReduction.{u,v}` from
`Langlands.ClassFieldTheory.Local.PrimeRamifiedNormReductionStatement`.
Its type is that proposition with no additional outer hypotheses, and its
universe parameters are `u, v` in that order. The statement pair and its
imports are unchanged.

Throughout, `TF` and `TL` are the canonical topological data of `F` and `L`,
`ell` is the degree, `t` the supplied break, `ψ` the natural index function
of the statement and `N = normUnits F.Carrier L.Carrier` the determinant norm
on field units.

## Use of the graded norm theorem

The proof starts by applying the published theorem
`primeRamifiedGradedNorm.{u,v}` (module
`Langlands.ClassFieldTheory.Local.PrimeRamifiedGradedNormProof`) to the same
data, and specializes its coefficient clause to the canonical uniformizers
`TF.uniformizer` and `TL.uniformizer`. It uses these parts:

- the containments `N(U_L^ψ(n)) ⊆ U_F^n` and
  `N(U_L^(ψ(n)+1)) ⊆ U_F^(n+1)` for every natural `n`;
- the zero-level formula: the relative residue map applied to the zero
  coordinate of `N x` equals the `ell`th power of the zero coordinate of `x`;
- for `0 < n < t`, the formula `r(c_n(N x)) = r(a_n) * c_n(x)^p` with
  `r(a_n) ≠ 0`, where `c_n` is the residue of the level-`n` unit
  coefficient (`unitCoefficient`) and `r` the relative residue map;
- for `n > t`, the formula `r(c_n(N x)) = r(b_n) * c_ψ(n)(x)` with
  `r(b_n) ≠ 0`.

The critical formula at `n = t` and the bijectivity clause are not used.
The relative residue map is a ring homomorphism between fields, hence
injective, and it maps the nonzero residues `a_n`, `b_n` to nonzero values.

## Generic helper lemmas

The namespace `Langlands.LocalClassField.PrimeRamifiedNormReductionProof`
contains lemmas stated for an arbitrary monoid homomorphism
`f : E.Carrierˣ →* F.Carrierˣ` between unit groups of two `PadicField`s with
topological data `T` and `S`.

- `exists_eq_of_approximations` is the completeness step. Suppose `f` is
  continuous for the supplied topologies and, for every `k`, some
  `x ∈ U_S^a` satisfies `y * f(x)⁻¹ ∈ U_T^(n+k)`. The sets `C_k` of such
  `x` are closed (preimages of the closed filtration levels under the
  continuous map `x ↦ y * f(x)⁻¹`, intersected with the closed `U_S^a`),
  nonempty and decreasing, and `C_0` is compact as a closed subset of the
  compact `U_S^a`. Mathlib's
  `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` gives
  a common point `x`. Then `y * f(x)⁻¹` lies in every level, so it is `1`
  by separatedness of the filtration, and `f(x) = y`. Compactness,
  closedness, monotonicity and separatedness of the unit filtration are the
  published `isCompact_unitFiltration`, `isClosed_unitFiltration`,
  `unitFiltration_antitone` and `unitFiltration_separated` from
  `UnitFiltrationStructuralProof`.
- `approximations_of_steps` is successive approximation. If every
  `w ∈ U_T^(n+k)` admits a correction `z` in a level contained in `U_S^a`
  with `w * f(z)⁻¹ ∈ U_T^(n+k+1)`, then induction on `k` multiplies the
  corrections into approximations to every depth inside `U_S^a`.
- These two lemmas are adapted from Worker 92's proof of
  `unitFiltrationCompactLifting_of_structural` in
  `Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyProof` (see
  Source and provenance).
- `map_eq_of_steps` combines both: for a monotone index function `ψ`,
  containments `f(U_S^ψ(n)) ⊆ U_T^n` and one-level corrections at every
  level `m > t` from `U_S^ψ(m)` give the subgroup equality
  `(U_S^ψ(n)).map f = U_T^n` for every `n > t`.
- `exists_step_positive` produces one positive-level correction from a
  residue formula `r(c_m(f x)) = φ(c_a(x))` whose right side attains every
  value `r(c)`. It takes a preimage under the surjective
  `positiveUnitCoordinate` of `GradedUnitCoordinates`, uses injectivity of
  `r` to match the coordinates, and concludes by
  `positiveUnitCoordinate_ker` that the quotient lies one level deeper.
- `exists_step_zero` is the analogous level-zero correction, from the
  formula `r(c_0(f x)) = c_0(x)^ell`, surjectivity of the `ell`th power on
  residue units, `zeroUnitCoordinate_surjective` and
  `zeroUnitCoordinate_ker`.
- `exists_mem_of_finite_steps` composes one-level corrections at the
  levels `0, …, t-1` to reduce an integer unit to level `t` modulo the image.
- `exists_pow_char_eq` and `exists_units_pow_char_eq` show that the `p`th
  power map is surjective on the actual residue field and on its units. The
  residue field is finite of characteristic `p` (`finite_residueField`,
  `residueCharP`), so Mathlib's `surjective_frobenius` applies.
- `Langlands.PadicField.TopologicalData.mem_unitFiltration_zero_of_ord_eq_zero`
  shows that a field unit of normalized order zero is an integer unit, hence
  lies in `U^0`. This public helper is reused directly from Worker 90's
  `Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof` (see
  Source and provenance).

Three arithmetic lemmas about the index function, `psi_monotone`,
`psi_succ_le` (`ψ(n) + 1 ≤ ψ(n+1)` for `n ≥ t`, `ell ≥ 1`) and `psi_pos`
(`ψ(n) > 0` for `n > t`), are proved by case analysis and `omega`.

Three lemmas concern the actual extension `L/F`:

- `residueDegree_eq_of_totalRamification` shows `f_L = f_F` for the
  absolute residue degrees from `e_L = ell * e_F`, the published
  `ramificationIndex_mul_residueDegree` for both fields and the tower law
  `Module.finrank_mul_finrank` over `Padic p`.
- `ord_normUnits_of_totalRamification` then cancels the common positive
  residue degree in the published `residueDegree_mul_ord_relative_norm`
  (`NormOrderProof`), giving `ord_F(N x) = ord_L(x)`. These two lemmas
  follow the pattern of Worker 110's `ord_relative_norm_of_unramified` in
  the same `NormOrderProof` module (see Source and provenance).
- `exists_norm_mul_of_unit_reduction` removes the valuation. For
  `x ∈ F.Carrierˣ` with `k = ord_F(x)`, set `y0 = π_L^k`, where `π_L` is
  `TL.uniformizer` viewed as a unit. Then `ord_F(N y0) = k`, so `x * (N y0)⁻¹` has
  order zero and lies in `U_F^0`. A reduction `w * (N y1)⁻¹ ∈ U_F^t` of
  integer units gives `x = N(y0 * y1) * z` with `z ∈ U_F^t`.

## Main theorem

**Clause 1.** The norm `N` is continuous for the canonical topologies by
the published continuous homomorphism `localNorm TF TL` of `Norms.lean`,
whose underlying map is `normUnits`. For `m > t`, the above-break graded
formula and `exists_step_positive` with `φ(d) = r(b_m) * d` (attaining
`r(c)` at `d = r(c) / r(b_m)`) give one-level corrections from
`U_L^ψ(m)`; here `ψ(m) > 0` by `psi_pos`. Then `map_eq_of_steps` yields
`(U_L^ψ(n)).map N = U_F^n` for every `n > t`. The preimage is constructed
inside `U_L^ψ(n)` by the compactness argument above, not assumed.

**Clause 2.** For `n ≥ t`, the containment of `N(U_L^(ψ(n)+1))` in
`U_F^(n+1)` is the graded theorem. Conversely `U_F^(n+1)` is the image of
`U_L^ψ(n+1)` by clause 1 at `n + 1 > t`, and
`U_L^ψ(n+1) ⊆ U_L^(ψ(n)+1)` by `psi_succ_le` and monotonicity of the
filtration. This covers `n = t` and `t = 0`.

**Clause 3.** First every `w ∈ U_F^0` is reduced to `U_F^t` modulo norms.
If `t = 0` the witness `1` suffices and no residue surjectivity is used.
If `t > 0`, the supplied pattern gives `lowerRamificationGroup TL F.Carrier 1
= ⊤`, and the published
`lowerRamificationGroup_one_eq_top_iff_prime_degree`
(`PrimeRamificationArithmeticSupport`) gives `ell = p`. For `m < t`,
`ψ(m) = m` and the graded containment maps `U_L^m` into `U_F^m`. At
`m = 0`, `exists_step_zero` uses the zero-level formula and surjectivity of
the `p`th power on residue units. At `0 < m < t`, `exists_step_positive`
uses the below-break formula with `φ(d) = r(a_m) * d^p`, which attains
every `r(c)` by Frobenius surjectivity on the finite residue field of `L`.
`exists_mem_of_finite_steps` composes these corrections. Finally
`exists_norm_mul_of_unit_reduction` extends the reduction from integer
units to all of `F.Carrierˣ`, including elements of positive and negative
order.

## Source and provenance

The mathematics follows Jean-Pierre Serre, *Local Fields*, Greenberg
translation, GTM 67, Springer (1979), registered as
`serre-1979-local-fields`, Chapter V, §3:

- Corollary 2 to Proposition 5 (printed p. 85 / PDF p. 92): graded norm
  surjectivity above the break, and below it for a perfect residue field.
- Corollary 3 (printed pp. 85–86 / PDF pp. 92–93): the two higher-unit
  norm equalities, by Lemma 2 of V.1 (printed p. 81 / PDF p. 88) and the
  inclusion `U_L^ψ(n+1) ⊆ U_L^(ψ(n)+1)`.
- Corollaries 6–7 (printed pp. 86–87 / PDF pp. 93–94): reduction of
  integer units below the break, and removal of the valuation using residue
  degree one.

The registered errata `serre-book-corrections-2019` (Local Fields section,
PDF pp. 2–3) list no corrections to printed pp. 81–88.

The implemented route differs from Serre in presentation. Serre's Lemma 2
on complete filtered groups is replaced by the explicit
successive-approximation and compactness argument of
`exists_eq_of_approximations`. The isomorphisms of Corollaries 6–7 are
replaced by explicit multiplicative witnesses. Perfectness of the residue
field is used only through Frobenius surjectivity on the actual finite
residue field. The graded formulas themselves come from the published
`primeRamifiedGradedNorm`, whose Markdown records its sources and authors.

Several helpers reuse or adapt published Library proofs that Worker 1047
read while writing this module:

- `Langlands.PadicField.TopologicalData.mem_unitFiltration_zero_of_ord_eq_zero`
  is Worker 90's existing helper in
  `Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof`, exposed
  publicly and reused directly. Its statement and proof are unchanged. It
  constructs an integer unit from the integrality of `a` and `a⁻¹`, checks
  level-zero membership in the residue quotient, and identifies the
  resulting field unit using `Units.ext`.
- `exists_eq_of_approximations` and `approximations_of_steps` are adapted
  from Worker 92's proof of `unitFiltrationCompactLifting_of_structural` in
  `Langlands.ClassFieldTheory.Local.UnitFiltrationTopologyProof`. The
  successive-approximation induction and the compactness argument follow
  Worker 92's proof closely: the sets `C k`, their closedness, compactness
  and nesting, the appeal to
  `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` and the
  separatedness conclusion. The published criterion
  `UnitFiltrationCompactLifting` cannot be applied directly here. It
  requires `f(U_S^n) ⊆ U_T^n` with corrections from `U_S^n` at every level
  `n`, while here the source level is `ψ(n)` and corrections exist only
  above the break. Worker 1047 therefore generalized the argument to an
  arbitrary source group `U_S^a`, a correction-level function `lev` and
  depths from an arbitrary `n`, and split it into the two lemmas. The
  structural facts are invoked directly through the published
  `isCompact_unitFiltration`, `isClosed_unitFiltration`,
  `unitFiltration_antitone` and `unitFiltration_separated`.
- `residueDegree_eq_of_totalRamification` and
  `ord_normUnits_of_totalRamification` follow the pattern of Worker 110's
  `ord_relative_norm_of_unramified` in
  `Langlands.ClassFieldTheory.Local.NormOrderProof`. That proof cancels the
  ramification index with `Nat.eq_of_mul_eq_mul_left` and the tower law,
  then cancels the residue degree in `residueDegree_mul_ord_relative_norm`
  with `mul_left_cancel₀`. The final cancellation line is the same. The
  residue-degree equality for total ramification is proved here by a
  separate `calc` argument.

The Library also publishes Worker 96's `ord_norm` and `residueDegree_eq` in
`Langlands.ClassFieldTheory.Local.PrimeGradedNormSupport`. These are
analogous statements under a total-ramification hypothesis, with `ord_norm`
stated for `Algebra.norm` on field elements. Worker 1047 did not consult or
import them.

Worker 1047 wrote the remaining helper lemmas, the main theorem and this
explanation, and adapted the helpers listed above. Workers 90, 92 and 110 are
listed as coauthors of this contribution for the adapted code. They did not
take part in this task.
