# Weak induction, inverse characters and contragredients

Module `Langlands.Automorphic.Unramified.ContragredientWeakInduction`. Facts on the
unramified condition `SpectralSystem.IsWeakInductionOf` of weak automorphic induction of a
Hecke character (Harris 1998, Definition 1.3(b), rank-one case; see
`Langlands.Automorphic.Unramified.WeakInduction` and
`Langlands.Automorphic.WeakAutomorphicInduction`). The fields `E`, `E'` (with
`[Algebra E E']`) are number fields in independent universes; `uV` is the carrier universe
of spectral presentations.

## Results

Polynomial facts (namespace `Langlands.Automorphic.Unramified.WeakInduction`):

- `reverse_one_sub_C_mul_X_pow`: for `a ≠ 0` and every `f`, the reverse of `1 - a X ^ f` is
  `X ^ f - a`.
- `reverse_finset_prod`: reversal of complex polynomials commutes with finite products.
- `eulerPolynomial_map_inv_of_eq_prod`: if the Euler polynomial `∏_{z ∈ s} (1 - z X)` of a
  spectrum `s : Eigenvalues n` equals `∏_i (1 - a_i X ^ f_i)` for a finite family of units
  `a_i` and exponents `f_i ≥ 1`, then the Euler polynomial of the inverse spectrum
  `s.map (·⁻¹)` equals `∏_i (1 - a_i⁻¹ X ^ f_i)`.

Spectral systems (namespace `Langlands.Unramified.SpectralSystem`):

- `IsWeakInductionOf.inv_of_eigenvalues`: if `s` is a weak induction of `χ`, and at all but
  finitely many places outside both exceptional sets the spectrum of `t` is the inverse of
  that of `s`, then `t` is a weak induction of `χ⁻¹`.
- `IsWeakInductionOf.sameEulerPolynomials`: two weak inductions of the same character (of
  any ranks) have the same Euler polynomials outside a finite set.

Cuspidal classes (namespace `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass`):

- `isWeakAutomorphicInductionOf_inv_of_isContragredientOf`: if `Sd` realizes the
  contragredient of the cuspidal realization `S` over `E` and `S.isoClass` is a weak
  automorphic induction of `χ`, then `Sd.isoClass` is a weak automorphic induction of
  `χ⁻¹` (same universes `uE, uE', uV`).
- `eq_of_sameEulerPolynomials`: given Euler constituent recovery over the field `F` (the
  body of `CuspidalEulerConstituentRecoveryStatement` at `F`, universes `uF, uV`), two
  cuspidal classes over `F` of the same rank with attached systems having the same Euler
  polynomials outside a finite set are equal.

## Proofs

- Reverse of `1 - a X ^ f`: write it as `C (-a) * X ^ f + C 1`; `reverse_add_C`,
  `reverse_mul_X_pow`, `reverse_C` and `natDegree_C_mul_X_pow` give `-a + X ^ f`. The
  product rule is induction on the finset with `reverse_mul_of_domain`.
- Euler inversion: with `k = ∏_{z ∈ s} (-z)`, `PairedHecke.C_mul_eulerPolynomial_map_inv`
  gives `C k * E(s⁻¹) = reverse E(s)`. By the hypothesis and the two reversal lemmas,
  `reverse E(s) = ∏_i (X ^ f_i - a_i) = C k' * Q` with `k' = ∏_i (-a_i)` and
  `Q = ∏_i (1 - a_i⁻¹ X ^ f_i)`, using `-a (1 - a⁻¹ X ^ f) = X ^ f - a`. Both `E(s⁻¹)` and
  `Q` take the value `1` at `0` (for `Q` because every `f_i ≥ 1`), so evaluating at `0`
  gives `k = k'`; `k'` is nonzero, and cancelling `C k` gives `E(s⁻¹) = Q`.
- Inverse character: the rank condition is unchanged. At a cofinite place `v` where `s` is
  weakly induced, the places above `v` are unramified and `χ⁻¹` is unramified there,
  since its components are the inverses of those of `χ` (`finiteComponent_inv`). For a
  uniformizer family `ϖ`, the Euler polynomial of `s` at `v` is
  `∏_w (1 - χ_w(ϖ_w) X ^ f(w|v))`, the inertia degrees are positive
  (`Ideal.inertiaDeg_pos`), and the Euler inversion gives
  `∏_w (1 - χ_w(ϖ_w)⁻¹ X ^ f(w|v))`, which is the induced Euler polynomial of `χ⁻¹`.
- Same Euler polynomials: at a place where both conditions hold, choose a uniformizer of
  every completion above `v` (`WeakInduction.exists_uniformizer`); both Euler polynomials
  equal the induced polynomial at this family.
- Contragredient: take a presentation `P` of `S` witnessing the weak induction
  (`isWeakAutomorphicInductionOf_iff`), a presentation `Pd` of `Sd` in the same carrier
  universe (`cuspidalDualPresentationExistence`), and apply the inverse-character result
  with `eigenvalues_eq_map_inv_of_isContragredientOf`, which gives the inverse spectrum at
  every place outside both exceptional sets.
- Equality of classes: apply the recovery hypothesis to the singleton families `c` and `d`
  with the systems `s` and `t`; the sums over one-element families have the Euler
  polynomials of `s` and `t` (`IsobaricData.sameEulerPolynomials_finiteSum_one`), and the
  resulting bijection of `Fin 1` matches the two classes
  (`PositiveRankCuspidalClass.ofFixedRank_injective`). This is the argument of
  `weakInductionUniqueness_of_cuspidalEulerConstituentRecovery` in
  `Langlands.Automorphic.Unramified.WeakInductionUniqueness`, with recovery assumed at one
  field only.

## Provenance

Derived content. The unramified condition follows Harris (1998), *The local Langlands
conjecture for GL(n) over a p-adic field, n < p*, Invent. Math. 134, 177–210 (registered
source `harris-1998-local-langlands`), Definition 1.3(b), as formalized in
`Langlands.Automorphic.Unramified.WeakInduction`. The inversion of the Euler factors is the
unramified computation behind the fact that the contragredient of an induction from `χ` is
the induction from `χ⁻¹`; the comparison of classes uses Euler constituent recovery,
the numerical step of Jacquet–Shalika strong multiplicity one stated in
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement`.
