# Relative determinant norm and normalized order

Author: Worker 110.

The closing theorem `Langlands.LocalClassField.relativeNormOrderLaws` proves
exactly the published proposition `RelativeNormOrderLaws.{u,v}`. The carrier
universes are independent. It quantifies every prime, compatible finite tower
of the specified p-adic fields, and every supplied pair of `TopologicalData`.
The determinant norm is `Algebra.norm`; the orders, residue degrees and
ramification indices are the existing constructions on that supplied data.
No Galois or unramified assumption is needed for the closing theorem.

## Implemented proof

The private lemma `norm_fieldNorm_eq_spectralNorm_pow` first proves, for any
finite extension L/K of a complete nontrivially normed ultrametric field,

    ‖N_{L/K}(x)‖ = spectralNorm K L x ^ [L:K].

Mathlib's `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` expresses the
spectral norm using the constant coefficient of the minimal polynomial.
Raising it to the positive minimal-polynomial degree removes the root.
`Algebra.norm_eq_norm_adjoin` reduces the determinant norm to K(x), and
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` computes that simple
extension norm as the signed constant coefficient. Its sign has norm one.
The simple-adjoin degree formula and the tower degree formula give the
claimed exponent. This argument includes zero and does not assume a
separable or Galois extension.

`normalizedAbs_relative_norm` applies this result over the p-adic base to
both fields. The published theorem
`normalizedAbs_eq_canonicalNorm_pow_degree` identifies the resulting absolute
norm sizes with the supplied residue-normalized absolute values.
`Algebra.norm_norm` then proves

    normalizedAbs_F (N_{E/F}(x)) = normalizedAbs_E x.

`normalizedAbs_relative_algebraMap` similarly uses
`spectralNorm.eq_of_tower` and multiplication of field degrees to prove

    normalizedAbs_E (i(x)) = normalizedAbs_F x ^ [E:F].

For nonzero x, the private helper `normalizedAbs_eq_prime_zpow` rewrites the
published expression q^(-ord(x)), using q = p^f, as p^(-f*ord(x)).
Injectivity of integer powers of the real number p > 1 applied to the norm
identity gives `residueDegree_mul_ord_relative_norm`:

    f_F * ord_F(N(x)) = f_E * ord_E(x).

Applying the same injectivity to the embedding identity first gives
f_E*ord_E(i(x)) = f_F*[E:F]*ord_F(x). The published absolute degree formulas
e_F*f_F = [F:Q_p] and e_E*f_E = [E:Q_p], together with the tower formula,
then imply `ramificationIndex_mul_ord_relative_algebraMap`:

    e_F * ord_E(i(x)) = e_E * ord_F(x).

Here the proof multiplies the two identities by e_F and ord_F(x), combines
them by polynomial arithmetic, and cancels the positive residue degree f_E.
Both order identities handle zero separately, using ord(0) = 0 and the
zero-preserving properties of the actual field norm and embedding.

`ord_relative_norm_units_eq_zero_iff` applies the first order identity to a
field unit and cancels the nonzero residue degrees. The mapped unit's
underlying value is definitionally the field norm, so the result uses the
exact `Units.map (Algebra.norm ...)` in the target. The closing theorem
assembles these three conclusions without adding hypotheses.

## Exported unramified specialization

`ord_relative_norm_of_unramified` assumes equality of the two absolute
ramification indices, precisely the unramified condition used by the
published unit-norm targets. Cancelling the common positive index from the
tower degree formula gives f_E = f_F*[E:F]. Substitution in the general norm
order law and cancellation of f_F yield

    ord_F(N(x)) = [E:F] * ord_E(x).

`ord_normUnits_of_unramified` gives the same equality for the published
`normUnits F.Carrier E.Carrier` on actual field units. These are direct
corollaries for the unramified norm-membership consumer. They assert no
surjectivity on integer units or on any unit-filtration group.

## Provenance and checks

This is a derived proof of the unchanged published norm/order target.
Its original-source provenance is recorded in
[NormCompatibilityStatement.md](NormCompatibilityStatement.md): Serre,
*Local Fields*, Chapter II, sections 1–2, in particular Corollary 4 on printed
page 29 (PDF page 37), followed by its absolute-value interpretation on printed
page 30 (PDF page 38). The present implementation uses the minimal-polynomial and
spectral-norm route described above, with the existing proof in
[Normalization/Proof.md](../../LocalField/Normalization/Proof.md) supplying
the arithmetic normalization and absolute degree identities. No new
literature assertion or definition is introduced by this module.

Development Lake compilation and inspection of the closing declaration
succeeded without diagnostics. The declaration retains the two universe
parameters u and v and has the exact written target `RelativeNormOrderLaws`.
The reported assumptions are only `propext`, `Classical.choice` and
`Quot.sound`. Independent semantic review, machine exact-target validation,
and Library publication remain separate requirements.
