# `Langlands.TauCeti.Algebra.Polynomial.Laurent.Basic`

Port of the TauCeti file `TauCeti/Algebra/Polynomial/Laurent/Basic.lean` at commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, from the
registered source `tauceti-8428d621-weil-restriction-closure`. Copyright (c) 2026 The Tau Ceti contributors,
released under the Apache 2.0 license; the licence and a notice are in
`licenses/TauCeti/`. The upstream header, module documentation, module-system
keywords (`module`, `public`, `@[expose]`) and declaration names are kept, and no
declaration is renamed.

## Contents

Laurent polynomial maps and evaluation at units.

- `TauCeti.laurentEval u : R[T;T⁻¹] →ₐ[R] A` for a unit `u` of an `R`-algebra `A`
  (not necessarily commutative), `TauCeti.laurentEval_unique`, and
  `TauCeti.laurentEvalEquiv : Aˣ ≃ (R[T;T⁻¹] →ₐ[R] A)`;
  `TauCeti.laurentEval_eq_eval₂` compares with Mathlib's `LaurentPolynomial.eval₂`.
- `LaurentPolynomial.mapAlgHom_C`, `LaurentPolynomial.mapAlgHom_T`,
  `LaurentPolynomial.genericUnit`, `LaurentPolynomial.T_sum`,
  `LaurentPolynomial.rescale`, `LaurentPolynomial.mapDomainAlgHom_mulRight_T` and
  related substitution lemmas.
- `TauCeti.laurentTAut`, `TauCeti.mul_laurentEval`,
  `TauCeti.eval₂_C_injective_of_val_eq_T`, `TauCeti.eval₂_C_inv_pow_injective`,
  `TauCeti.laurentPolynomialC_smul`, `TauCeti.map_smul_eq_laurentEval_smul`.

## Edits relative to upstream

- Lines 396 and 411: `MonoidHom.coe_ofClass` replaced by `MonoidHom.coe_coe` in two `simp` lists (the former lemma does not exist in the pinned Mathlib).

## Port note

The Lean file carries a port note comment between the upstream copyright
header and the `module` keyword. It names the upstream file, the commit, the
repository `https://github.com/TauCetiProject/TauCeti` and the registered
source, and lists the edits above.

## Credit

Port prepared from Worker 207's shared draft for task 46249db5 (the import
renaming, the compatibility fixes and this description), with the port note and
licence files added by Worker 1122. It builds with lake against environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library commit
`dad4d948ab2f6838277ce9094bcc92df1507b0cb` with 0 errors and 0 warnings.
