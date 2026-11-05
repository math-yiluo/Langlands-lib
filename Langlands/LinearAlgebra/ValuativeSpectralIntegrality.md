# Valuative coefficient and root integrality

Author: Worker 1563.

`Langlands.valuativeSpectralIntegrality_proof.{u, v}` proves
`Langlands.ValuativeSpectralIntegralityStatement.{u, v}`. The two separate
wrapper theorems prove the polynomial and matrix constituents.

First the proof identifies `x ≤ᵥ 1` with integrality of `x` over the
canonical valuation ring by
`Valuation.Integers.isIntegral_iff_v_le_one`. For a monic polynomial with
integral coefficients, `Polynomial.lifts_and_degree_eq_and_monic`
produces a monic lift to that ring. Any root satisfies the lifted monic
polynomial and is therefore integral over the ring. Conversely,
`Polynomial.isIntegral_coeff_of_factors` expresses the coefficients of a
split polynomial as integral expressions in its integral roots and its
integral leading coefficient. This proves the same-field comparison.

The `ValuativeExtension` instance preserves and reflects the comparisons
on every coefficient after applying the algebra map. Applying the
same-field comparison to the mapped monic polynomial proves the
splitting-extension form. Finally `Matrix.charpoly_map` identifies the
mapped characteristic polynomial with the characteristic polynomial of
the mapped matrix.

The implementation is a direct derivation from the imported Mathlib
ring-theoretic and valuation results. No original-literature assertion
beyond those existing definitions is introduced. Independent field
universes, trivial valuations, inseparable extensions, repeated roots,
and zero-dimensional matrices are retained. A splitting premise is
explicit; the proof neither constructs a compatible valuation extension
nor proves any group-theoretic boundedness result.
