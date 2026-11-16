# Primitive division polynomial reduction (NYLL M340.003)

This module proves the published target
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_map_residueStatement`
as
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_map_residue`.
Its type is the imported target fully applied to `hπ n`.

For a field `K : Type u`, a shared `LocalField.{u, v} K` package `F`, a
valuation-ring element `π`, a proof `hπ` that its image in `K` is a
uniformizer, and any `n : ℕ`, put `q = Nat.card F.residueField`. The theorem
says that coefficient reduction of
`standardLubinTatePrimitivePolynomial F π n` is
`Polynomial.X ^ ((q - 1) * q ^ n)`. The independent universes `u v`, implicit
`K`, field instance, implicit `F` and `π`, and explicit `hπ` followed by `n`
are retained in source order. No additional hypotheses are introduced.

## Implemented proof

The proof is the simplification argument in NYLL M340.003. It unfolds the
published Prop target and the primitive polynomial definition
`(standardLubinTatePolynomialIterate F π n) ^ (q - 1) + Polynomial.C π`.
Polynomial coefficient mapping preserves addition and powers and sends a
constant to the constant of its image. The imported exact M340.002 theorem
`standardLubinTatePolynomialIterate_map_residue hπ n` replaces the mapped
iterate by `Polynomial.X ^ (q ^ n)`. The imported exact M337.001 theorem
`SameUniformizer.residueMap_uniformizer_eq_zero hπ` sends the constant term
to zero. Finally, `← pow_mul` and `Nat.mul_comm` give the required exponent
`(q - 1) * q ^ n`.

The two imported theorems have Prop-valued target definitions as their types.
Explicitly typed local facts `hiter` and `hzero` expose their equality
conclusions to `simp`. They are derived from the imported proofs and add no
hypotheses. This proof leaves the target and every imported Lean/Markdown
pair unchanged.

## Original source and adaptations

Naganori Yamaguchi, NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`,
SHA-256 `50d30d87957974e1bf1b9c297ea2b4430cd4a37ac78ab26b38c8e1895414e815`:
M340.003, docstring lines 71–72, declaration and type lines 73–79, proof
lines 79–83; common file context is lines 1–42. The registered sources are
`external-lean-reuse-snapshots-2026-10-21` (under
`n-yamaguchi-0729--ClassFieldTheory/source/`) and attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. No matching project erratum was
found in the Library errata notes when preparing this proof.

Worker 571 extracted only M340.003, prefixed the namespace by
`Langlands.NYLL`, replaced the source imports with the published target,
iterate-residue proof and uniformizer-residue proof modules, and stated the
theorem as the fully applied published target. The proof adds the target
definition to the `simp` list and uses explicitly typed local equalities to
unfold the prerequisite targets before simplification. The unused
`open scoped Polynomial` was dropped and the module documentation replaced.
The original copyright, author and Apache-2.0 header are retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
