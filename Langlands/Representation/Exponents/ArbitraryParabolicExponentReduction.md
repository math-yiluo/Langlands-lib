# The exponent theorem from Jacquet admissibility and quotient compactness

Author: Worker 1670. This is an internal conditional assembly of the published
represented-parabolic exponent results. It uses the existing statements and
constructions without changing them.

`ArbitraryParabolicExponentReductionStatement` is the implication

```lean
ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
  ArbitraryParabolicQuotientCompactStatement.{u} →
    ArbitraryParabolicExponentStatement.{u, v}
```

`arbitraryParabolicExponent_reduction` proves this implication. The field
universe `u` and representation-carrier universe `v` are independent.
The conclusion is the original proposition itself, retaining every field,
valuation, topology, local-field, connected-reductive, local-compactness and
nonarchimedean-group quantifier, the canonical rational-point topology, all
parabolic, Levi, radical, multiplication-isomorphism and split-component data,
and every supplied compatible point homomorphism.

For clause 1, the Jacquet-admissibility premise is specialized to the given
field, group, represented parabolic and source representation. The published
`normalizedJacquetWeightSpace_decomposition_of_admissible` then gives
independence and spanning of the actual normalized Jacquet characteristic
spaces, indexed by the actual exponent set.

If the source has finite length, the quotient-compactness premise supplies
`CompactSpace (Induction.LeftQuotient (pointImage p))` for that same parabolic.
The proof installs this instance for the existing canonical quotient topology
and applies
`finite_normalizedJacquetExponents_of_hasFiniteLength_of_compactQuotient_of_spanning`
to the source finite-length proof and the spanning equality just obtained.
That imported argument deduces source finite generation from finite length,
passes finite generation to the actual normalized Jacquet module using the
compact quotient, and combines it with independence and spanning to obtain
finite exponent support. No finite-length preservation assertion for the
Jacquet functor is used.

Clause 2 is the published `groupWeightSpace_decomposition` for the specified
split component and admissible representation. The two parts of clause 3 are
the published `inducedExponent_restrict` and
`normalizedJacquetExponent_restrict`, applied to the same compatible point
homomorphism. Their conclusions already have exactly the character and
exponent conventions of the original target.

The source context is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, VII.1.1, printed pages 220–221 /
PDF pages 226–227. Jacquet admissibility is the normalized assertion of the
VI.6.1 Corollary, printed pages 176–177 / PDF pages 182–183; quotient
compactness is the compactness assertion of the V.5.1 Corollary, printed
page 123 / PDF page 129. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implication is an internal dependency reduction rather than an additional
assertion attributed to Renard. Its finite-support route uses finite
generation, independence and spanning, whereas Renard invokes Jacquet
finite-length preservation and Schur's lemma.

Both global premises remain hypotheses of this theorem. The module supplies
no unconditional proof of Jacquet admissibility, quotient compactness or the
full exponent proposition. It does not establish a contraction basis,
cocharacter realization, existence of a compatible inclusion, Casselman's
criterion or any VII.2 assertion.
