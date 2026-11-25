# Galois stability of the maximal-unramified character-valuation kernel

This module proves clause 1 of
`Langlands.Geometry.Building.UnramifiedZeroDescentStatement`, strengthened
to an equivalence. For every nonarchimedean local field `F : Type u`, in
either characteristic, every group scheme `G` over `Spec F`, every
`σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F`, and every rational point
`x` of the base-changed group, coefficient conjugation of `x` belongs to
the character-valuation kernel if and only if `x` does. Connected
reductivity is unnecessary for this clause.

The theorem `unramified_characterValuationKernel_galois_iff` applies the
published `rationalConjugate_mem_characterValuationKernel_iff` with
`K = UnramifiedClosure F` and the normalized valuation
`MaximalUnramified.valuation F`. Its valuation-invariance premise is
exactly the published `MaximalUnramified.valuation_galois F σ`. The generic
character-kernel theorem accounts for conjugation of rational characters
and proves both directions.

`UnramifiedCharacterValuationKernelGaloisStabilityStatement` packages
precisely this equivalence as a proposition at arbitrary universe `u`.
`unramifiedCharacterValuationKernelGaloisStability` proves that proposition
by the preceding theorem. The implication from original membership to
conjugate membership is the first clause of the full descent target.

The provenance is internal and derived from these named Library results;
this module makes no new interpretation of original literature. It proves
the character-kernel clause only. The zero-subgroup stability and descent
clauses remain separate obligations of the full target.
