# Quotient construction for unipotent Iwahori double cosets

This is supporting work for the added KP Theorem 7.8.1(4), in the authors'
1 November 2024 corrections, PDF pages 35–36. The geometric Iwasawa
decomposition and corrected normalizer-coset lemma remain explicit inputs.
This module does not prove their global statements or close the global
unipotent Iwahori target.

The registered source is `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The exact per-data target and its geometric inputs are the published
[Iwahori–Weyl statements](IwahoriWeylStatement.md). The normalization proof
uses the published [dynamic decomposition](../../GroupScheme/Dynamic/Decomposition.md)
theorem `Dynamic.conj_mem_unipotent`.

`normalizerDoubleCosetMap` descends the representative map through the quotient.
The accompanying equivalence criterion proves injectivity by quotient induction
and surjectivity by reducing a double-coset class to a representative.

For the actual building data, the corrected criterion implies normality of
`normalizerZero`: for `z` in the zero subgroup, write
`n = 1 * (n*z) * z⁻¹`, using its image in the chamber parahoric. The criterion
then gives `n*z*n⁻¹` in the zero subgroup.

Centralizer points normalize every literal standard unipotent because they
belong to each dynamic centralizer in its defining intersection. Dynamic
centralizers lie in dynamic parabolics, which preserve their dynamic
unipotents by conjugation.

The first quotient equivalence uses Iwasawa for representative surjectivity,
and the corrected coset criterion together with the derived normality for
descent and injectivity. Its value on every normalizer representative follows
from the quotient lift itself. The quotient uses the full normalizer modulo
the actual zero subgroup, retaining all components.

For the second equivalence, the centralizer normalization proves that the
carrier of `U ⊔ Z₀` is exactly the literal pointwise product `U * Z₀`, where
`Z₀` is the actual ambient image of `centralizerZero`. On normalizer
representatives, a relation `n' = (u*z)*n*p` becomes
`n' = u*n*((n⁻¹*z*n)*p)`. Derived normality puts the conjugated zero element
in the chamber parahoric, so the original corrected criterion still decides
equality. Conversely a relation with left factor in `U` is a relation with
left factor in `U ⊔ Z₀`. The same Iwasawa factorization proves surjectivity.

The construction first uses the subgroup `U ⊔ Z₀` to apply the subgroup
double-coset API and then rewrites its carrier by the proved equality to
`U * Z₀`. This transports the equivalence and its representative equation
to precisely the set-quotient target, including its `Quotient.mk''` equation.
It establishes both conjuncts of the published per-data
`UnipotentIwahoriDoubleCosetBijection` from the two named geometric facts.
No apartment, chamber, Henselian or residue-field premise is weakened by
this reduction; those hypotheses belong to the still-separate proofs of
the input facts.

The general quotient lift, normality deduction and intersection-normalization
lemmas are internal derived content. Their provenance is the elementary
quotient argument just described, combined with the already published
dynamic conjugation theorem. They assert no additional building existence,
component exact sequence or global Iwasawa theorem.
