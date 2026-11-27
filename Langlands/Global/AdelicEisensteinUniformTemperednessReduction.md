# Uniform temperedness of Eisenstein series from the criterion and the Eisenstein inputs

Module `Langlands.Global.AdelicEisensteinUniformTemperednessReduction`, namespace
`Langlands.Global`. It proves

```
theorem eisensteinUniformTemperedness_of_criterion
    (hcrit : UniformTemperednessCriterionStatement)
    (hgrowth : EisensteinUnitaryUniformGrowthStatement)
    (hexp : EisensteinUnitaryExponentStatement) :
    EisensteinUniformTemperednessStatement
```

It is a reduction: it does not prove `EisensteinUniformTemperednessStatement` (Delorme 2023,
Proposition 4.1; module `Langlands.Global.AdelicEisensteinUniformTemperednessStatement`) without
the three premises, which are stated in the modules
`Langlands.Global.AdelicUniformTemperednessCriterionStatement`,
`Langlands.Global.AdelicEisensteinUnitaryGrowthStatement` and
`Langlands.Global.AdelicEisensteinUnitaryExponentStatement` and are not proved in this module.

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering), proof of Proposition 4.1,
p.17: Mœglin–Waldspurger's Lemma I.4.1 holds uniformly for a bounded family of automorphic
forms whose constant terms uniformly satisfy its assumption, and it applies to the Eisenstein
series by Bernstein–Lapid's uniform growth, the holomorphy on `i𝔞_P^*` and the constant-term
formulas (4.1)–(4.2). The three premises split this sentence: the uniform criterion, the
uniform growth (with the holomorphy) and the exponents of the constant terms.

## Proof

Fix the data of the target, coordinates `e` and a compact `C`.

1. `hgrowth` gives an open level `L`, an exponent `R` and smooth left `G(F)`-invariant functions
   `f x` with underlying function `E(i e(x))` for `x ∈ C`, forming a family with uniform
   moderate growth on `C` (`IsUniformGrowthFamily rho hsmooth hcalc L R f C`).
2. `hexp` gives `m` such that for every standard family `𝓕`, index `J` and `x ∈ C`, the
   constant term of `E(i e(x))` along `P_J` satisfies `𝓕.HasSubunitaryShiftEquations J m`.
   Rewriting `E(i e(x))` as the function underlying `f x` gives hypothesis 2 of the criterion.
3. `hcrit`, applied to `f` on `S = C`, gives `k`; for each setup, threshold and compact `Ω` it
   gives `B`. Rewriting the function underlying `f x` back to `E(i e(x))` gives the target's
   bound with `m := k`.

The order of the quantifiers matches: `k` is chosen before the Siegel setup, and `B` after the
setup, the threshold and `Ω`. The proof uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).
