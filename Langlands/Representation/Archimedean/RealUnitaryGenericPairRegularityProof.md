# Proof: Getz–Hahn, Theorem 11.5.2, real case

Module `Langlands.Representation.Archimedean.RealUnitaryGenericPairRegularityProof`. The theorem

```lean
theorem Langlands.Archimedean.realUnitaryGenericPairRegularity :
    RealUnitaryGenericPairRegularityStatement.{uV, uW}
```

proves `Langlands.Archimedean.RealUnitaryGenericPairRegularityStatement` (module
`UnitaryGenericPairRegularityStatement`) at universes `uV` and `uW`. Unfolded, the statement is

```lean
∀ (n m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ (Matrix.unitaryGroup (Fin m) ℝ) W)
    (π' : (ℂ ⊗[ℝ] Matrix (Fin m) (Fin m) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (ds ds' : List RealBlock),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsRealGenericGKModule n π → IsRealUnitarizableGKModule n ρ π →
        HasRealStandardParameter n ρ π ds →
    IsRealGKModule m ρ' π' → IsIrreducibleGKModule ρ' π' → IsAdmissibleGKModule ρ' →
      IsRealGenericGKModule m π' → IsRealUnitarizableGKModule m ρ' π' →
        HasRealStandardParameter m ρ' π' ds' →
    ∀ s : ℂ, 1 ≤ s.re → (realPairLFactor ds ds').denominator s ≠ 0
```

In words: take an irreducible admissible generic unitarizable `(𝔤𝔩_n(ℝ), O(n))`-module on
`V : Type uV` with standard parameter `ds` and an irreducible admissible generic unitarizable
`(𝔤𝔩_m(ℝ), O(m))`-module on `W : Type uW` with standard parameter `ds'`. Then the entire
denominator of the real pair factor `realPairLFactor ds ds'` does not vanish at any `s` with
`1 ≤ Re(s)`; that is, `L(s, π × π')` is holomorphic and nonzero there.

The exponent bound `RealUnitaryGenericExponentBoundStatement` (`|Re t| < 1/2` for every block
exponent of a unitary generic module) is the Library theorem `realUnitaryGenericExponentBound`
(module `RealUnitaryGenericExponentBoundProof`), which has exactly that type; this module uses
it.

## Proof as implemented

The proof is a single term that combines three Library theorems.

1. `realUnitaryGenericPairRegularityReduction.{uV, uW}` (module
   `RealUnitaryGenericPairRegularityReductionProof`) proves
   `RealUnitaryGenericPairRegularityReductionStatement`: the exponent bound at universe `uV`,
   the exponent bound at universe `uW` and the right half-plane regularity of real pair
   `L`-factors together imply the target.
2. `realUnitaryGenericExponentBound` (module `RealUnitaryGenericExponentBoundProof`) proves
   `RealUnitaryGenericExponentBoundStatement`: every block exponent of the standard parameter of
   an irreducible admissible generic unitarizable module has absolute value `< 1/2`. Its
   universe is a parameter, so it is instantiated once at `uV` and once at `uW`.
3. `realPairLFactorRightHalfPlaneRegularity` (module `RealPairLFactorRegularityProof`) proves
   `RealPairLFactorRightHalfPlaneRegularityStatement`: the denominator does not vanish at `s`
   when `Re(s) + Re(t) + Re(t') > 0` for all block exponents `t` of `ds` and `t'` of `ds'`.

Applying the reduction to these three proofs gives the statement. The reduction does the
arithmetic: each block exponent is greater than `−1/2`, so `Re(s) + t + t' > 1 − 1/2 − 1/2 = 0`
when `Re(s) ≥ 1`. The complex case is the same term with the complex theorems
(`complexUnitaryGenericPairRegularity`, module `ComplexUnitaryGenericPairRegularityProof`).

## Declarations

- `realUnitaryGenericPairRegularity : RealUnitaryGenericPairRegularityStatement.{uV, uW}`
  (theorem).

## Provenance

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations` (in Chapter 11, PDF page = printed page + 11).
§11.5, printed p. 304 (PDF page 315), sets up irreducible admissible generic representations `π`
of `GL_n(F)` and `π'` of `GL_m(F)` over a local field `F`. Theorem 11.5.2, printed p. 305 (PDF
page 316): "If `π` and `π'` are unitary, then `L(s, π × π')` is holomorphic and nonzero for
`Re(s) ≥ 1`." The Library's `F = ℝ` statement expresses this as nonvanishing of the entire
denominator of its reciprocal-entire pair factor and takes the two standard parameters as
hypotheses; this proof does not construct them. Getz–Hahn refer to Barthel–Ramakrishnan (1994),
§2, for the Archimedean case; that proof is not used here. The provenance of the exponent bound
for `GL_n(ℝ)` (Badulescu–Renard 2010, Theorem 8.2) is described on the page of its proof module,
`RealUnitaryGenericExponentBoundProof`.
