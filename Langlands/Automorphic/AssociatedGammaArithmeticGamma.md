# The gamma factor of arithmetic local factors

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaArithmeticGamma`). It links the arithmetic Hecke
family's local factors to the Library's arithmetic pair gamma factor, which is the
arithmetic side of `IsPairGammaMatch` in the proof of `AssociatedGammaStatement`
(Henniart 2000, Théorème 2.3). Internal deduction from Library definitions.

## Result

`IsArithmeticPairLocalFactors.exists_gamma`: let `B`, `B'` be Weil–Deligne representations
of the local Weil group of `K`, and `f` a factor triple of `(classOf B, classOf B')` with dual
pair `(dualClass (classOf B), dualClass (classOf B'))`, in the sense of the published
`IsArithmeticPairLocalFactors`. Then some `H` is an arithmetic pair gamma factor of
`(classOf B, classOf B')` (`Correspondence.IsArithmeticPairGammaFactor`), and the gamma factor
`ε(s) L∨(1 - s) / L(s)` of `f` has the rational continuation `H`
(`RankinSelberg.HasRationalContinuation`).

## Proof

Let `T = B ⊗ B'`, `P` its Euler polynomial and `Pd` that of `T^∨`, at the published inertia
subgroup and geometric Frobenius. The L-factor of `f` is the evaluation of `1/P`; the dual
L-factor is the evaluation of `1/Pd`, after identifying `B^∨ ⊗ B'^∨` with `T^∨`
(`tensorDualEquiv`, `rationalLFactor_eq_of_equiv`). Take `H` to be the epsilon monomial
times the reflected L-ratio class of `X ⊗ Y`; by `rationalLRatio_eq` this is
`rationalGammaExpression δ c m P Pd`. The polynomials are nonzero (constant coefficient
`1`), so on a right half-plane `P(q^-s) ≠ 0` and `Pd(q^-(1-s)) ≠ 0`
(`eval_spectralPoint_ne_zero_of_ne_zero`, `eval_spectralPoint_one_sub_ne_zero`). There the
gamma factor of `f` equals the polynomial gamma expression (`RationalEvaluation.eval_inv`),
which has the rational continuation `rationalGammaExpression δ c m P Pd` by the lemma
`hasRationalContinuation_polynomialGammaExpression` (module `Langlands.Automorphic.AssociatedGammaLocalLink`).
