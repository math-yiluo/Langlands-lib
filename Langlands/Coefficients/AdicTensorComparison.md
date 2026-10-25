# Tensor presentation of coefficient reductions and their inverse system

Author: Worker 13.

Let `R : Type u` be an arbitrary commutative ring and `I : Ideal R`. All
module carriers in this file also lie in `Type u`. No field, nontriviality,
flatness, finite-generation, principal-ideal or completeness assumption is
made. All comparisons are natural in every `R`-linear module map.

This is an internal construction from the published quotient functors in
`Langlands.Coefficients.AdicSystem` and Mathlib's
`TensorProduct.quotTensorEquivQuotSMul`. It does not independently transcribe
an external source. The published `AdicSystem` explains the coefficient
motivation; the present file supplies the natural tensor comparison left
open there. The pointwise equivalence in
`Langlands.Shimura.Coefficients.Lattice.torsionTensorEquiv` uses the same
Mathlib map; the new construction records quotient-ring linearity,
naturality, units and compatibility across the entire inverse system.

`tensorReductionIso I M` is the actual isomorphism of `R/I`-modules

\[
 (R/I)\otimes_R M\;\cong\;M/IM.
\]

It uses Mathlib's `R`-linear tensor-quotient equivalence and promotes it to
`R/I`-linearity by `LinearEquiv.extendScalarsOfSurjective`, using the
surjectivity of the quotient ring map. Both modules carry their existing
quotient-ring structures. The proved evaluation formulas are

\[
 \bar r\otimes x\longmapsto [rx],\qquad
 [x]\longmapsto 1\otimes x.
\]

`tensorReduction` assembles these into a natural isomorphism from
`ModuleCat.extendScalars (Ideal.Quotient.mk I)` to the existing
`reduction I`. Its naturality is proved on tensors `1 ⊗ x` using the
scalar-extension hom-extensionality lemma and the displayed formulas.

For every natural number `n`, `reductionRestrictIso I n` identifies reduction
by `I^n` followed by restriction to `R` with the existing
`powerReduction I n`; it is the identity on the actual quotient carrier.
`tensorPowerIso I n` composes this identification with the restricted tensor
comparison. Thus `tensorPower I n` is the actual tensor extension by
`R/I^n`, subsequently viewed as an `R`-module, and

\[
 e_n:\operatorname{tensorPower}_n\cong\operatorname{powerReduction}_n.
\]

`tensorPowerIso_unit` proves that the extension/restriction adjunction unit,
followed by `e_n`, equals the existing quotient natural transformation
`quotientMap I n`. The proof evaluates the maps at a module element and
uses `quotTensorEquivQuotSMul_mk_one_tmul`.

For `h : m ≤ n`, the natural transition is constructed by conjugating the
existing quotient transition `t_{n,m}`:

\[
 \operatorname{tensorTransition}_{n,m}=e_n\,;\,t_{n,m}\,;\,e_m^{-1}.
\]

The semicolon denotes composition in the displayed order. The theorem
`tensorTransition_tmul` proves, for every `a : R/I^n` and `x : M`, that

\[
 a\otimes x\longmapsto \operatorname{factorPow}_{n,m}(a)\otimes x.
\]

The proof lifts `a` to an element of `R`, evaluates the tensor-quotient map,
uses the actual quotient transition on the representative, evaluates the
inverse comparison, and applies tensor balancing. Hence the transported
map is the canonical coefficient map on tensors.

`tensorTransition_comparison` is the commuting comparison square.
`tensorTransition_refl` and `tensorTransition_comp` prove the identity and
composition laws by cancellation of the intervening isomorphisms and the
existing quotient-transition laws. `tensorTransition_unit` proves
compatibility of the extension units with every transition by composing
with the comparison and using the quotient-unit compatibility.

`tensorPowers` packages these maps into a functor from `ℕᵒᵖ` to the
category of endofunctors of `ModuleCat R`. `tensorPowersIso` identifies it
with the published quotient system `powers I`. `tensorFunctor` exchanges
the module and power arguments, and `tensorFunctorIso` is the resulting
natural isomorphism to `AdicSystem.functor I`. Its components are exactly
the `e_n` above, with compatibility proved both in the module and in the
power index. Index zero is included, with `I^0 = R` and its zero quotient.

This contribution constructs module functors, maps and isomorphisms. It
makes no exactness, completion, continuity, smoothness or cohomology claim.
The published limit construction is reused by import but is not enhanced
here. Sheafified reduction, geometric equivariance, sheaf inverse systems,
and identification with the required Harris coefficient sheaves remain
separate construction obligations.
