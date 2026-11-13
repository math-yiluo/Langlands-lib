# Renard VI.10.4, Remark 2, from the Theorem with Remark 1 and the VI.7.4 idempotents

Worker 117. Derived conditional reduction for Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`), VI.10.4,
Remarks 1–2, printed p.212 / PDF p.218, with VI.7.4, printed pp.185–186 /
PDF pp.191–192.

## Statement

`BernsteinCentralIdempotentFunctionReductionStatement.{uF, uV}` is the
implication

> `BernsteinCenterFunctionsStatement.{uF, uV}` →
> `BernsteinCentralIdempotentStatement.{uF, max uF uV}` →
> `BernsteinCentralIdempotentFunctionStatement.{uF, uV}`.

All three are unchanged published statements:

- `BernsteinCenterFunctionsStatement` is VI.10.4, Theorem, second sentence,
  with Remark 1, in the published form. Every element `z` of the centre of
  `SmoothRep ℂ G(F)` (carriers in `Type (max uF uV)`) acts on every induction
  `i_{P_a}^G(ρ_a ⊗ ω)` by a scalar, `z` is determined by these scalars, and every
  compatible family of polynomial functions arises this way. Only its second
  conjunct, injectivity, is used here: two central elements whose components
  agree on every `i_{P_a}^G(ρ_a ⊗ ω)` are equal.
- `BernsteinCentralIdempotentStatement` is VI.7.4, first paragraph: central
  idempotents `e_s` that are the identity on the block `M(G)_s` and zero on
  every other block. It is used at carrier universe `max uF uV`, the universe
  of the target.
- `BernsteinCentralIdempotentFunctionStatement` is VI.10.4, Remark 2, the
  target. `z` is the identity on the saturated block of `s` and zero on every
  other saturated block exactly when, for every cuspidal datum `a` and every
  `ω ∈ X(M_a)`, `z` acts on `i_{P_a}^G(ρ_a ⊗ ω)` by `1` if `a` lies in `s` and by
  `0` otherwise.

`bernsteinCentralIdempotentFunction_reduction` proves the implication.

## Provenance

The statement is internal: it is not a translation of a single assertion of
Renard. Renard states Remark 2 without proof, as a consequence of the Theorem
and Remark 1. This reduction records that consequence: given Remark 1 and the
VI.7.4 idempotents, Remark 2 follows. Neither premise is proved here, and the
unit does not prove `BernsteinCentralIdempotentFunctionStatement`
unconditionally.

## Proof

The helper `centralIdempotent_scalar_of_mem` is proved in this module without
conditions. Suppose a central element `z` is the identity on every object of
the saturated block of `s` and zero on every object of the saturated block of
every `t ≠ s`. Then `z` acts on every object `V` of the saturated block of any
`t` by the scalar `1` if `t = s` and `0` otherwise. (Case split on `t = s`, then
rewrite with the hypothesis.)

Fix `F, G, T, i, ν`, a standard family, an inertial class `s` and `z`.

1. **Forward direction.** Let `a` be a cuspidal datum and `ω ∈ X(M_a)`. The
   helper lemma `twistInduction_mem_saturatedBlock` (module
   `BernsteinCenterFunctionsBasics`) puts `i_{P_a}^G(ρ_a ⊗ ω)` in the
   saturated block of `bernsteinInertialClass a`. So
   `centralIdempotent_scalar_of_mem` with `t = bernsteinInertialClass a` gives
   the required scalar. This direction does not use either premise.
2. **Converse.** Take the idempotents `e` from
   `BernsteinCentralIdempotentStatement.{uF, max uF uV}`. Its conditions are
   stated with `bernsteinBlockProperty`. `bernsteinBlockProperty_iff_saturated`
   turns them into the saturated-block conditions: `e s` is `𝟙` on the
   saturated block of `s` and `0` on that of every `t ≠ s`. By step 1 applied to
   `e s`, `e s` acts on every `i_{P_a}^G(ρ_a ⊗ ω)` by the same scalar as `z`
   (the hypothesis). So `z.app` and `(e s).app` agree on all these objects
   (`SmoothRep.hom_ext'` and pointwise equality). The injectivity conjunct of
   `BernsteinCenterFunctionsStatement` then gives `z = e s`, and the
   conditions of `e s` are the required ones.

In both directions the membership and scalar lemmas are applied one step at a
time (`have hmem := …; have hmemω := hmem ω; …`). Passing them as arguments
of a single application made elaboration time out. The module uses
`backward.isDefEq.respectTransparency.types false`, like the statement module,
and no heartbeat options.
