# The conductor functional on induced character differences

Worker 4803 wrote this supporting module of
`SpectralConductor.spectralConductorRankOneReduction`.

## Setting

Let `M` be an actual finite Galois subfield of the algebraic closure. Let `L` be an
intermediate field with `hLM : L.field ≤ M`, and let `χ, χ'` be continuous
characters of `W_L = weilSubgroup F L`.

- `GalM F M` is `Gal(M/F)`. `restrictionM F M` is restriction from the local Weil
  group to it. On Weil inertia it agrees with `weilInertiaRestriction`, and it
  evaluates as the original automorphism (`restrictionM_apply`).
- `fixingM F M L` is the subgroup of `Gal(M/F)` fixing `L`. `mem_weilSubgroup_iff`: a
  Weil element lies in `W_L` exactly when its restriction to `M` lies in `fixingM`.
- `inertiaM_normal`: inertia is normal (lower group zero). `conjInertia` is
  conjugation on it. `galoisLowerCount_conj`: the count `m` is conjugation-invariant,
  because every lower group is normal. `sum_conjInertia`: class sums over inertia are
  invariant under conjugating the argument.
- `IsPresentedAt F M L χ`: `χ` is trivial on inertia elements of `W_L` that act
  trivially on `M`. Then `χ` takes equal values on inertia elements with equal
  restriction (`IsPresentedAt.eq`).
- `liftL`: the section element of an inertia element fixing `L`, as an element of `W_L`.
- `differenceFunction`: `χ(liftL δ) - χ'(liftL δ)` on inertia elements fixing `L`,
  and `0` otherwise.
- `inertiaL F M L = fixingM ⊓ inertiaM` is the inertia group of `M/L` inside `Gal(M/F)`.
- `lClassSum F M L hLM χ = |inertiaL|^{-1} Σ_{δ ∈ inertiaL} m(δ) (1 - χ(liftL δ))`, where `m` is
  the count of lower groups of `M/F`.

## Main results

`inertiaTrace_induce`: the trace of `Ind_L(χ - χ')` at the section element `s(γ)` is
`Σ_q differenceFunction(t_q γ t_q^{-1})`. The sum runs over the right cosets `q` of
`W_L` in `W_F`, and `t_q` is the restriction of the chosen representative. Proof: the
Library's Frobenius formula `CommonClosure.trace_induce` sums over cosets fixed by
`s(γ)` of the trace at the factor. `coset_out_mul_eq_iff` and `factor_out_mul` show
that the coset is fixed exactly when the conjugate `q.out s(γ) q.out^{-1}` lies in
`W_L`, i.e. when `t_q γ t_q^{-1}` fixes `L`, and that the factor is that conjugate. It
lies in inertia and has the same restriction to `M` as `liftL (t_q γ t_q^{-1})`. So the
presentation hypotheses give equal character values.

`conductorFunctional_induce`: the functional of `M` at `Ind_L(χ - χ')` is
`-(#cosets) |I(M/F)|^{-1} Σ_δ m(δ) differenceFunction(δ)`. Proof: the trace at `1` is the
degree, which is `0` (`inertiaTrace_one`, `degree_induce`). Exchange the sums over
inertia and cosets. For each coset, reindex the inertia sum by conjugation
(`sum_conjInertia`).

`conductorFunctional_induce_eq`: in terms of the class sums of `M/L`,
`a_M(Ind_L(χ - χ')) = #cosets · |I(M/L)| / |I(M/F)| · (lClassSum χ - lClassSum χ')`
(`sum_differenceFunction`).

## Source

This is the degree-zero case of Serre, *Local Fields*, VI §2, Proposition 4 and its
proof, printed pp. 101–102 (PDF pp. 108–109): `a_G` restricted to `H` differs from
`f_{K'/K} a_H` only at `1`, and the degree-zero class kills that difference. The
identity `H_i = G_i ∩ H` (IV §1, Proposition 2, printed p. 62, PDF p. 69) holds by
construction: the class sum of `M/L` uses the lower groups of `M/F`. Module
`SpectralConductorRankOneBridge` proves this agrees with the lower groups of `M/L`.
The factor `#cosets · |I(M/L)| / |I(M/F)|` is the residue degree `f_{L/F}`
(module `SpectralConductorDegree`).
