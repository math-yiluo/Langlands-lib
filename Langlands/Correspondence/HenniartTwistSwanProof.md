# Proof of the supercuspidal twist Swan bound

Module `Langlands.Correspondence.HenniartTwistSwanProof` proves the published statement
[`SupercuspidalTwistSwanBoundStatement`](HenniartTwistSwanStatement.md) of Task 7373:

```lean
theorem Langlands.Henniart.supercuspidalTwistSwanBound :
    Langlands.Henniart.SupercuspidalTwistSwanBoundStatement.{uK, uV}
```

The field universe `uK` and the representation-carrier universe `uV` are arbitrary and
independent. The theorem has no hypotheses beyond those of the statement.

## What is proved

Let `K` be a p-adic field, `n = k + 1 ≥ 1`, `χ` a quasicharacter of `K^×` and `π` a
supercuspidal class of `GL_n(K)` with Swan exponent `s`, in the sense of
`HasSupercuspidalSwan K π s`: the conductor of `π` is a finite natural number `a` with
`a − n = s` (truncated subtraction in `ℕ`). Write
`sw(χ) = Numerical.characterSwanExponent K χ`, the multiplicative conductor of `χ` minus
one (truncated). Then the twist `Numerical.supercuspidalCharacterTwist K k χ π` of `π` by
`χ ∘ det` has a Swan exponent `s'` in the same sense, with `s' ≤ max(s, n · sw(χ))`, and
`s' = max(s, n · sw(χ))` whenever `s ≠ n · sw(χ)`. This includes rank one (`k = 0`).

## Implemented proof

The proof is a single term. It applies the published reduction

- `Langlands.Henniart.supercuspidalTwistSwanBoundReduction :
  SupercuspidalTwistSwanBoundReductionStatement.{uK, uV}` (Task 7902, module
  `Langlands.Correspondence.HenniartTwistSwanReductionProof`), whose type is the
  implication L0 → L2 → T2 → `SupercuspidalTwistSwanBoundStatement.{uK, uV}`,

to the three published level theorems, in that order and all at universes `uK, uV`:

- L0, `Langlands.BushnellKutzko.normalizedLevelExistence :
  NormalizedLevelExistenceStatement.{uK, uV}` (Task 7680, module
  `Langlands.BushnellKutzko.NormalizedLevelExistenceProof`): every class `a` in
  `SmoothDualClass` of `GL_n(K)`, `n ≥ 1`, has a rational `x` with
  `IsNormalizedLevel K n a x`;
- L2, `Langlands.BushnellKutzko.normalizedLevelTwist :
  NormalizedLevelTwistStatement.{uK, uV}` (Task 7682, module
  `Langlands.BushnellKutzko.NormalizedLevelTwistProof`): if `x` and `y` are normalized
  levels of `a` and of its `SmoothDualClass.twist` by `χ ∘ det`, and `t` is the
  multiplicative conductor of `χ` minus one, then `y ≤ max(x, t)`, with equality when
  `x ≠ t`;
- T2, `Langlands.BushnellKutzko.supercuspidalSwanLevel :
  SupercuspidalSwanLevelStatement.{uK, uV}` (Task 7683, module
  `Langlands.BushnellKutzko.SupercuspidalSwanLevelProof`): if the automorphic class of a
  supercuspidal class `π` of rank `n = k + 1` has normalized level `x`, then the conductor
  of `π` is a natural number `c` with `((c − n : ℕ) : ℚ) = n · x`.

Inside the reduction, L0 supplies the levels of `π` and of its twist, T2 identifies the
rank-scaled levels with the natural Swan exponents (and supplies the finite conductor of
the twist), and L2 yields the maximum bound and the equality case; see the reduction's
Markdown for the details. Since all three inputs are discharged by theorems, none
remains a hypothesis of the final theorem. The four inputs are imported from their Library
modules; this module adds no other declarations.

`lean_check` reports no errors or warnings and the axioms `propext`, `Classical.choice`
and `Quot.sound` only.

## Provenance

This is the supercuspidal conclusion of Lemma `lem:level`(ii) of the operator note
*Numerical local Langlands for GL_n: counts on the two sides and the recommended route*
(`operator-numerical-llc-route-2026-11-16`, §4.4, printed p. 16;
`numerical-LLC-route.tex`, line 627), whose proof deduces it at line 641 from the level
bound of (ii) and the identity `sw(π) = n · ℓ(π)` of (i) (line 625, resting on
Proposition `prop:T2`), applied to `π` and to its twist. The route uses the level
comparison of Bushnell (1987) and Bushnell–Kutzko through L0, L2 and T2, not Henniart's
(1988, §6.7) argument through the Jacquet–Langlands correspondence.

The theorem name and the one-term proof follow an unreviewed draft by Worker 408
(Task 7339).
