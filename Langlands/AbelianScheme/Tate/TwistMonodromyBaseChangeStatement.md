# Pointed base change for integral and rational root monodromy

Author: Worker 92.

This module states four laws for the existing geometric actions on actual
Tate twists. All declarations are Prop-valued definitions; they provide no
proofs of these laws.

## Internal provenance and the common base morphism

The statements combine the already constructed actions from
`TwistIntegralMonodromy`, `TwistPrimeMonodromy`,
`TwistRationalMonodromy` and `TwistRationalPrimeMonodromy` with the
actual induced fundamental-group homomorphism in
`AlgebraicGeometry.FiniteEtale.Pullback`. Their internal meaning is
restriction of these actual root actions along pointed base change;
no external theorem is newly cited and no replacement action is supplied
as data.

Every law quantifies schemes `S, S'` and a field `Ω` in the same universe,
a morphism `b : S' ⟶ S`, a point `t : Spec (.of Ω) ⟶ S'`, and finite-fibre
proofs `ht` and `hs` for all finite-etale covers at `t` and `t ≫ b`
respectively. Write

```text
b_* = fundamentalGroupMap b t (t ≫ b) rfl ht hs.
```

This is the published homomorphism from `FundamentalGroup t ht` to
`FundamentalGroup (t ≫ b) hs`, obtained from actual pullback of covers
and the canonical fibre comparison. Each law quantifies every group
element `g` and every element `x` of its indicated root module, and states

```text
rho_(t ≫ b)(b_*(g))(x) = rho_t(g)(x).
```

The root module is the same at both points because the coefficient field
is unchanged. Equality on this common carrier does not assert that either
action is trivial. Its geometric basis is that the canonical comparison
of `mu` points preserves the root coordinate; extending that finite
comparison coordinatewise or by scalar extension yields these targets.

## Four laws and their hypotheses

| Proposition | Existing action | Common carrier |
| --- | --- | --- |
| `IntegralMonodromyBaseChange` | `integralMonodromy` | `Divisibility.Integral Ω P` |
| `PrimeMonodromyBaseChange` | `primeMonodromy` | `Integral Ω p` |
| `RationalMonodromyBaseChange` | `rationalMonodromy` | `Divisibility.Rational Ω P` |
| `RationalPrimeMonodromyBaseChange` | `rationalPrimeMonodromy` | `Rational Ω p` |

For the selected integral and rational laws, `P : ℕ → Prop` is arbitrary.
`Index P` consists of the positive orders satisfying `P`. The four
explicit geometric hypotheses are finiteness and etaleness of
`(mu S n.val).X.hom` and `(mu S' n.val).X.hom` for every `n : Index P`.
The same `P` is retained at both bases. No nonemptiness, directedness,
rank or invertibility assumption is substituted for these hypotheses.
Taking `P n := True` gives the full system; taking
`P n := Nat.Coprime n m` gives the away-from-`m` system, including the
prime-to-`p` case.

The prime laws quantify `p : ℕ` with `Fact p.Prime` and assume finiteness
and etaleness of `mu` at both bases at every order `p ^ n`, for every
natural `n`, including zero. They keep the same prime at both bases.

The selected integral carrier is the existing coherent subgroup of the
product of finite root groups. The prime integral carrier is the existing
coherent prime-power root sequence. The former retains its
profinite-integer scalar action and the latter its `Z_p` scalar action;
no new scalar structure appears in these statements.

The selected rational carrier is `Q tensor over Z` with the selected
integral root module. The prime rational carrier is `Q_p tensor over Z_p`
with the prime integral root module. Their existing actions are the
respective scalar extensions. The two tensor bases are not interchanged.

`TwistMonodromyBaseChange` is the conjunction of the four propositions in
table order. All its quantified schemes, field, points, geometric
hypotheses, selections, prime instances, group elements and vectors belong
to its constituents; none is replaced by a supplied equivariance proof.

## Scope

These are statement targets only. They do not prove finite etaleness of
roots of unity or supply geometric instances. The geometric application
may impose further assumptions to establish those hypotheses, but the
conditional action comparison requires only the hypotheses displayed
here. The statements add no rational topology, restricted-product
comparison, finite-adelic bundle equality, Weil pairing compatibility,
unpointed base-point independence or PEL completion claim. They concern
the existing geometric monodromy, without choosing roots or a twist
trivialization.
