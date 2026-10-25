# Pointed base-change compatibility of root monodromy

Authors: Worker 92 and Worker 437.

The proof and its explanation reuse Worker 92's shared draft, revision 1.
Worker 437 checked them against the published prerequisites and prepared
this contribution for independent review.

This module proves the proposition
`Langlands.TateTwist.Geometry.TwistMonodromyBaseChange` from
`TwistMonodromyBaseChangeStatement`. Its four components compare the
existing selected integral, prime integral, selected rational and prime
rational root actions after restriction along the actual pointed
fundamental-group homomorphism.

## Assumptions and meaning

Fix same-universe schemes `S, S'`, a morphism `b : S' ⟶ S`, a field `Ω`,
and `t : Spec Ω ⟶ S'`. Retain the explicit finite-fibre proofs at `t` and
`t ≫ b`. For every group element `g` and root-module vector `x`, the
conclusion is

```text
rho_(t ≫ b)(fundamentalGroupMap b t (t ≫ b) rfl ht hs g)(x)
  = rho_t(g)(x).
```

The two actions use the same root carrier over `Ω`. The selected laws
retain an arbitrary predicate `P` and finiteness and etaleness of
`mu S n.val` and `mu S' n.val` for every positive selected index.
The prime laws retain `Fact p.Prime` and the corresponding assumptions
at every order `p ^ n`, including `n = 0`. The proof does not establish
these geometric hypotheses.

## Implemented proof

`integralMonodromyBaseChange` applies subtype and function
extensionality to a coherent selected root family. At index `n`,
both existing integral actions reduce to finite root monodromy.
The imported `levelMonodromy_baseChange` proves their equality.
The four explicitly quantified finite-etaleness families are locally
installed so that each coordinate uses the stated geometric hypotheses.

`primeMonodromyBaseChange` applies the same argument to the existing
coherent prime-power root sequence, using finite order `p ^ n`.

`rationalMonodromyBaseChange` uses tensor-product induction over `Z`.
On a pure tensor, the two `rationalMonodromy_tmul` formulas reduce
the claim to the selected integral comparison. Congruence under
`y ↦ q tensor y` finishes that case; preservation of zero and addition
handles the remaining cases.

`rationalPrimeMonodromyBaseChange` first uses linear-map extensionality
and the prime integral result to equate the two existing
`primeMonodromyHom` maps over `Z_p`. Applying scalar extension
`LinearMap.baseChange Q_p` to this equality and evaluating it at `x`
proves the desired comparison. This retains the prime rational
construction `Q_p tensor over Z_p`; it does not interchange its tensor
base with the selected rational construction's `Z`.

`twistMonodromyBaseChange` assembles these four proofs in exactly the
order of the target proposition.

## Provenance and scope

This is an internal derived proof. Its finite geometric input is
`TwistFiniteBaseChange`, which obtains the finite equality from the
canonical pullback of actual `mu` schemes and finite-etale fibre
transport. The present proof extends that equality through the already
constructed coherent root modules and their scalar extensions. It
introduces no new actions, comparisons, roots, generators or
trivializations.

The arbitrary selected predicate includes the full and away systems.
The result does not prove finite etaleness, rank, rational topological
claims, a restricted-product comparison, Weil-pairing compatibility,
unpointed base-point independence or completion of the PEL construction.
