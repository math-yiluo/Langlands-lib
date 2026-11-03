# First-order characters on the actual principal units

Worker 84 specifies the internal derived proposition
`Langlands.HarmonicAnalysis.PadicDeepUnitCharacterStatement.{u}`.
This module defines the target and contains no proof.

For every prime `p`, every arbitrary-universe finite p-adic field `F`,
every supplied topological realization `T`, every continuous nontrivial
unitary additive character `psi`, every actual field scalar `c` and
every natural principal-unit level `n`, assume

```text
v_T(c) * exp(-2*n) <= exp(n_T(psi)).
```

Here `v_T` is exactly `T.discreteValuation`, `exp` is `WithZero.exp`
into the ordered value group with zero, and `n_T(psi)` is the existing
additive conductor. The conclusion asks for a continuous multiplicative
character `eta : T.principalUnits n -> Circle` with the actual value

```text
eta(u) = psi(c*(u-1))
```

on every element of that subgroup, and a natural `k` with
`eta^(p^k) = 1`. Since `p` is prime, `p^k` is positive, so this is a
finite-order conclusion. The exponent `k = 0` is allowed for the trivial
character. Every prime, including two, and the cases `c = 0` and `n = 0`
are retained.

The subgroup, topology and conductor are the published constructions
in `Langlands.HarmonicAnalysis.Conductor`. The topology of the unit
group and its subgroup are induced from the supplied `T.topology`.
Its level convention is `v_T(u)=1` and `v_T(u-1)<=exp(-n)`, including
`U^0=O_F^x`. The additive lattice of level `m` is `pi^(-m) O_F`;
the character is trivial on the lattice of level `n_T(psi)`.
Thus the displayed bound kills the actual multiplication error
`c*(u-1)*(v-1)`. It does not ask for an unspecified character formula
or filtration supplied as extra data.

## Internal derivation and scope

This target is an internal consequence of the published valuation and
conductor APIs, rather than a statement attributed verbatim to Harris
or Henniart. The identity

```text
c*(u*v-1) = c*(u-1) + c*(v-1) + c*(u-1)*(v-1)
```

and the ultrametric valuation show that the formula is multiplicative
under the stated quadratic bound. Its continuity follows from the
actual field operations and the additive character's continuity.
The positive normalized order of the rational prime in
`Langlands.LocalField.Normalization.Proof` puts
`p^k*c*(u-1)` in the additive conductor lattice for a sufficiently
large natural `k`, uniformly over the subgroup. Additivity then gives
the p-power order assertion. These are derivation inputs, not extra
hypotheses of the target.

This is one prerequisite for the first-order deep-unit route to
`Langlands.Global.AuxiliaryCharacterStatement`. It asserts no
nontriviality, extension to all units or to the multiplicative field
group, norm–trace comparison, arbitrary-depth detection or exact Galois
stabilizer. In particular, it keeps the explicit quadratic bound so
that a consumer can use levels where the formula is still nontrivial;
merely choosing very deep levels for a fixed scalar would give a
trivial character and would not solve those remaining obligations.
