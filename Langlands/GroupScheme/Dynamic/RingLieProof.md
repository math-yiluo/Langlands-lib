# Dynamic Lie-weight descriptions over arbitrary rings

Worker 3483 (proof development); Worker 292 (submission and validation).

This module proves the published proposition
`Langlands.GroupScheme.DynamicRingLieStatement.{u}` for every universe `u`.

The entry theorem `Langlands.GroupScheme.dynamicRingLie.{u}` has exactly that target. The base is any
commutative ring, including nonreduced, disconnected and zero rings. The
ambient group scheme is relatively affine and locally of finite presentation;
no smoothness or flatness is assumed. The three clauses compare actual
dual-number subgroup membership in Z, P and U with the zero, nonnegative and
positive integer-power adjoint weight submodules, respectively.

The source and exact scope are recorded in
[`RingLieStatement.md`](RingLieStatement.md): Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition 2.1.8(1),
printed pp.53–54 / PDF pp.79–80, registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The proof extends the implemented route of the published field proof
[`LieProof`](LieProof.md). The published ring-general
`splitTorus.universalAdjointCoefficients` gives a finite family of actual Lie
vectors, indexed by the integral exponents of the rank-one split torus. The
published `RelativeAdjointWeights` and `ExponentCharacters` identify each
coefficient with its all-test character weight equation and show that a pure
weight has a singleton coefficient family. The fixed exponent character is
defined over the arbitrary base; no identification of the entire character
lattice with a single integer lattice is assumed. The finite coefficients
sum to the original vector, so vanishing of forbidden coefficients detects
membership in the corresponding sum of weight submodules.

The Laurent, orbit and assembly helpers adapt the field proof over a
commutative ring. The algebra map `(R[t,t⁻¹])[ε] → (R[ε])[T,T⁻¹]` preserves
both the constant and infinitesimal Laurent coefficients. On actual scheme
points it identifies the universal adjoint vector with the conjugation
orbit of the dual-number point. The imported generic chart comparison and
dynamic coefficient criteria then identify membership in Z, P and U with
vanishing outside degree zero, in negative degrees, and in nonpositive
degrees, respectively. The final theorem combines those criteria with the
weight-submodule criteria.

The entry theorem obtains absolute affineness from the affine structure
morphism over `Spec R` and uses the local finite type instance supplied by
local finite presentation. Thus it retains exactly the hypotheses of the
published target.
