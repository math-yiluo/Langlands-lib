# Proof of rank-one highly ramified twist stability

Worker 1786 proves `Langlands.LocalFactor.rankOneStability.{u}` with exact
type `Langlands.LocalFactor.RankOneStabilityStatement.{u}`.
Worker 1813 contributes bounded-conductor separation and the full witness
coset theorem in `RankOneStabilityCoset`. Workers 649, 655 and 394 are
credited there for adapted published implementations. Worker 784 is credited
for the finite-level duality argument adapted in `RankOneStabilityHelpers`.

The proof retains every quantified prime, arbitrary p-adic carrier universe,
supplied topological data, actual continuous quasicharacter, and nontrivial
continuous additive character. It adds no assumptions to the published
target. The target pair and its imported pairs are unchanged.

Write `a = a(chi) >= 2`, `n = n(psi)`, `k = floor(a/2)` and
`m = a-k = ceil(a/2)`. The lattice `L_j` consists of elements of normalized
order at least `-j`. In particular `L_(-m)` has positive depth.
The numerical facts used in Lean are
`0 < m < a`, `a <= 2*m`, `a = m+k` and `k <= m`.
They include the even-conductor endpoint and every residue characteristic.

For each twisting character with `2*a(eta) <= a`, the conductor of `eta`
is strictly less than `a`. The published different-conductor product
theorem gives `a(chi*eta) = a`. Both characters are therefore ramified.
`conductor_and_L` unfolds the actual rank-one constructors to prove that
both rational L factors equal one and both numerical L representatives
equal one at every complex spectral parameter.

`exists_deep_linearization` constructs `c != 0` such that
`chi(1+h) = psi.complex(c*h)` for `h in L_(-m)` and
`ord(c) = -(a+n)`. This uses the actual additive character
`deepLatticeCharacter`, finite lattice duality, and conductor minimality;
its implementation is described in `RankOneLinearization.md`.
Set `d = Units.mk0 c` and `gamma = d^(-1)`. The actual order law gives
`ord(gamma) = a+n`.

For every allowed `eta`, its conductor is at most both `k` and `m`.
`gauss_integral_twist` then gives the identity at spectral parameter zero,
with multiplier `eta(d^(-1))`. Its implementation averages over the finite
additive quotient `L_(-m)/L_(-a)`, localizes both Gauss integrals to
`x-c in L_(n+m)`, and uses `x/c in U^k` there. All integral rotations
preserve the identical supplied regular additive Haar measure. The finite
averaging and integrability arguments are described in
`RankOneStationaryPhase.md`.

Because the actual conductors of `chi*eta` and `chi` coincide, the
published formula `epsilonAt_eq_zero_mul` gives their common spectral
multiplier `exp(-(a+n)*s*log(q))`. Applying it to the zero-parameter
identity proves the required epsilon equality for every complex `s`
and every supplied Haar measure. This establishes
`RankOneTwistWitness T chi psi gamma` without a witness premise.

Finally, `rankOneTwistWitness_iff_mem_coset` applies to this constructed
witness. If `gamma'` is another witness, nonvanishing of the actual
epsilon factor allows cancellation at one Haar measure and parameter zero.
Every character of conductor at most `k` then takes value one on
`gamma'*gamma^(-1)`. Character separation on the discrete quotient by
the open subgroup `U^k` proves membership in that subgroup. Conversely,
membership makes all allowed twisting evaluations equal, so the witness
identity transfers to `gamma'` for every Haar measure and spectral parameter.
There is no additional valuation premise on `gamma'`.

This is an internal proof route for the published rank-one specialization
of Deligne–Henniart, Theorem 4.6, printed page 110. It uses `1+h` only on
the sufficiently deep lattice where its quadratic error lies in the
conductor kernel. It does not assert a truncated-exponential formula at
other depths. The original-source translation and conventions are in the
unchanged `RankOneStabilityStatement.md`:

- Deligne–Henniart (1981), sections 0.1–0.6 and 4.1–4.7, especially
  Theorem 4.6 and Lemma 4.7, printed pages 108–110;
  literature ID `deligne-henniart-1981-variation`, SHA-256
  `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
- Tate (1979), sections 3.2.6, 3.4.3 and 3.4.5, printed pages 14–15
  (PDF pages 23–24); literature ID
  `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The Lean proof uses the published actual conductor, Gauss-integral and
spectral-law theorems. No source theorem is introduced as an axiom.
The general virtual-representation stability theorem is outside this
rank-one proposition's scope.
