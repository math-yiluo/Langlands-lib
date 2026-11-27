# Every supercuspidal class of `GL_{k+1}(K)` contains a maximal simple type

Module `Langlands.BushnellKutzko.SupercuspidalClassMaximalTypeStatement`, namespace
`Langlands.BushnellKutzko`. It defines the proposition
`SupercuspidalClassMaximalTypeStatement.{uK, uV, uT}` and does not prove it.

## Statement

For every prime `p`, every `K : PadicField.{uK} p`, every `k : ℕ` and every supercuspidal
class `π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat` of
`GL_{k+1}(K)`, one of the following holds:

- there are `t, m : ℕ` with `1 ≤ t`, `t ∣ k + 1` and `1 ≤ m`, and a pair
  `x ∈ glMaximalSimpleTypesAt.{uK, uT} (k + 1) K.Carrier t m` such that `π` contains `x`;
- there is a pair `x ∈ glMaximalLevelZeroSimpleTypes.{uK, uT} (k + 1) K.Carrier` such that
  `π` contains `x`.

Containment is `SupercuspidalClassContainsType K π x.2`
(`Langlands/BushnellKutzko/SupercuspidalClassContainment.lean`): some representative of `π`
has a nonzero `J`-homomorphism from the representation `λ` of the pair `x = (J, λ)` to its
restriction to `J`.

The field `K.Carrier` carries the topology, the valuation relation and the local-field
structure of `K.canonicalTopologicalData`, and `GL_{k+1}(K)` the topology inferred from that
of the field. These are the instances behind the class space and behind the two sets of
pairs.

`glMaximalSimpleTypesAt (k + 1) F t m` consists of the pairs exhibited by simple type data of
kind (a) of BK93 (5.5.10): a simple stratum `[𝔄, m, 0, β]` in `End_F(F^{k+1})` with principal
order `𝔄` of period `e(𝔄 | 𝔬_F) = t`, whose `𝔄`-centraliser `𝔅_β` has period
`e(𝔅_β | 𝔬_E) = 1` over `𝔬_E`, `E = F[β]`. `glMaximalLevelZeroSimpleTypes (k + 1) F`
consists of the pairs exhibited by data of kind (b) on a principal order of period one. Both
are the maximal simple types of BK93 §6.2 (`Langlands/BushnellKutzko/GLMaximalSimpleTypeSets.lean`).

The universes are independent: `uK` for the field, `uV` for the carriers of the class
representatives and `uT` for the carriers of the pairs. A simple type is finite-dimensional,
so for each `uT` a copy of it with carrier in `Type uT` exists.

## Provenance

The statement transfers to the Library's class objects the following results on
representations, which the Library states as
`Langlands.BushnellKutzko.SupercuspidalSimpleTypeExistenceStatement` (BK93 (8.4.1), existence)
and `Langlands.BushnellKutzko.SupercuspidalSimpleTypeMaximalityStatement` (BK93 (6.2.1)). It
is not a numbered result of a source in this form.

- BK93 (8.4.1): every irreducible supercuspidal representation `π` of `GL(N, F)` contains a
  simple type `(J, λ)`.
- BK93 (6.2.1): if a simple type `(J, λ)` is contained in an irreducible supercuspidal
  representation, then the `𝔬_E`-order `𝔅` attached to it is maximal, that is,
  `e(𝔅 | 𝔬_E) = 1`. BK93, p. 204, calls such a simple type maximal. For data of kind (b)
  (BK93 (5.5.10)(b), with the convention `E = F`, `𝔅 = 𝔄`) the condition is `e(𝔄 | 𝔬_F) = 1`.
- The period `t = e(𝔄 | 𝔬_F)` of a principal order in `End_F(F^N)` divides `N`, and the level
  `m` of a simple stratum `[𝔄, m, 0, β]` is positive. BK94, p. 126: "The principal order 𝔄 is
  determined up to G-conjugacy by its period e(𝔄), which can be any positive divisor of N."

## Sources

- C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
  (1993): (8.4.1), printed p. 297 (PDF p. 309); (6.2.1), printed p. 202 (PDF p. 214); the
  definition of a maximal simple type before (6.2.3), printed p. 204 (PDF p. 216).
  Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
  SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
- C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994),
  §3, after (3.7) and before (3.8), printed p. 126 (volume PDF p. 139).
  Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
  SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
