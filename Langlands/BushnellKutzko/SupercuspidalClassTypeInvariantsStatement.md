# Torsion number and Swan exponent of a supercuspidal class containing a maximal simple type

Module `Langlands.BushnellKutzko.SupercuspidalClassTypeInvariantsStatement`, namespace
`Langlands.BushnellKutzko`. It defines the proposition
`SupercuspidalClassTypeInvariantsStatement.{uK, uV, uT}` and does not prove it.

## Statement

For every prime `p`, every `K : PadicField.{uK} p`, every `k : ℕ` and every supercuspidal
class `π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat` of
`GL_{k+1}(K)`, with `N = k + 1`:

- (a) for all `t, m : ℕ` with `1 ≤ t` and `1 ≤ m` and every pair
  `x ∈ glMaximalSimpleTypesAt.{uK, uT} (k + 1) K.Carrier t m` contained in `π`, one has
  `t ∣ k + 1`, `Henniart.Numerical.supercuspidalTorsionNumber K π = (k + 1) / t` and
  `Henniart.Numerical.HasSupercuspidalSwan K π (m * ((k + 1) / t))`;
- (b) for every pair `x ∈ glMaximalLevelZeroSimpleTypes.{uK, uT} (k + 1) K.Carrier` contained
  in `π`, one has `Henniart.Numerical.supercuspidalTorsionNumber K π = k + 1` and
  `Henniart.Numerical.HasSupercuspidalSwan K π 0`.

Containment is `SupercuspidalClassContainsType K π x.2`
(`Langlands/BushnellKutzko/SupercuspidalClassContainment.lean`). The field `K.Carrier` carries
the instances of `K.canonicalTopologicalData`, as in the class space and the two sets of pairs
(`Langlands/BushnellKutzko/GLMaximalSimpleTypeSets.lean`). The universes `uK`, `uV` and `uT`
of the field, of the class carriers and of the pair carriers are independent.

The invariants are those of `Langlands/Correspondence/HenniartRefinedStrata.lean`:

- `supercuspidalTorsionNumber K π` is the cardinality `Nat.card` of the set of `z : ℂˣ` with
  `Henniart.Numerical.supercuspidalUnramifiedTwist K k z π = π`. The twist by `z` is the twist
  by the character `g ↦ z ^ ord(det g)` of `GL_{k+1}(K)`
  (`determinantUnramifiedCharacter`). So the torsion number is the number `t(π)` of unramified
  quasicharacters `χ` of `K^×` with `π ⊗ (χ ∘ det) ≅ π`, where `χ` corresponds to
  `z = χ(ϖ_K)`.
- `HasSupercuspidalSwan K π s` says that the conductor `Henniart.Numerical.conductor K π` is a
  natural number `a` with `a - (k + 1) = s`, in truncated subtraction. This is the Swan
  exponent `sw(π)`.

In the notation of BK93, a pair of `glMaximalSimpleTypesAt (k + 1) F t m` is a maximal simple
type attached to a simple stratum `[𝔄, m, 0, β]` with `e(𝔄 | 𝔬_F) = t`, `E = F[β]` and
`e(𝔅_β | 𝔬_E) = 1`, so `t = e(E | F) e(𝔅_β | 𝔬_E) = e(E | F)`. Part (a) is then
`t(π) = N/e(E | F) = N/t` and `sw(π) = m N/t`. Part (b) is the level-zero case, with `E = F`
and `m = 0`: `t(π) = N` and `sw(π) = 0`. The divisibility `t ∣ k + 1` holds because the
period of a principal order in `End_F(F^N)` divides `N`.

## Provenance

The statement transfers to the Library's class objects the results on representations
listed below. It is not a numbered result of a source in this form.

- Torsion number. BK93 (6.2.5), printed p. 204: for an irreducible supercuspidal `π`
  containing the simple type defined by `[𝔄, n, 0, β]`, `E = F[β]`, and an unramified
  quasicharacter `χ` of `F^×`, `π ≅ π ⊗ (χ ∘ det)` if and only if `χ` has finite order
  dividing `N/e(E | F)`. The Library states this as
  `Langlands.BushnellKutzko.SimpleTypeSelfTwistStatement`. The unramified quasicharacters of
  order dividing `N/e(E | F)` are the `χ` with `χ(ϖ_F)` an `N/e(E | F)`-th root of unity, so
  there are exactly `N/e(E | F)` of them. BK93, printed p. 205, draws the consequence
  `e(𝔄 | 𝔬_F) = e(E | F) = N/g(π)`, with `g(π)` the number of unramified `χ` such that
  `π ⊗ (χ ∘ det) ≅ π`.
- Swan exponent. The route note, Proposition `prop:T2` (printed p. 12), states the formula
  for every irreducible supercuspidal `π`: if `π` contains a maximal simple type attached to
  `[𝔄, m, 0, β]` with `m ≥ 1` and `e = e(𝔄) = e(E | K)`, then `sw(π) = mn/e`; if `π`
  contains a maximal simple type of level zero, then `sw(π) = 0`. The sentence after the
  proposition states `t(π) = n/e(𝔄)` and `sw(π) = mf` with `f = n/e(𝔄)`. The sources of the
  proposition are BK94 (3.10)(i), from Bushnell–Fröhlich (1985), (3.3.8), and Bushnell (1987),
  Theorem 3. BK94 (3.10)(i) is stated for `π ∈ R(N, F)`, the irreducible discrete series
  representations of `GL(N, F)` whose central character takes the value `1` at a fixed prime
  element `ϖ_F` (BK94, printed p. 126). Every irreducible discrete series representation, in
  particular every irreducible supercuspidal `π`, has an unramified twist in `R(N, F)` (BK94,
  printed p. 126). An unramified character of `F^×` is `|·|_F^w` for some `w ∈ ℂ`, and
  twisting by `|det|_F^w` replaces `ε(s, π, ψ_F)` by `ε(s + w, π, ψ_F)`. This changes the
  constant `c(π)` but not the exponent of `q_F^{−s}`, so the formula holds for every
  irreducible supercuspidal `π`.

  The proof of Lemma `lem:level`(i) in the route note (printed p. 16) goes in the following
  direction. A pure stratum `[𝔄, m, m − 1, β]` is fundamental (BK93 (2.3.2)). So a
  representation containing a maximal simple type attached to `[𝔄, m, 0, β]` contains a
  fundamental stratum, and the first assertion of the lemma gives the normalized level
  `ℓ(π) = m/e(𝔄)`. The Swan formula of Proposition `prop:T2` then gives `sw(π) = n ℓ(π)`;
  in level zero both sides are `0`. The Library states the normalized level of a
  representation containing a fundamental stratum as
  `Langlands.BushnellKutzko.FundamentalStratumLevelStatement` and the identity
  `sw(π) = n ℓ(π)` as `Langlands.BushnellKutzko.SupercuspidalSwanLevelStatement`. Both are
  proved in the Library (`fundamentalStratumLevel`, `supercuspidalSwanLevel`). With BK93
  (2.3.2) they give the Swan exponent `sw(π) = n · m/e(𝔄)` of part (a). In part (b) the type
  is trivial on `U^1(𝔄)`, so `π` has a nonzero `U^1(𝔄)`-fixed vector, normalized level `0`
  and Swan exponent `0`.

## Sources

- C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
  (1993): (6.2.5) and its proof, printed pp. 204–205 (PDF pp. 216–217); (2.3.2), printed
  p. 57 (PDF p. 69).
  Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
  SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
- C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing conjugacy classes* (1994),
  (3.10)(i), printed p. 127 (volume PDF p. 140): for `π ∈ R(N, F)` whose simple type has
  label in `P̃_n(t, N/t; q_F)`, `ε(s, π, ψ_F) = c(π) q_F^{−snN/t}`; the set `R(N, F)` of
  irreducible smooth discrete series representations `π` of `GL(N, F)` with
  `ω_π(ϖ_F) = 1`, `ω_π` the central quasicharacter, printed p. 126 (volume PDF p. 139).
  Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
  SHA-256 `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
- C. J. Bushnell and A. Fröhlich, *Non-abelian congruence Gauss sums and p-adic simple
  algebras* (1985), (3.3.8), printed p. 258 (PDF p. 52).
  Literature ID `bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`,
  SHA-256 `7ab34c7ebd9c3e5567d260de22cbc9e51598ab96a03c407376fb225496460819`.
- C. J. Bushnell, *Hereditary orders, Gauss sums and supercuspidal representations of GL_N*
  (1987), Theorem 3, printed p. 198 (PDF p. 15).
  Literature ID `bushnell-1987-hereditary-orders-gauss-sums`,
  SHA-256 `285eebfc66e11b0c4234c24e677ebac7472d49e113a3e3cd1e5e91c5ac364fa0`.
- Operator route note, *The numerical local Langlands correspondence for GL_n: counts on the
  two sides and the recommended route of proof* (16 November 2026), `numerical-LLC-route.tex`:
  Proposition `prop:T2` and the sentence after it (lines 510–516, printed p. 12); §4.4
  `sec:conductors` and Lemma `lem:level`(i) (lines 600–629, printed pp. 15–16) with its proof
  (lines 630–634, printed p. 16).
  Literature ID `operator-numerical-llc-route-2026-11-16`,
  SHA-256 `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
