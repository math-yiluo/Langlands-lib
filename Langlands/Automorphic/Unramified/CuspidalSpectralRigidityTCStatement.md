# Totally complex forms of Jacquet–Shalika rigidity for supplied cuspidal spectral systems

**Scope.** The module
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement` defines four
propositions in the namespace `Langlands.Automorphic.Unramified` and proves
nothing. The first three are published propositions of
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement` with one more
instance argument, `[NumberField.IsTotallyComplex F]`, inserted directly after
`[NumberField F]`. The universe parameters are the same, and the rest of each body
is copied verbatim. The fourth is their conjunction, exactly as the published
conjunction is formed from the originals.

| New proposition | Universes | Published original |
|---|---|---|
| `CuspidalPowerTraceIndependenceTCStatement` | `uF uV` | `CuspidalPowerTraceIndependenceStatement` |
| `CuspidalPowerTraceConstituentRecoveryTCStatement` | `uF uV` | `CuspidalPowerTraceConstituentRecoveryStatement` |
| `CuspidalEulerConstituentRecoveryTCStatement` | `uF uV` | `CuspidalEulerConstituentRecoveryStatement` |
| `CuspidalSpectralRigidityTCStatement` | `uF uV` | `CuspidalSpectralRigidityStatement` |

The principal declaration of the module is
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement`, the totally
complex form of Harris's input 9 in
`Langlands.Global.Harris.Proposition48ReductionStatement`.

## 1. The statements

All vocabulary is that of the originals, and nothing is redefined:
`PositiveRankCuspidalClass`, `SpectralSystem`, `HasSpectralSystem`, `powerTrace`,
`finiteSum`, `SamePowerTraces` and `SameEulerPolynomials` are explained in
`CuspidalSpectralRigidityStatement.md`. In words, for every totally complex number
field `F : Type uF` with `[CompactSpace (AdeleQuotient F)]`:

- `CuspidalPowerTraceIndependenceTCStatement`. Let `c` be an injective family of
  `p` full cuspidal classes of positive ranks over `F`, with supplied spectral
  systems `s i` attached to `c i` (local-factor universe `uV`), and let `S` be a
  finite set of finite places containing their exceptional sets. If complex
  coefficients `a i` satisfy `∑ a i · tr((s i)_v^k) = 0` for every finite place
  `v ∉ S` and every `k > 0`, then every `a i` is `0`.
- `CuspidalPowerTraceConstituentRecoveryTCStatement`. If two finite families `c`,
  `d` of such classes, with attached spectral systems `s`, `t`, have direct sums
  with the same power traces outside a finite set, then there is a bijection
  `e : Fin p ≃ Fin q` with `c i = d (e i)`; so the lists agree with
  multiplicities.
- `CuspidalEulerConstituentRecoveryTCStatement`. The same conclusion when the two
  direct sums have the same Euler polynomials outside a finite set.
- `CuspidalSpectralRigidityTCStatement`. The conjunction of the three.

## 2. Effect of the restriction

The originals have no archimedean clause: they speak only of finite places. The
restriction therefore changes only the class of number fields, and nothing in the
bodies becomes vacuous. Its purpose is the proof. The proof route proposed for
`CuspidalSpectralRigidityStatement` follows JS81 §4.1 and Theorem 4.2: the behaviour at `s = 1`
of the partial pair L-functions over the same field, namely absolute convergence
(Jacquet–Shalika I, 5.2–5.3), the pole at `s = 1` (from Getz–Hahn Theorem 11.7.1,
published as `Langlands.Global.CuspidalPairPoleStatement`) and Shahidi's
nonvanishing on `Re s = 1`. Of these, only the pole statement has archimedean
clauses. Over a totally complex field it can be replaced by
`Langlands.Global.CuspidalPairPoleTCStatement` (module
`Langlands.Global.Factors.CuspidalPairPoleTCStatement`), whose archimedean part
involves only `GL_n(ℂ)`. So on that route a proof of these forms needs no
`GL_n(ℝ)` archimedean theory.

## 3. Relation to the originals

Each original implies its totally complex form at the same universe levels: apply
it to the same field and forget the new instance. A development check outside
the module compiled the three implications, each as `fun h F _ _ _ _ => h F`, and
the implication of the conjunctions componentwise. The converses are not claimed.
The statements make no claim about number fields with a real place.

## 4. Why the totally complex forms are stated

Harris's Proposition 4.8 (published as `Langlands.Global.Harris.Proposition48Statement`)
concerns CM fields: in a `Proposition48Problem` the fields `E` and `E'` are CM and
`L` is a finite extension of `E`. Its proof applies rigidity only over these fields
and their intermediate fields, through the isobaric invariance step (input 10)
and the prime and singleton branches (inputs 5 and 6). A CM field is totally
complex (Mathlib `NumberField.IsCMField.isTotallyComplex`), and every finite
extension of a totally complex field is totally complex
(`NumberField.isTotallyComplex_of_algebra`). The totally complex reduction
`Langlands.Global.Harris.Proposition48ReductionTCStatement` (module
`Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement`) takes
`CuspidalSpectralRigidityTCStatement.{0, uV}` as its input 9.

The unrestricted statement `CuspidalSpectralRigidityStatement` remains in the
Library as infrastructure. No statement is made here for the alternative route
from partial L-functions (Jacquet–Shalika 1981, Part I, without archimedean
parameters).

## 5. Sources and provenance

Provenance: *derived*. The propositions are the special cases, for totally complex
base fields, of the published statements, which follow the source below; the
source states its results for every number field (more generally, every global
field). The source and locators are those of the originals; the full
correspondence and the scope of the numerical recovery step are in
`CuspidalSpectralRigidityStatement.md`.

- `jacquet-shalika-1981-euler-ii` (JS81): H. Jacquet and J. A. Shalika, *On Euler
  Products and the Classification of Automorphic Forms II*, Amer. J. Math. 103
  (1981), 777–815. §4.1, printed p.805 (PDF 30): the analytic background;
  Theorem 4.2 and its proof, printed pp.806–807 (PDF 31–32): mixed-rank
  independence; Theorem 4.4 and its proof, printed p.809 (PDF 34): recovery of
  the constituents with multiplicities.
