# Finiteness of the supercuspidal unramified-orbit strata (statement)

Module `Langlands.Correspondence.HenniartOrbitStratumFinitenessStatement`, namespace
`Langlands.Henniart`. Authors: Worker 5733 (draft), Worker 408. This module only defines
the proposition. Nothing is proved here.

Universes: `uK` (p-adic fields) and `uV` (supercuspidal carriers). They are independent.

## Statement: `SupercuspidalOrbitStratumFinitenessStatement.{uK, uV}`

```
∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k a : ℕ),
  (Numerical.supercuspidalOrbitStratum.{uK, uV} K k a).Finite
```

`Numerical.supercuspidalOrbitStratum K k a` is the published set from module
`Langlands.Correspondence.HenniartNumericalStatement`. Its elements are orbits in
`PadicSupercuspidal.UnramifiedOrbitClasses K`. These are the orbits of supercuspidal
classes under twisting by the unramified characters `g ↦ z ^ ord(det g)`, for all
`z : ℂˣ`. An orbit is in the set when it contains a supercuspidal class `π` of
`GL_(k+1)(K)` (carrier in `Type uV`) with `Numerical.conductor K π = a`. That conductor is
the first level with a nonzero vector fixed by the newvector (last-row congruence)
subgroup, `GeneralLinear.SupercuspidalClass.firstFixedLevel`.

In words: for every p-adic field `K`, rank `k + 1` and conductor exponent `a`, only
finitely many unramified-twist orbits of supercuspidal classes of `GL_(k+1)(K)`
contain a class of conductor `a`.

The quantifiers have no added hypotheses. The prime `p`, the field `K`, the rank index
`k` and the conductor exponent `a` are arbitrary.

## Relation to published statements

The statement is exactly the second conjunct of the published
`Langlands.Henniart.NumericalOrbitCountStatement.{uK, uW, uV}`. For each `(K, k, a)` that
proposition asserts three things: the Weil stratum is finite, this supercuspidal stratum
is finite, and the two strata have the same `Set.ncard`. This module states the
supercuspidal finiteness by itself, so that it can be proved without the other two
conjuncts. It has no Weil universe `uW`. For any `uW`,
`NumericalOrbitCountStatement.{uK, uW, uV}` implies this statement by taking its second
conjunct. That implication is not formalized in this module.

## Provenance

The statement is internal (derived). It is not a numbered result of a source. It was
split off from `NumericalOrbitCountStatement` for Task 5584. That task proves Henniart
(1988), Théorème 1.2 (registered source `henniart-1988-numerical`, printed p. 498),
through the counting reduction `numericalOrbitReduction`. The public route study
`notes/henniart/numerical-count-route-study.md` calls it step U1 (GL-side orbit-stratum
finiteness). The Markdown of `NumericalOrbitCountStatement` says that
"Bernstein–Zelevinsky finiteness gives finiteness on the supercuspidal side". The
intended proof uses the Library's p-adic form of Bernstein–Zelevinsky (1976),
Corollary 4.15:
`Langlands.Henniart.CompactOpenFiniteness.centralLevelStratum_finite`, from module
`Langlands.Correspondence.PadicSupercuspidalFinitenessProof`. That theorem says that
only finitely many supercuspidal classes of `GL_(n+1)` have a given central character
and first newvector level at most `b`.

Henniart's own §2.6 (printed p. 505) uses a different normalization. It defines
`𝒜²_K(n, j, ϖ_K)`, the essentially square-integrable `π` with `ω_π(ϖ_K) = 1` and Swan
exponent `s(π) ≤ j`. It also defines the corresponding set `𝒜_D(j, ϖ_K)` for the
division algebra `D` of reduced degree `n`, which it states is finite. The statement
here does not fix `ω_π(ϖ_K)` or bound the Swan exponent. It counts orbits under all
unramified twists, and fixes the conductor exponent exactly.

## Imports

- `Langlands.Correspondence.HenniartNumericalStatement` (published, unchanged), for
  `Numerical.supercuspidalOrbitStratum`.
