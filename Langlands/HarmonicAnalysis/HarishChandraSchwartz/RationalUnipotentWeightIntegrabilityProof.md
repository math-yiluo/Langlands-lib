# Waldspurger II.4.2 on the actual opposite radical

`rationalUnipotentWeightIntegrability` proves exactly
`RationalUnipotentWeightIntegrabilityStatement.{u}` at arbitrary universe `u`.
Let F be a nonarchimedean local field and G a connected reductive group over F.
Fix a maximal split torus, a generic cocharacter ν and a cocharacter ζ that is
standard for J, with simultaneous standard-basis and finite Cartan-covering
data at a compact open K0. Then for every compact open minimal Iwasawa factor
K, every closed matrix representation ρ of nonzero size and every Haar measure
on U = `oppositeUnipotent i ζ`, there is a natural number d with

```
∫⁻ u ∈ U, w(u) (1 + σ(u))^(-d) < ∞,
```

where w = `iwasawaWeight hPK (rationalMinimalModulus i ν)` and
σ = `rationalHeight ρ`.

The proof is one application of
`rationalUnipotentWeightIntegrability_of_levelStatements` (module
`RationalUnipotentWeightLevelReduction`) to two theorems:

- `rationalOppositeModulusLevelData` gives a measurable integer level
  function L on U with w(u) = q^(-L(u)/2), q the residue cardinality of F,
  and constants C₀, C₁, C₂ with C₁, C₂ > 0 and
  C₁ (1 + σ(u)) ≤ C₀ + L(u) log q ≤ C₂ (1 + σ(u)).
- `rationalOppositeLevelSetMeasureBound` bounds the Haar measure of the level
  set {L = n}, for n ≥ 1, by C q^(n/2) n^d' for constants C and d'.

The reduction then runs the summation of the generic theorem
`unipotentWeightIntegrable_of_levelSets`. The set {L ≤ 0} lies in a height
sublevel by the lower comparison. It has finite measure because height
sublevels of the closed subgroup U are compact, and the integrand is bounded
on it. On the level set {L = n} with n ≥ 1, the factor q^(-n/2) of w cancels
the factor q^(n/2) of the volume bound. The upper comparison bounds
(1 + σ)^(-d) by a constant times n^(-d), so the terms are bounded by a
constant times n^(d'-d), which is summable once d ≥ d' + 2. The reduction finally
replaces the real exponent returned by the generic theorem by a natural number
at least as large. This keeps the integral finite because w ≥ 0 and σ ≥ 0.

The route is Waldspurger's proof of Lemma II.4.2: a compact part together with
the level sets of Lemma II.3.4, the volume bound of Lemma II.4.1, and the
height comparison.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), Lemma II.4.2 and its proof, printed p. 261.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
PDF page = printed page minus 234.
