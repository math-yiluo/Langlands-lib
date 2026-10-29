# Proof of irreducible unequal-rank mirabolic pairing rigidity

Author: Worker 895.

Module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingProof`.

This module proves `Langlands.RankinSelberg.unequalRankMirabolicPairingRigidity`.
Its type is exactly
`UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW} F T n r` from
`Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`.
The theorem holds for every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData` and all natural numbers `n, r`. It keeps the three universes
independent. The statement, its Markdown and every imported definition are unchanged.
The helper results of the proof are internal. They live in the namespace
`Langlands.RankinSelberg.UnequalRankRigidity` and in four helper modules:

- `UnequalRankMirabolicTower`: the tower embeddings `P_j → P_N` and the tower datum
  `IsTower`;
- `UnequalRankMirabolicTowerFinite`: finiteness of the radical-coinvariant spectrum
  of a tower datum (`IsTower.exists_polynomial`);
- `UnequalRankMirabolicTowerClaim`: the inner induction `towerClaim`;
- `UnequalRankMirabolicMixedTransfer`: the adjacent-rank transfer `mixedTransfer`.

Each helper module has its own Markdown. Only the axioms `propext`,
`Classical.choice` and `Quot.sound` are used.

## Notation

`P_m = mirabolic m F` is the mirabolic subgroup of `GL_(m+1)(F)`. `q = q_F` is
`T.residueCardinality`, `|·|` is `normalizedAbsoluteValue T`, and
`sp(s) = spectralPoint q s = q^(-s)`. Write `dW g s = determinantWeight |·| g s`
for `|det g|^s`, `θ_n = standardCharacter ψ n` and
`θ⁻_n = inverseStandardCharacter ψ n` on `U_(n+1) = upperUnipotent (n+1) F`.
`Φ⁻` is the published unnormalized functor `phiMinusUnnormalized T ψ m` from
`P_(m+1)`-representations to `P_m`-representations. Its radical character is
`Θ = T.mirabolicTheta ψ m`, with `Θ(radicalElement d) = ψ(d_last)`. For a form
`B` with rank pair `n < r`, the two laws of `unequalRankMirabolicForms` are the
Levi law (weight `dW g ((r - n)/2 - s)`) and the unipotent law (character
`standardCharacter ψ r`).

## Overall structure

The proof first proves a version with the standard character `θ_n` in place of
`θ⁻_n` (`rigidity_of_lt`), by induction on `r ≥ n + 1`. The final theorem converts
the functional at the end.

### Final conversion (`hasFunctional_inverse_of_standard`)

A nonzero `θ_n`-functional on `η` gives a nonzero `θ⁻_n`-functional. The published
linear equivalence `characterChangeFunctionalEquiv ψ η (-1)` maps `θ_n`-functionals
onto `standardCharacter (ψ.scale (-1)) n`-functionals. That character is `θ⁻_n`
(`standardCharacter_scale_neg_one`). A linear equivalence maps nonzero vectors to
nonzero vectors.

`unequalRankMirabolicPairingRigidity` applies `rigidity_of_lt` with the same `E`
and converts the functional. The compact-model isomorphism is passed through
unchanged.

## Descent (`exists_descent_ne_zero`)

Let `n < m`, `ξ` a smooth representation of `P_(m+1)` and `B` a nonzero form in
`unequalRankMirabolicForms (n < m + 1) ψ |·| ξ η s`. Then there is a nonzero form
`B'` in `unequalRankMirabolicForms (n < m) ψ |·| (Φ⁻ ξ) η (s - 1/2)`.

1. *Radical law.* For `d ∈ F^(m+1)`, the radical element `radicalElement d` of
   `P_(m+1)` is a covariance unipotent element
   (`UnequalRankCompactPairing.isCovarianceUnipotent_radical`). The standard
   character takes the value `ψ(d_last)` on it
   (`UnequalRankCompactPairing.standardCharacter_radicalElement`), which is
   `Θ(radicalElement d)` (`theta_radicalElement`). So the unipotent law of `B` gives
   `B(ξ(u) v, w) = Θ(u) B(v, w)` for every radical element `u`.
2. *Factorization.* By this law, each `B(·, w)` factors through the
   `(radical, Θ)`-coinvariants of `ξ`. This quotient is the carrier of `Φ⁻ ξ`. The
   published `Jacquet.Localization.lift` gives a bilinear `L` with
   `L(π v, w) = B(v, w)`, where `π = phiMinusQuotient T ψ m` is the quotient map.
3. *Laws of `L`.* The quotient map is surjective (`phiMinusQuotient_surjective`), so
   it suffices to check the laws on `π v`. `Φ⁻ ξ(g)` acts on `π v` as
   `ξ(successor g)`. The published algebra of `UnequalRankCompactPairingReduction`
   gives:
   - Levi law: `successor (unequalRankEmbedding (n < m) g)` equals
     `unequalRankEmbedding (n < m + 1) g` (`unequalRankEmbedding_succ`), and the
     weights agree, since `(m - n)/2 - (s - 1/2) = (m + 1 - n)/2 - s`
     (`weight_succ`).
   - Unipotent law: for a covariance unipotent `u` of rank `m`,
     `successor (unequalRankUnipotentLift u)` is the lift of
     `successorUnipotent u` (`unequalRankUnipotentLift_successorUnipotent`). That
     element is a covariance unipotent of rank `m + 1`
     (`isCovarianceUnipotent_successor`), and the character values agree
     (`standardCharacter_successor`).
4. *Nonvanishing.* If `L = 0` then `B(v, w) = L(π v, w) = 0` for all `v, w`.

## Adjacent ranks (`rigidity_adjacent`)

Here `r = n + 1`, `ξ` is a smooth irreducible representation of `P_(n+1)` and `η`
an admissible irreducible representation of `GL_(n+1)`. In this case the embedding
is the Levi embedding `g ↦ diag(g, 1)` (`unequalRankEmbedding_adjacent`). The
weight is `(1/2 - s) = -(s - 1/2)`. So the Levi law reads

`B(ξ(levi g) v, η(g) w) = dW g (-(s - 1/2)) · B(v, w)`   (`hlevi`).

The published `radicalTrivial_or_radicalGenerated` splits the proof into two cases.

*Case 1: `ξ` is radical-trivial.* Let `ϖ` be the uniformizer unit, so
`|ϖ| = q^(-1)`. Let `z = leviScalar ϖ ∈ P_(n+1)` and `ζ = ϖ I_(n+1) ∈ GL_(n+1)`, so
`z = levi ζ`.

- `ξ(z)` commutes with `ξ` (`apply_mul_leviScalar`). `ξ` has countable dimension
  (`rank_le_aleph0`), so Schur's lemma (`exists_scalar_of_commute`) gives
  `ξ(z) = c` for a scalar `c`.
- `η(ζ)` is a `GL_(n+1)`-endomorphism of `η`, because `ζ` is central
  (`Matrix.GeneralLinearGroup.scalar_commute`). The published Schur lemma for
  admissible irreducible representations, `admissibleSchur_scalarEndomorphism`,
  gives `η(ζ) = c'` for a scalar `c'`.
- `dW ζ (-t) = (sp(t)^(n+1))⁻¹` for every `t`, since `|det ζ| = q^(-(n+1))`
  (`determinantWeight_scalar`, based on the published
  `determinantWeight_eq_spectralPoint_zpow`).

Take `E = {w / q^(1/2) : w^(n+1) = (c c')⁻¹}`. It is finite: it is the image of the
roots of the nonzero polynomial `X^(n+1) - (c c')⁻¹` (`Polynomial.nthRoots`). Suppose
`sp(s) ∉ E` and `B ≠ 0`. Pick `x, y` with `B(x, y) ≠ 0`. The Levi law at `g = ζ`
gives `c c' B(x, y) = (sp(s - 1/2)^(n+1))⁻¹ B(x, y)`. So
`sp(s - 1/2)^(n+1) = (c c')⁻¹`. Since `sp(s - 1/2) = q^(1/2) sp(s)`
(`spectralPoint_sub`), this gives `sp(s) ∈ E`, a contradiction
(`spectralPoint_sub_notMem`). In this case no nonzero form exists outside `E`.

*Case 2: `ξ` is radical-generated.* Let `X' = Φ⁻ ξ`, a smooth representation of
`P_n`. Let `ρ = η|_(P_n)`. It is smooth, since `η` is.

- `mixedTransfer` (helper module), applied at the parameter `s - 1/2` with the Levi
  law `hlevi`, turns a nonzero `B` into a nonzero form `β'` on `X' × ρ`. This form
  has `P_n`-covariance `h ↦ dW h (-(s - 1/2 - 1))`.
- If `X'` has `⊥ = ⊤` as subrepresentations, take `E = ∅`. Every form on `X' × ρ`
  vanishes (`forms_eq_zero_of_bot_eq_top_left`), so no nonzero `B` exists.
- Otherwise `X'` is irreducible, by the published `phiMinusIrreducible` dichotomy
  and `isIrreducible_of_dichotomy`. Apply the tower claim `towerClaim` at level
  `j = N = n`. Its tower datum is `ρ` with the identity map
  `W → W` (`isTower_top`). This gives a finite set `E'`. Take
  `E = {w / q^(3/2) : w ∈ E'}`. If `sp(s) ∉ E`, then
  `sp(s - 3/2) = sp(s - 1/2 - 1) ∉ E'`. The claim applied to `β'` gives
  `X' ≅ mirabolicCompactInduced ψ n` and a nonzero `θ_n`-functional on `η`. The
  published `nonempty_equiv_of_phiMinus` lifts the first isomorphism to
  `ξ ≅ mirabolicCompactInduced ψ (n + 1)`. It uses functional multiplicity one
  (`mirabolicFunctionalMultiplicity`) in ranks `n` and `n + 1`.

## Induction on `r` (`rigidity_of_lt`)

The induction is `Nat.le_induction` on `n + 1 ≤ r`. The base case is
`rigidity_adjacent`. For the step from `m` to `m + 1` (with `n + 1 ≤ m`), let `ξ` be
a smooth irreducible representation of `P_(m+1)` and `X' = Φ⁻ ξ`.

- If `X'` has `⊥ = ⊤`, take `E = ∅`. The descended form `B'` from
  `exists_descent_ne_zero` would be nonzero, but every vector of `X'` is zero
  (`eq_zero_of_bot_eq_top`).
- Otherwise `X'` is irreducible, as in the adjacent case. The induction hypothesis
  for `(X', η)` gives `E'`. Take `E = {w / q^(1/2) : w ∈ E'}`. If `sp(s) ∉ E`, then
  `sp(s - 1/2) ∉ E'`. The descended nonzero form `B'` at `s - 1/2` then gives
  `X' ≅ mirabolicCompactInduced ψ m` and the `θ_n`-functional on `η`.
  `nonempty_equiv_of_phiMinus` lifts the isomorphism to `ξ`, as above.

In every case the set `E` is chosen after `ψ, ξ, η` and before `s` and `B`, as in
the statement.

## Sources and route

Jacquet, Piatetski-Shapiro and Shalika (1983), *Rankin-Selberg Convolutions*,
§2.11, Lemma on printed p.399; registered as `jpss-1983-rankin-selberg`. The source
proves the lemma with the classification of irreducible mirabolic representations
(Theorem 1.2), the finite length of `η|_(P_t)` and a distribution argument
(pp.400–403). The Lean proof follows a different route. It uses induction on the
large rank through the Bernstein–Zelevinsky functor `Φ⁻`, and recognizes the compact
model through Whittaker functionals and functional multiplicity one. It needs no
finite length of `η|_(P_t)`: the tower claim uses only the finiteness of the action
of the Jacquet-module center (published `Parabolic.jacquetCenterSpan`), packaged in
`UnequalRankMirabolicTowerFinite`. The proof keeps the exceptional set finite in
`q^(-s)`, as in the statement.
