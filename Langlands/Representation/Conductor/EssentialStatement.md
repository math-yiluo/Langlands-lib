# Existence of the essential vector and the conductor exponent

Author: Worker 11. This module, in namespace `Langlands.Conductor`, states the
main results about the essential vector and the conductor of an irreducible
admissible generic representation of `GL_r(F)` over a nonarchimedean local
field `F`. It states Jacquet's corrected existence theorem for the essential
vector (2012) with the uniqueness clause after it, and the theorem of
Jacquet, Piatetski-Shapiro and Shalika (1981) that identifies the exponent of
the epsilon factor with the least congruence level that has a nonzero fixed
vector. The module defines four propositions and proves none of them.

The essential vector is the published `IsEssentialVector` of
`Langlands.Representation.Conductor.Essential`. The congruence levels and the
least nonzero level are the published `levelFixedVectors` and
`IsNewvectorConductor` of `Langlands.Representation.Conductor.Definitions`.
The epsilon factor is the published relation `IsPairEpsilonFactor` of
`Langlands.Representation.RankinSelberg.EpsilonFactor`, applied to `π` and the
trivial character of `GL_1(F)`.

## Sources

**Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du
groupe linéaire*, Math. Ann. 256 (1981), 199-214** (PDF page = printed
page - 198).

- **(1.1), printed page 199.** `π` is an irreducible admissible representation
  of `G_r = GL(r, F)`. Godement and Jacquet define `L(s, π) = P_π(q^{-s})^{-1}`
  with `P_π(0) = 1`, and `ε(s, π, ψ) = ε_π(q^{-s}, ψ)` with
  `ε_π(X, ψ) = c X^m`, where `q` is the module of `F`. The exponent of `ψ` is
  always `0`: the largest ideal on which `ψ` is trivial is the ring of integers
  `𝔒`. Then `m` depends only on `π`. For `r = 1`, `m ≥ 0`, and the source
  separates two cases. If `m = 0`, the character `π` is unramified, of the form
  `|x|^s`, hence trivial on `𝔒^×`. If `m > 0`, then `π` is ramified, trivial on
  `1 + 𝔓^m` and nontrivial on `1 + 𝔓^a` for `0 < a < m`.
- **(1.2), printed page 200.** `|x| = q^{-v(x)}`. `θ_{r,ψ}(n) = ψ(Σ_i n_{i,i+1})`
  on the upper unitriangular group `N_r`. `π` is *generic* if it is realized on
  a space of functions that transform on the left by `θ_{r,ψ}`, the Whittaker
  model `𝒲(π; ψ)`.
- **(5.1) Theorem, printed page 211.** Let `π` be irreducible and generic and
  `ψ` of exponent `0`, and let `m` be the integer with `ε_π(X, ψ) = c X^m`.
  (i) `m ≥ 0`. (ii) For an integer `a > 0`, `K_r(a)` is the subgroup of
  `K_r = GL_r(𝔒)` of matrices `[[h, v], [u, x]]` with `h ∈ K_{r-1}`,
  `x ∈ 𝔒^×`, `x ≡ 1 mod 𝔓^a` and `u ≡ 0 mod 𝔓^a`, and `K_r(0) = K_r`. Then the
  essential vector is invariant under `K_r(m)`, and the space of vectors fixed
  by `K_r(m)` has dimension one. (iii) If `a ≥ 0` and `π` has a nonzero vector
  fixed by `K_r(a)`, then `a ≥ m`.

The essential vector of (5.1) is the vector of (4.1) and (4.4), whose
existence proof in the 1981 paper is defective.

**Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515-525.**

- **Printed page 515.** `|x| = q^{-v(x)}`, `ψ` has conductor `𝔒_F`, and the
  Haar measure on `G_r(F)` gives `G_r(𝔒_F)` volume one.
- **Printed page 516.** The Haar measure on `N_r(F)` gives `N_r(𝔒_F)` measure
  one, with the invariant quotient measure on `N_r(F) \ G_r(F)`. The spherical
  Whittaker function `W(g; x_1, ..., x_r; ψ)` is characterized by right
  `G_r(𝔒_F)`-invariance, `θ_{r,ψ}`-equivariance on the left, the Hecke
  eigen-equation with Satake eigenvalue at `x`, and `W(e) = 1`.
- **Printed page 517, Theorem 1.** For irreducible admissible generic `π` of
  `G_r(F)`, with `L(s, π) = P(q^{-s})^{-1}` (Godement-Jacquet), there is `W` in
  `𝒲(π; ψ)` such that for every `(r - 1)`-tuple of nonzero complex numbers
  `x`,

  `∫_{N_{r-1} \ G_{r-1}} W(diag(g, 1)) W(g; x; ψ̄) |det g|^{s - 1/2} dg
    = ∏_{1 ≤ i ≤ r-1} P(q^{-s} x_i)^{-1}`.

  The paragraph after the theorem: if the extra condition
  `W(diag(g h, 1)) = W(diag(g, 1))` for all `h ∈ G_{r-1}(𝔒_F)` is imposed, then
  `W` is unique, and it is called the essential vector of `π`.
- **Printed page 523, Remark 1.** The 1981 proof is correct when `L(s, π) = 1`.

**Bushnell, Henniart and Kutzko, *Correspondance de Langlands locale pour
GL_n et conducteurs de paires*, Ann. Sci. ENS (4) 31 (1998), 537-560.**

- **Section 1.3, printed page 538.** For a quasicharacter `χ` of `F^×` and `π`
  of `GL_n(F)`, `L(χ × π) = L(χπ)` and `ε(χ × π, ψ) = ε(χπ, ψ)`, stated
  without proof. This is the factor comparison discussed under
  "Interpretation and gaps".

## The four propositions

All four take a field `F` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]` in universe `uF`, and representations on
complex vector spaces in universe `uV`. The valuation `v` is
`ValuativeRel.valuation F` and `𝔒` is its integer ring.

### `EssentialVectorStatement`

Jacquet 2012, Theorem 1 with the uniqueness clause. For every `n`, every
Borel measurable structure on `GL_{n+1}(F)`, its upper unitriangular group and
`GL_1(F)`, measurable structures on the quotients `N_{n+1} \ GL_{n+1}(F)` and
`N_1 \ GL_1(F)`, and every `q`, `ψ`, `abv`, `ϖ` and quotient measure `μ` with
`h : IsJacquetNormalization q ψ abv ϖ μ`: let `π` be a representation of
`GL_{n+2}(F)` with `IsGeneric ψ (n + 1) π` (irreducible, admissible, and with a
nonzero `θ_ψ`-Whittaker functional). Then for every nonzero
`ℓ ∈ glFunctionals ψ (n + 1) π`, exactly one vector `w` of the coefficient
model `coefficientModel π ℓ` satisfies `IsEssentialVector h π ℓ w`.

`IsJacquetNormalization` records Jacquet's normalizations: `q` is the residue
cardinality, `ϖ` a uniformizer, `abv(ϖ) = q^{-1}` and `abv = 1` on valuation
units, `ψ` of conductor `𝔒`, `μ` compatible with the Haar measures giving
`GL_{n+1}(𝔒)` and `N_{n+1}(𝔒)` mass one, and both quotients Borel. Jacquet's
rank `r` is `n + 2 ≥ 2`. The statement makes no claim for a normalization
that no `μ` satisfies.

### `ConductorExponentStatement`

JPSS 1981, Theorem (5.1), parts (i)-(iii), in every rank `n + 1 ≥ 1`. The
hypotheses are:

- `T2Space F`, `TotallyDisconnectedSpace F`, and Borel measurable structures on
  `F`, `GL_1(F)`, its unipotent subgroup and `N_1 \ GL_1(F)`;
- `q` is the residue cardinality of `𝔒`;
- `abv` is normalized: `abv(ϖ) = q^{-1}` for some uniformizer `ϖ`, and
  `abv x = 1` whenever `v(x) = 1`;
- `HasIntegerConductor ψ` (JPSS's exponent `0`);
- `ν` is an additive Haar measure on `F` with `IsSelfDual ψ ν`;
- `π` is a representation of `GL_{n+1}(F)` with `IsGeneric ψ n π`.

The conclusion is that there are `c : ℂˣ` and `m : ℕ` with

- `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`: the epsilon
  factor of `π` against the trivial character of `GL_1(F)` is `c q^{-ms}`;
- `IsNewvectorConductor π m`: the level-`m` fixed space `levelFixedVectors π m`
  is nonzero, and `levelFixedVectors π b = 0` for every `b < m`;
- `Module.finrank ℂ (levelFixedVectors π m) = 1`.

Taking `m : ℕ` is part (i). The last conjunct is the dimension claim of part
(ii). Part (iii) is the minimality clause of `IsNewvectorConductor`. Its first
clause, a nonzero level-`m` fixed vector, also follows from dimension one.

`levelFixedVectors π a` is the subspace fixed by the published
`levelSubgroup F n a`: the integral invertible matrices whose last row is
congruent to `(0, ..., 0, 1)` modulo `𝔓^a`, with level `0` the whole
`GL_{n+1}(𝔒)`. For `a > 0` this is JPSS's `K_r(a)`. The condition `h ∈ K_{r-1}`
is then automatic, because a matrix of `GL_r(𝔒)` whose last row reduces to
`(0, ..., 0, 1)` modulo `𝔓` has an invertible upper-left block. The congruence
modules document the construction.

Since `IsPairEpsilonFactor` has at most one solution for `q > 1` (published
`.unique` lemmas), the `m` is the exponent of the epsilon factor, and the
statement is JPSS's identification of the conductor.

### `EssentialVectorLevelStatement`

JPSS 1981, Theorem (5.1)(ii), first clause, in rank `n + 2`. With the
hypotheses of `EssentialVectorStatement` together with `T2Space F`,
`TotallyDisconnectedSpace F`, a Borel structure on `F`, Borel structures on
`GL_1(F)` and its unipotent subgroup, and an additive Haar measure `ν` with
`IsSelfDual ψ ν`: for generic `π` of `GL_{n+2}(F)`, nonzero
`ℓ ∈ glFunctionals ψ (n + 1) π`, an essential vector `w` of the model of `ℓ`,
and `(c, m)` with
`IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`, the vector `w`
lies in `levelFixedVectors (modelRepresentation π ℓ) m`. The model
representation acts by right translation, `(g · W)(x) = W(x g)`, so this says
that `W(x k) = W(x)` for every `k ∈ K_{n+2}(m)`.

The statement is about every essential vector and every `(c, m)` satisfying the
relation. By `EssentialVectorStatement` and the uniqueness of the epsilon
factor, these are the essential vector and the exponent of the theorem.

### `EssentialConductorStatement`

The conjunction of the three statements above, with universe parameters
`uF uV`.

## Interpretation and gaps

- **The L-factor in the essential identity.** Jacquet's `P` is the
  Godement-Jacquet polynomial of `L(s, π)`. The published `IsEssentialVector`
  uses the JPSS factor `L(s, π × 1)` of `π` against the trivial character of
  `GL_1`, with the published rank-one quotient measure. The two factors agree
  by a theorem that is not in the Library. `Essential.md` records this choice.
  JPSS 1983 does not state the comparison. Bushnell, Henniart and Kutzko,
  Ann. Sci. ENS 31 (1998), section 1.3, printed page 538, recall the JPSS 1983
  (and Shahidi) pair factors and then state, without proof or a specific
  reference, that `L(χ × π) = L(χπ)` and `ε(χ × π, ψ) = ε(χπ, ψ)` for a
  quasicharacter `χ`. Taking `χ = 1` gives the comparison used here. Since it
  has no proof in a source read here and none in Lean, it remains a gap.
- **The epsilon factor.** JPSS 1981 uses the Godement-Jacquet
  `ε(s, π, ψ)`. Here the factor is the JPSS 1983 pair factor
  `ε(s, π × 1, ψ)` of the published `IsPairEpsilonFactor`, with `π` as the
  candidate and the trivial character as the test. That the two epsilon
  factors agree is likewise a theorem not in the Library. In rank one the
  relation is the equal-rank relation. Its zeta integrals are Tate's integrals
  of the character `π`, so `ε` is Tate's epsilon factor and `m` is the
  conductor exponent of `π`, as in JPSS (1.1); this reading is not proved in
  Lean.
- **The additive measure.** `ν` enters the epsilon relation, which defines the
  JPSS factor only for `ν` self-dual for `ψ`, the measure JPSS 1983 use
  (`EpsilonFactor.md`). In rank one `ν` scales the Fourier transform. At rank
  two (test rank one) the relation does not depend on `ν`. From rank three on,
  rescaling `ν` rescales the blocks of the unequal-rank equation differently,
  so the common value `(c, m)` depends on the normalization of `ν`. The
  hypotheses `T2Space F` and `TotallyDisconnectedSpace F` are needed to state
  `IsSelfDual`. They hold for every nonarchimedean local field, so they do not
  restrict the statement; the Library does not provide them as instances of
  `IsNonarchimedeanLocalField`.
- **The spherical function.** The published `inverseSphericalWhittaker` is
  Shintani's explicit spherical Whittaker function for the inverse standard
  character. That it satisfies Jacquet's characterization on page 516 is left
  open in `Whittaker/Spherical.md`. I compared the explicit formula
  `δ_B^{1/2}(ϖ^λ) s_λ(x)` with Jacquet's normalization of `I(t)` for
  `x_i = q^{-t_i}` and found that they agree. This comparison is not a Lean
  proof.
- **Existence with the invariance condition.** Jacquet's Theorem 1 gives a
  `W` with the identity. Averaging `W` over the compact group
  `diag(GL_{n+1}(𝔒), 1)` with Haar probability measure gives a vector of the
  same model with the extra invariance, and it does not change the integrals,
  because `W(·; x; ψ̄)` is right `GL_{n+1}(𝔒)`-invariant and `|det|` is `1` on
  `GL_{n+1}(𝔒)`. This step is implicit in the paragraph after Theorem 1 and
  in JPSS (4.1). The uniqueness claim is JPSS's, cited on page 517.
- **The Whittaker model.** For irreducible generic `π` and nonzero `ℓ`, the
  coefficient model is `𝒲(π; ψ)`, because the Whittaker functional is unique
  up to a scalar. The statements quantify over every nonzero `ℓ`, so they make
  no choice of functional.
- **Measures.** The epsilon relation quantifies over every compatible quotient
  measure on `N_1 \ GL_1(F)` and contains an existence conjunct for such a
  measure (`EpsilonFactor.md`). The essential identity uses the measure `μ`
  fixed by `h`.
- **Ranks.** The essential vector is defined only in rank `n + 2 ≥ 2`, as in
  Jacquet's proof, so `EssentialVectorStatement` and
  `EssentialVectorLevelStatement` cover rank at least two.
  `ConductorExponentStatement` covers every rank `n + 1`, including the rank
  one case of JPSS (1.1).
- **Fields.** `F` is any nonarchimedean local field given by
  `IsNonarchimedeanLocalField`, as in both papers, including fields of positive
  characteristic.
- **Relation to `Langlands.NewvectorStatement`.** The published
  `NewvectorStatement` states the existence, uniqueness and minimality of the
  newvector level for p-adic fields, with no epsilon factor. The
  `ConductorExponentStatement` here also identifies that level with the
  epsilon exponent, as JPSS do, and is stated over the published conductor
  modules.
- **Not stated.** The essential identity for the induced representations of
  Jacquet's Remark 2 (page 524), and the intermediate results of JPSS 1981
  Sections 2-4 and (5.2)-(5.3).

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `EssentialConductorStatement` was inspected: it returns `Prop`,
has universe parameters `uF uV`, and uses only `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry` and no new axiom.
