# Normalized compact sections for the strict rank-one extension

Author: Worker 270, following the statement design (the four conclusions and
their exact Lean ingredients) in Worker 469's task objective.

This module defines the closed proposition
`Langlands.RankinSelberg.RankOneExtensionCompactSectionStatement.{uF,uV,uW}`.
It states the compact-section construction at the start of the proof of JPSS
Lemma (5.5): an actual section of the published lower induction of `(σ, χ)`,
supported in the lower parabolic times the complementary upper cell, whose
restriction to that cell is a normalized compact test function times a fixed
pure tensor, with the test function supported where a supplied vector of `π`
is fixed. The module neither proves nor assumes the proposition. It states no
Whittaker property of any scalar coefficient, no zeta-integral identity, no
scalar cutoff, no Laurent-span containment and no L-factor divisibility.

## Original source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, American Journal of Mathematics 105 (1983), 367–464.

- Registered source: `jpss-1983-rankin-selberg`.
- Retained PDF: `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
- SHA-256: `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- Section 3.1, printed 404–405 (PDF 39–40): `Q` is the **lower** standard
  parabolic subgroup of `G_t` of type `(t₁, …, t_p)` and
  `σ = Ind(G_t, Q; σ₁, …, σ_p)` is normalized induction.
- Lemma (5.5), printed 423 (PDF 58): `t₂ = 1`, `t = t₁ + t₂`, `r ≥ t + 1`,
  `σ = Ind(G_t, Q; σ₁, σ₂)` with `σ₂` a quasicharacter of `F^×`.
- Its proof, printed 424–425 (PDF 59–60), formulas (5)–(7), is the source of
  the construction stated here.

The scanned pages have no text layer and were read directly as rendered
images. A bounded search of the project literature index and the Library notes
found no erratum for the 1983 paper (the available Jacquet correction concerns
the 1981 conductor paper); this is not a claim that none exists elsewhere.
The source allows any nonarchimedean local field; this statement is restricted
to the Library's canonical `PadicField` data.

## The source construction

Printed 424 writes `U` for the space of `σ` and realizes `σ₁` in its Whittaker
model `W(σ₁; ψ)`, so a section is a function `f(g; h)` on `G_t × G_{t₁}` with
`f(g; ·) ∈ W(σ₁; ψ)`. Printed 424–425 then states: given `W₁ ∈ W(σ₁; ψ)`
there are `φ ∈ C_c^∞(Ū_Q)` and `f ∈ U` with

- (5) `∫_{Ū_Q} φ(v) dv = 1`;
- (6) `f(u; h) = W₁(h) φ(u)` for all `h ∈ G_{t₁}`, `u ∈ Ū_Q`.

Writing `q = [[1_{t₁}, 0], [y, 1]] · diag(m, a)` for elements of `Q`, the source
obtains `f` by averaging `F = β ⊗ φ ⊗ W₁ ∈ C_c^∞(G_t) ⊗ W(σ₁; ψ)` over `Q` with
the factor `σ₂⁻¹(a) δ_Q^{-1/2}(q)`; `F` is supported in `Q Ū_Q`, and right
`K`-finiteness of `W₁` reduces the result to (6) for a suitable `β`. Finally,
"since we are still free to choose the support of `φ`", for a given
`W ∈ W(π; ψ)` one may assume

- (7) `W[g · diag(u, 1_{r-t})] = W(g)` for all `u` in the support of `φ`.

## The statement

The proposition quantifies over every prime `p` (with `[Fact p.Prime]`),
`F : PadicField.{uF} p`, unitary additive character `ψ` (for the canonical
topology; the Library's `UnitaryAdditiveCharacter` includes nontriviality) and
supplied `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
Existence of the self-dual measure is not asserted. It quantifies over all
`t k : ℕ`, independent complex modules `V : Type uV` and `W : Type uW` (no
topology on either), a representation `π` of the actual group
`GL_((1+(t+1))+(k+1))(F)` on `V`, a representation `σ` of `GL_(t+1)(F)` on `W`,
an arbitrary `χ : Quasicharacter F.Carrier` for the canonical topology (no
unitarity or ramification restriction), and arbitrary vectors `v : V`, `w : W`.

The only hypotheses are `IsSmooth π` and `IsSmooth σ` for the canonical
topology: every vector is fixed by an open subgroup. No irreducibility,
admissibility or Whittaker-type hypothesis is assumed.

Conclusion: for every `O : Set (Fin (t+1) → F)` that is open and contains `0`,
there exist `φ : SchwartzBruhat (Fin (t+1) → F)` and
`f : rankOneExtensionLowerSection F t χ σ` such that

1. `Function.support φ ⊆ O`, `φ` is integrable for
   `rowMeasure ν.val (t+1)`, and `∫ y, φ y ∂(rowMeasure ν.val (t+1)) = 1`;
2. for every `y`, `rankOneExtensionLowerSectionEval F t χ σ f
   (rankOneExtensionUpperCell t y) = φ y • rankOneExtensionLowerPureTensor w (ULift.up 1)`;
3. for every `g ∈ GL_(1+(t+1))(F)` with nonzero
   `rankOneExtensionLowerSectionEval F t χ σ f g`, there are
   `q : (rankOneExtensionLowerShape t).oppositeParabolic F.Carrier` and
   `y ∈ Function.support φ` with
   `g = (q : GL_(1+(t+1))(F)) * rankOneExtensionUpperCell t y`;
4. for every `y ∈ Function.support φ`,
   `π (rankInclusion (k+1) (rankOneExtensionUpperCell t y)) v = v`.

Items 1, 2, 3, 4 are the four conjuncts of the Lean existential, in that order
(item 1 is three conjuncts).

## Conventions

- **Topology.** `F.Carrier` carries `F.canonicalTopologicalData.topology`,
  introduced by `letI`; the row space `Fin (t+1) → F.Carrier` has the product
  topology, which is the topology in `IsOpen O` and in the Schwartz–Bruhat
  conditions (locally constant with compact support). The `GL` groups carry the
  topologies used by the published `IsSmooth` and the published lower section
  type.
- **Borel structure and measure.** Inside the conclusion `F.Carrier` carries
  `borel F.Carrier` with `BorelSpace` by `⟨rfl⟩`, as in the published span
  comparison statement; `ν.val` is the supplied self-dual additive Haar measure
  for that structure, and `rowMeasure ν.val (t+1)` is its product measure
  `Measure.pi` on the row space (the convention fixed for the cell variable in
  `RankOneExtensionAnalyticData.md`). The integral is the Bochner integral of
  the complex-valued `φ`. The source's `dv` on `Ū_Q` is a Haar measure on
  `Ū_Q ≅ F^{t₁}`; fixing the supplied self-dual product measure is a choice of
  that normalization, and with any other Haar measure (5) only rescales `φ`.
- **Induction.** `rankOneExtensionLowerSection F t χ σ` is the carrier of the
  published `rankOneExtensionLowerModel F t χ σ`: the canonical normalized
  opposite-parabolic induction (`normalizedOppositeParabolicInduced`) for the
  shape `rankOneExtensionLowerShape t`, the reversal of the upper blocks
  `(1, t+1)`, so its opposite parabolic consists of the lower block matrices
  `[m, 0; x, a]` with `m ∈ GL_(t+1)`, `a ∈ GL_1`; this is the source's `Q`.
  The inducing data are the reversed ordered factors `(σ, χLift)` on the
  published tensor space `rankOneExtensionLowerTensor` (over the reversed
  carriers `(W, ULift.{uW} ℂ)`), where `χLift = rankOneExtensionCharacter F χ`
  acts on `ULift.up z` by `ULift.up (χ(det a) z)`. Sections satisfy
  `f(q g) = δ_P(m)^(-1/2) (σ ⊗ χLift)(m) f(g)` with `m` the Levi part of `q` and
  `δ_P` the modulus of the upper parabolic, i.e. the source's `δ_Q^{1/2}` for the
  lower `Q`; they are right-smooth, and `G` acts by right translation.
  `rankOneExtensionLowerSectionEval` is the published `Induction.eval`.
- **Coordinates.** `rankOneExtensionUpperCell t y` is the published unit
  `[I_(t+1), y; 0, 1]` in the explicit coordinates `Fin (t+1) ⊕ Fin 1 ≃
  Fin (1+(t+1))` (large block first, scalar coordinate last); these are the
  elements `u ∈ Ū_Q` of the source with column `y`. `rankInclusion (k+1)` is the
  Library's `g ↦ diag(g, I_(k+1))`, so the element in item 4 is the source's
  `diag(u, 1_{r-t})`. The subgroup coercion `q ↦ (q : GL_(1+(t+1))(F))` in
  item 3 is explicit.

## Index translation and strict range

The Library indexes ranks by predecessors. With JPSS ranks `t₁` for `σ₁` and
`R` for `π`: `t₁ = t + 1`, the induced rank `t₁ + t₂ = t₁ + 1` is `1 + (t+1)`,
and `R = (1 + (t+1)) + (k+1)`. Hence `R ≥ (t₁ + 1) + 1`, which is the source's
hypothesis `r ≥ t + 1` in source notation, and the parent's strict range
`t + 3 ≤ r + 1` with `r + 1 = R`. The trailing identity block has rank
`k + 1 = R - (t₁ + 1) ≥ 1`, the size of `1_{r-t}` in (7). Every strict-range
`R` arises from exactly one `k`, and the equal-rank endpoint `R = t₁ + 1`
(trailing rank zero) is excluded by construction, not by a hypothesis.

## Provenance of the internal refinements

- **Tensor in place of the Whittaker model.** The source realizes `σ₁` in
  `W(σ₁; ψ)` and states (6) with a Whittaker function `W₁`. Here sections take
  values in the published basis-free tensor space and (6) becomes item 2 with
  the pure tensor `w ⊗ 1` for an arbitrary `w ∈ W`. The source's version is
  recovered by applying a Whittaker functional through the published
  `rankOneExtensionTensorContraction` (whose value on the pure tensor is
  `ℓ(w) · 1`); that contraction step is **not** part of this statement, which
  in particular does not claim that any scalar contraction of `f` is a
  Whittaker function. No Whittaker hypothesis on `σ` is needed for the
  construction itself, so none is imposed.
- **Support statement.** The source states that `F`, hence `f`, is supported in
  `Q Ū_Q` (printed 425). Item 3 records the sharper form that the source's
  construction yields: `f` vanishes off `Q · u(supp φ)`. Since
  `Q ∩ Ū_Q = {1}`, item 2 then determines `f` completely from `φ` and `w`.
  The decomposition is stated with an explicit subgroup element `q`, not as a
  set product.
- **Arbitrary neighbourhood and vector form of (7).** The source shrinks the
  support of `φ` after the fact so that (7) holds for one `W ∈ W(π; ψ)`.
  Here the shrinking is made explicit by quantifying over every open
  neighbourhood `O` of zero (item 1), and (7) is stated for the vector `v`
  itself (item 4): every `y ∈ supp φ` fixes `v` under
  `π(diag(u(y), I_(k+1)))`. Since `W(g x) = (π(x) W)(g)` in a Whittaker model,
  this gives (7) for every matrix coefficient `g ↦ λ(π(g) v)` simultaneously,
  with no Whittaker model for `π`.
- **Integrability.** Item 1 records integrability explicitly, so the integral
  equal to `1` is not the Bochner integral's junk value.

The source's averaging formula over `Q`, the auxiliary `β` and the
`K`-finiteness reduction are a proof route and are not part of the statement.
The published `Induction.compactLocalSection` provides local sections at a
point but not the exact restriction to the cell (item 2) or the cell support
(item 3); it is not used in the statement.

## Relation to other units

The published `RankOneExtensionAnalyticData` supplies all the section, tensor
and coordinate names used here; no helper definition is added. The companion
scalar-cutoff statement, the Jacquet/integral comparison and the published
strict span comparison `RankOneExtensionSpanComparisonStatement` are separate
units; this statement is a prerequisite for the early Lemma (5.5) route and
does not prove or assume any of them.
