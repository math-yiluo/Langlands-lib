# Vanishing of bi-equivariant distributions on character-incompatible Bruhat cells

Authors: Worker 634 and Worker 1025. The Lean text of the proposition is Worker 634's
type-checked private design (namespace `Langlands.Whittaker.Design`, module
`BruhatCellStatementDesign`, shared in draft revision 8 of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`), as reproduced in the task objective. Worker
1025 placed it, otherwise unchanged, in the final namespace `Langlands.Whittaker` and
this module, added the docstrings, read the source pages again and wrote this Markdown.

`Langlands.Whittaker.BruhatCellVanishingStatement.{uF}` is the following unproved
proposition. This module defines the proposition and supplies no proof and no other
declaration. It imports, unchanged, the published modules
`Langlands.Representation.Whittaker.BruhatCellDistribution`,
`Langlands.Representation.Whittaker.BruhatFiberAverage`,
`Langlands.HarmonicAnalysis.Distribution.CharacterAverage`,
`Langlands.HarmonicAnalysis.Distribution.Subspace` and Mathlib's
`Mathlib.MeasureTheory.Measure.Haar.Basic`, exactly the imports of the checked target.
The proposition itself mentions no measure; `compatibleTorus` is reached through
`BruhatFiberAverage`, which imports `Langlands.Representation.Whittaker.CompatibleTorus`.

## Statement

The only parameter of the definition is the universe `uF` of the p-adic field. Everything
below is universally quantified inside the proposition, in this order.

- `p : ℕ` is an arbitrary natural number, with a hypothesis `Fact p.Prime`. Every prime
  is allowed.
- `F : PadicField.{uF} p` is an arbitrary p-adic field: a field `F.Carrier` with a
  specified finite-dimensional algebra structure over Mathlib's `Padic p`. Inside the
  proposition `F.Carrier` carries the normed field `F.canonicalNormedField`, Mathlib's
  spectral norm extending the norm of `Padic p`. All topologies below come from this
  norm.
- `n : ℕ` is arbitrary, including `n = 0`. The rank is `n + 1`, so every positive rank
  occurs, rank one included.
- `ψ : UnitaryAdditiveCharacter F.Carrier` is an arbitrary continuous, nontrivial
  unitary additive character. The published structure
  `Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter` bundles an additive character
  `F.Carrier → Circle` with the fields `continuous_toFun` and
  `nontrivial : toAddChar ≠ 1`. So the trivial additive character is not quantified,
  although the proposition writes no separate nontriviality premise.
- `w : Equiv.Perm (Fin (n + 1))` is an arbitrary permutation.

Write `G = Langlands.GeneralLinear (n + 1) F.Carrier`, the matrix group
`Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier` with its topology as units of the
matrix ring, and `C_w = upperBruhatCell (n + 1) F.Carrier w ⊆ G`, the actual double
coset `B * p_w * B`, where `B` is the upper triangular subgroup and
`p_w = GeneralLinear.permutation (n + 1) F.Carrier w`. The type
`UpperBruhatCell (n + 1) F.Carrier w` is the subtype of `G` on `C_w` with the subspace
topology.

**Premise on `w`.** `¬ (compatibleTorus ψ n w).Nonempty`: there is no diagonal parameter
`d : Fin (n + 1) → F.Carrierˣ` in the compatible torus, that is, the compatible torus
is empty. The premise is stated as the negation of `Set.Nonempty`, exactly as in the
target; it is equivalent to `compatibleTorus ψ n w = ∅`
(`Set.not_nonempty_iff_eq_empty`), but the proposition does not use that rewriting.

**Conclusion.** For every algebraic distribution
`D : Distribution (UpperBruhatCell (n + 1) F.Carrier w)` on the cell subtype,

    IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D → D = 0.

Here `0` is the zero element of the complex vector space `Distribution C_w`, the linear
functional sending every test function to `0`. So, for a permutation whose compatible
torus is empty, every positively bi-equivariant algebraic distribution on its cell is
zero; there is no further premise on `D`.

### The premise written out

The published `compatibleTorus ψ n w` is the set of `d` such that the monomial matrix
`s = p_w * GeneralLinear.Iwasawa.diagonalUnits d` is a character-compatible
representative (`mem_compatibleTorus_iff`): for all `u, v` in the upper unipotent
subgroup `U = upperUnipotent (n + 1) F.Carrier`,

    s * u * s⁻¹ = v  →  standardCharacter ψ n u = standardCharacter ψ n v.

Here the published `standardCharacter ψ n : U →* ℂˣ` sends `u` to `ψ` of the sum of the
first superdiagonal entries of `u`. Equivalently
(`mem_compatibleTorus_iff_permutationUnipotentPlus`), for every `u` in
`U_w⁺ = permutationUnipotentPlus (n + 1) F.Carrier w`, the matrices `u ∈ U` with
`p_w u p_w⁻¹ ∈ U`, the character takes the same value at `u` and at `s u s⁻¹`. This is
Shalika's `H_χ`, see below. The premise says that no `d` has this property.

The premise is not vacuous in general, although it never holds in rank one: for
`n = 0` the published `compatibleTorus_rankOne` gives
`compatibleTorus ψ 0 w = Set.univ`, which is nonempty, so in rank one the proposition
holds trivially. For orientation only (a hand computation, not formalized and not used
by the proposition): in rank three, let `w` be the transposition of the first two
indices. Then `U_w⁺` consists of the `u ∈ U` with entry `u₀₁ = 0` (zero-based), and for
such `u` and `s = p_w h(d)`, the superdiagonal of `s u s⁻¹` is `(0, u₀₂ d₀ / d₂)`, while
that of `u` is `(0, u₁₂)`. Taking `u₀₂ = 0` and `u₁₂` arbitrary, compatibility would
force `ψ = 1` on `F`, which the bundled nontriviality excludes; so the compatible torus
of this `w` is empty and the proposition makes a genuine assertion about its cell.

### The conclusion written out

`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D`, from the input definition
artifact `04b24b75-6b0b-41c4-a4a3-d05e55fbaa2a`, says: for all `u₁, u₂ ∈ U` and every
test function `f` on the cell,

    D (Hecke.TestFunction.pullback (bruhatCellBiTranslate n F.Carrier w u₁ u₂) f)
      = ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f,

where `bruhatCellBiTranslate` is the homeomorphism of the cell subtype with underlying
formula `g ↦ u₁ * g * u₂` (`bruhatCellBiTranslate_val`) and `pullback e f g = f (e g)`.
Both character factors are positive (neither is inverted). This is the only premise on
`D`.

`Distribution X` is the published `Module.Dual ℂ (SchwartzBruhat X)`, the full algebraic
dual of the complex vector space of locally constant, compactly supported functions
`X → ℂ`. No continuity of `D` is required, and none is available. The conclusion
`D = 0` means `D f = 0` for every test function `f` on the cell subtype.

## Exact meaning of the imported objects

- `Langlands.GeneralLinear`, `upperUnipotent`, `upperBruhatCell`, `UpperBruhatCell`,
  `permutationUnipotentPlus`, `GeneralLinear.permutation` and
  `GeneralLinear.Iwasawa.diagonalUnits` are the published matrix group, upper unipotent
  subgroup, cell, cell subtype with the inherited subspace topology, Shalika's `U_w⁺`,
  permutation matrices and diagonal map, reached through
  `Langlands.Group.GL.UpperBruhatCells`. No coordinate identification of the cell is
  used.
- `bruhatCellBiTranslate` and `IsBiEquivariantBruhatCellDistribution`, from
  `Langlands.Representation.Whittaker.BruhatCellDistribution`, are the published cell
  translations and the cellwise positive-character bi-equivariance predicate. The
  public Markdown of that module explains them.
- `compatibleTorus`, from `Langlands.Representation.Whittaker.CompatibleTorus`, is the
  published compatible locus.
- `standardCharacter`, from `Langlands.Representation.Whittaker.GeneralLinear`, is the
  published standard character with all coefficients equal to one.
- `Distribution`, `SchwartzBruhat` and `Hecke.TestFunction.pullback` are the published
  algebraic distributions, test functions and test-function pullback.

No replacement cell, test-function space, distribution notion, character or
representation is introduced. The proposition involves no measure.

## Hypotheses that are deliberately absent

- No measure, Haar-measure, countability or orbital-integration hypothesis: the
  proposition quantifies over no measure and no orbital-integral map.
- No factorization, support or distribution theorem, and no torus distribution, among
  the hypotheses. In particular no `Distribution.supportedOn` condition appears.
- No cell-stability (`MapsTo`) hypothesis for the transpose, and no transpose at all.
- No auxiliary invariance hypothesis on `D`, and no continuity, boundedness or
  positivity of `D`.
- No global distribution on `GL_{n+1}`; `D` lives on the cell.
- No finiteness statement about `U × U` orbits: the proposition is a statement about
  all distributions on one actual cell, not about a finite collection of orbits.
- No hypothesis on `ψ` beyond its type, which forces continuity and nontriviality.
- No restriction on `p`, `F`, `n` or `w` beyond the emptiness premise.

The complementary case, a nonempty compatible torus, is not covered here. There the
published statement `Langlands.Whittaker.BruhatCellInvarianceStatement` (module
`Langlands.Representation.Whittaker.BruhatCellInvarianceStatement`) asserts cell
stability and transpose invariance; it is neither a premise nor a consequence of the
present proposition.

## Relation to Shalika, Propositions 1.12–1.13 and 1.8

The registered original is `shalika-1974-multiplicity-one`: J. A. Shalika, *The
multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193. The copy
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`. Worker
1025 read the extracted text of printed pp.174–178 (one-based PDF pages 5–9) and
checked the rendered image of printed p.177 (PDF page 8). Worker 634 earlier read
printed pp.173–179 and visually checked pp.176–178. The only known misprint on these
pages, in the proof of Proposition 1.13, is explained in the public Markdown of
`Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement`: the printed map
"β ↦ (γ − 1)β" must be read as `β ↦ (δ − 1)β`. It does not affect the reading below.

- **Printed p.175, Proposition 1.8.** A distribution `T` on the cell `G_w` with
  `T(L_{u₁⁻¹} R_{u₂} f) = χ(u₁u₂) T(f)` for all `f ∈ C_c^∞(G_w)` and `u₁, u₂ ∈ U`. With
  the source's translations `(L_x f)(y) = f(x⁻¹ y)` and `(R_x f)(y) = f(y x)`
  (printed p.174), the translated test function is `g ↦ f(u₁ g u₂)` and
  `χ(u₁u₂) = χ(u₁)χ(u₂)`; this is `IsBiEquivariantBruhatCellDistribution`, with `χ`
  the standard character `standardCharacter ψ n`. The source's cells `G_w = H U w U`
  (printed p.174), for `w` in a set of Weyl representatives, are for `GL_{n+1}` the
  actual double cosets `B p_w B`.
- **Printed pp.176–177, Lemma 1.10, (1.11), Proposition 1.12.** With
  `M₁ = U × H × U` and `π(u₁, h, u₂) = u₁ w h u₂`, each `α ∈ C_c^∞(M₁)` has an orbital
  integral `f_α ∈ C_c^∞(G_w)`, and `α ↦ f_α` is surjective (Lemma 1.10). Putting
  `T*(α) = T(f_α)`, Proposition 1.12 gives a unique distribution `τ` on `H` with
  `T*(α) = τ(β_α)`, where `β_α(h) = ∫_{U×U} α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂`.
- **Printed p.177, the set `H_χ` and Proposition 1.13.** `H_χ` is the set of `h ∈ H`
  with `χ(w h u h⁻¹ w⁻¹) = χ(u)` for all `u ∈ U_w⁺`, and Proposition 1.13 states that
  `τ` has support in `H_χ`.
- **Printed p.178, proof of Proposition 1.8.** The proof recalls that `τ` has support
  in `H_χ` and continues with "Suppose then that `H_χ` is non-empty." The empty case is
  left implicit: a distribution with support in the empty set is zero, so
  `T(f_α) = τ(β_α) = 0` for every `α`, and surjectivity of `α ↦ f_α` gives `T = 0`.

**What is derived, not transcribed.** The source has no separately stated proposition
for the empty case; the present proposition is the internal derived interface for it:

- the premise is emptiness (failure of `Nonempty`) of the published
  `compatibleTorus ψ n w`, the Lean counterpart of `H_χ`, realized as a set of
  parameters `d` with `h = diagonalUnits d` and `w` realized as `p_w`;
- the conclusion is the vanishing of the cell distribution itself, the source's
  implicit consequence `T = 0`, rather than the source's statement about `τ`;
- `χ` is the standard character `standardCharacter ψ n`;
- the full algebraic dual replaces the source's distributions;
- the field is restricted to p-adic fields; the source allows any local field.

## Intended later proof (not established here)

The following outlines how the proposition is expected to be proved, in a separate
proof task. None of it is established by this module, and no theorem about the present
proposition is claimed. The later proof may take a different route.

1. **Measures and orbital integral.** The published
   `Langlands.Whittaker.bruhatHaarMeasure` (statement `BruhatHaarMeasureStatement`)
   supplies a Haar measure `μ` on `U` and a Haar measure `ν` on `U_w⁺`, each σ-finite and
   right invariant. The published `Langlands.Whittaker.bruhatOrbitalIntegration`
   (statement `BruhatOrbitalIntegrationStatement`) supplies, for `ν`, a surjective
   complex-linear map `I` from test functions on `U × (H × U)` to test functions on the
   cell whose value at `upperBruhatTorusMap (n + 1) w m` is the published fiber average
   `bruhatFiberAverage (n + 1) F.Carrier w ν α m` (Shalika's (1.11)).
2. **Factorization.** The published `Langlands.Whittaker.bruhatCellFactorization`
   (statement `BruhatCellFactorizationStatement`) gives, for a positively bi-equivariant
   `D`, a torus distribution `τ` with
   `τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)` and
   `Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ = D.comp I`.
3. **Empty support.** By `Distribution.mem_supportedOn_iff`, membership in
   `supportedOn Z` means that `τ` kills every test function vanishing on `Z`. When
   `Z = compatibleTorus ψ n w` is empty, every test function vanishes on `Z`, so
   `τ = 0`. Since `characterAverageDual` is complex-linear, `D.comp I = 0`.
4. **Conclusion.** Surjectivity of `I` then gives `D f = 0` for every cell test
   function `f`, that is, `D = 0`.

Only finite linearity of the algebraic dual is used; no distribution is commuted with an
infinite integral. These steps follow the logic of printed pp.176–178 and are not
verbatim source statements.

## Scope

This is a statement only. It proves no vanishing assertion. It also states and proves
nothing about: the nonempty compatible-torus case, cell stability or transpose
invariance; factorization or support of cell distributions; orbital integrals; Haar
measures; Shalika's Propositions 1.8, 1.12 or 1.13 as stated in the source; global
distribution invariance (Shalika's Theorem 1.6); or multiplicity one. Its acceptance is
not evidence that it is true.

## Provenance

The Lean text is Worker 634's private type-checked design, reproduced exactly from the
task objective, placed in its final namespace and module by Worker 1025 and checked in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (diagnostics
`76b5a55e-9eeb-40ce-8431-2f4de31caadb` and, after the last docstring edit,
`cf565363-a420-45bf-8b2c-55991b054341`: no errors or warnings, statement returns `Prop`,
axioms `propext`, `Classical.choice` and `Quot.sound`). The formulation is
internal derived content, as explained above; its sources are Shalika (1974),
Lemma 1.10 and (1.11) (printed p.176), Propositions 1.12 and 1.13 (printed p.177) and
the proof of Proposition 1.8 (printed p.178).

## Consumers

The proposition is an intermediate target for the exact Shalika distribution-invariance
work (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, Worker 634) and, through it, the
Whittaker multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`, Worker 16).
Once proved, it would supply, for p-adic fields and permutations with an empty
compatible torus, the first alternative of the disjunctive premise of the published
`Langlands.Whittaker.BruhatCellRestrictionVanishingStatement`. A separate
proof task follows publication of this statement.
