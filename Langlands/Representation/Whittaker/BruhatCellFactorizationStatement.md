# Factorization of a bi-equivariant cell distribution over the compatible torus

Authors: Worker 634 and Worker 1035. The Lean text of the proposition is Worker 634's
type-checked private design, as supplied in the task objective. Worker 1035 placed it,
otherwise unchanged, in the final namespace `Langlands.Whittaker` and this module, added
the docstrings and wrote this Markdown.

`Langlands.Whittaker.BruhatCellFactorizationStatement.{uF}` is the following unproved
proposition. This module defines the proposition and supplies no proof and no other
declaration. It imports, unchanged, the published modules
`Langlands.Representation.Whittaker.BruhatCellDistribution`,
`Langlands.Representation.Whittaker.BruhatFiberAverage`,
`Langlands.HarmonicAnalysis.Distribution.CharacterAverage`,
`Langlands.HarmonicAnalysis.Distribution.Subspace` and Mathlib's
`Mathlib.MeasureTheory.Measure.Haar.Basic`.

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

With these data the proposition introduces the local names

- `U = upperUnipotent (n + 1) F.Carrier`, the upper unipotent subgroup of
  `Langlands.GeneralLinear (n + 1) F.Carrier`, that is of
  `Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier`, with the subspace topology of the
  matrix group;
- `P = permutationUnipotentPlus (n + 1) F.Carrier w`, Shalika's `U_w⁺ = U ∩ w⁻¹ U w`:
  the matrices `g ∈ U` with `p_w * g * p_w⁻¹ ∈ U`, where
  `p_w = GeneralLinear.permutation (n + 1) F.Carrier w`. It is used as a type through its
  coercion to the subtype of the matrix group;
- `H = Fin (n + 1) → F.Carrierˣ`, the diagonal parameters, with the product topology of
  the unit groups;
- `M = U × (H × U)`, the right-associated product, with the product topology;
- `C = UpperBruhatCell (n + 1) F.Carrier w`, the subtype of the actual double coset
  `B * p_w * B` in the matrix group, `B` the upper triangular subgroup, with the
  inherited subspace topology. No coordinate identification of the cell is used.

It equips `U` with its Borel σ-algebra (`letI := borel U`), records that this is a Borel
space (`letI : BorelSpace U := ⟨rfl⟩`), and equips `P` with its Borel σ-algebra
(`letI := borel P`). Then, further quantified:

- `μ : Measure U` is a Haar measure (`Measure.IsHaarMeasure μ`), s-finite (`SFinite μ`)
  and right invariant (`μ.IsMulRightInvariant`).
- `ν : Measure P` is a Haar measure (`Measure.IsHaarMeasure ν`) and right invariant
  (`ν.IsMulRightInvariant`).
- `I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C` is an arbitrary complex-linear map from
  test functions on `M` to test functions on the cell.

**Hypothesis on `I` (evaluation formula).** For every `α : SchwartzBruhat M` and every
`m : M`,

    I α (upperBruhatTorusMap (n + 1) w m) = bruhatFiberAverage (n + 1) F.Carrier w ν α m.

Then, for every algebraic distribution `D : Distribution C`:

**Hypothesis on `D` (cellwise bi-equivariance).**
`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D`.

**Conclusion.** There is a unique `τ : Distribution H` such that

    τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)   and
    Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ = D.comp I.

The uniqueness clause of `∃!` is taken over the conjunction: any `τ'` satisfying both
clauses equals `τ`.

### The hypotheses written out

Write `χ = standardCharacterContinuous ψ n`, `h(d) = GeneralLinear.Iwasawa.diagonalUnits d`
for `d : H`. The published `standardCharacter ψ n : U →* ℂˣ` sends `g ∈ U` to `ψ` of the
sum of the first superdiagonal entries of `g`; `χ` is the same homomorphism packaged as a
continuous homomorphism, so `(χ u : ℂ) = (standardCharacter ψ n u : ℂ)`.

- `upperBruhatTorusMap (n + 1) w (u₁, (d, u₂))` is the cell element with underlying
  matrix `u₁ * p_w * h(d) * u₂` (`upperBruhatTorusMap_val`), Shalika's
  `π(u₁, h, u₂) = u₁ w h u₂`.
- `bruhatFiberAverage (n + 1) F.Carrier w ν α m = ∫ u, α (bruhatFiberAct u m) ∂ν`
  (`bruhatFiberAverage_apply`), the unweighted Bochner integral over `P`, where

      bruhatFiberAct u (u₁, (d, u₂)) =
        (u₁ * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹, (d, u * u₂)).

So the hypothesis on `I` says: for all `α`, `u₁, u₂ ∈ U` and `d ∈ H`,

    I α (u₁ p_w h(d) u₂) = ∫_P α (u₁ p_w h(d) u⁻¹ h(d)⁻¹ p_w⁻¹, (d, u u₂)) dν(u).

This prescribes the values of `I α` at the points of the image of `upperBruhatTorusMap`.
Shalika observes that `π` is surjective onto the cell (printed p.176), so the formula
determines `I` when such an `I` exists; the proposition neither states nor uses this
surjectivity, and it does not assert that such an `I` exists.

`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D`, from the input definition
artifact `04b24b75-6b0b-41c4-a4a3-d05e55fbaa2a`, says: for all `u₁, u₂ ∈ U` and every
test function `f` on the cell,

    D (Hecke.TestFunction.pullback (bruhatCellBiTranslate n F.Carrier w u₁ u₂) f)
      = ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f,

where `pullback e f g = f (e g)` and `bruhatCellBiTranslate` has underlying formula
`g ↦ u₁ * g * u₂`. Both character factors are positive. This is the only premise on `D`.

### The conclusion written out

`D.comp I` is the composite linear functional `α ↦ D (I α)` on test functions on `M`.
By the published evaluation laws, `characterAverageDual χ μ τ α = τ β_α`
(`characterAverageDual_apply`), where `β_α = SchwartzBruhat.characterAverage χ μ α` is
the test function on `H` with

    β_α d = ∫ z : U × U, α (z.1, (d, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)

(`characterAverage_apply`). The weight is the inverse of both character values; for the
unitary character `χ` this is Shalika's `χ̄(u₁u₂)`. The equality of linear maps in the
conclusion therefore says `τ β_α = D (I α)` for every `α : SchwartzBruhat M`.

`Distribution X` is the published `Module.Dual ℂ (SchwartzBruhat X)`, the full algebraic
dual of the locally constant, compactly supported functions `X → ℂ`; no continuity of
`D` or `τ` is required, and none is available. `Distribution.supportedOn Z` is the
published submodule with carrier
`{τ | ∀ f : SchwartzBruhat H, (∀ z ∈ Z, f z = 0) → τ f = 0}` (`mem_supportedOn_iff`):
`τ` kills every test function vanishing on `Z`. The published `compatibleTorus ψ n w`
is closed (`isClosed_compatibleTorus`) and is the set of `d : H` with
`χ(p_w h(d) u h(d)⁻¹ p_w⁻¹) = χ(u)` for every `u ∈ U_w⁺`
(`mem_compatibleTorus_iff_permutationUnipotentPlus`), Shalika's `H_χ`. The public
Markdown of `BruhatCompatibleSupportStatement` explains this support convention in
detail.

## Exact meaning of the imported objects

- `Langlands.GeneralLinear`, `upperUnipotent`, `permutationUnipotentPlus`,
  `upperBruhatCell`, `UpperBruhatCell`, `upperBruhatTorusMap`,
  `GeneralLinear.permutation` and `GeneralLinear.Iwasawa.diagonalUnits` are the
  published matrix group, subgroups, cell, cell subtype, torus-coordinate multiplication
  map, permutation matrices and diagonal map, reached through
  `Langlands.Group.GL.UpperBruhatCells`.
- `bruhatCellBiTranslate` and `IsBiEquivariantBruhatCellDistribution`, from
  `Langlands.Representation.Whittaker.BruhatCellDistribution`, are the published cell
  translations and the cellwise bi-equivariance predicate described above.
- `bruhatFiberAct` and `bruhatFiberAverage`, from
  `Langlands.Representation.Whittaker.BruhatFiberAverage`, are the published action of
  `P` on `M` and its raw fiber integral, a complex-linear map from test functions on `M`
  to complex functions on `M`. It needs only `IsFiniteMeasureOnCompacts ν`, supplied by
  the Haar hypothesis.
- `compatibleTorus`, from `Langlands.Representation.Whittaker.CompatibleTorus`, is the
  published closed compatible locus.
- `standardCharacterContinuous`, from `Langlands.Representation.Whittaker.GeneralLinear`,
  is the published continuous standard character.
- `SchwartzBruhat.characterAverage` and `Distribution.characterAverageDual`, from
  `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, are the published weighted
  product average and its algebraic dual `τ ↦ τ ∘ characterAverage χ μ`. They require
  `[SFinite μ]`, `[IsFiniteMeasureOnCompacts μ]` and an opens-measurable structure on
  `U`; the last two come from the Haar hypothesis and the Borel structure.
- `Distribution` and `Distribution.supportedOn`, from
  `Langlands.HarmonicAnalysis.Distribution.Basic` and `.Subspace`, are as described
  above.
- `Measure.IsHaarMeasure`, `SFinite`, `Measure.IsMulRightInvariant` and `borel` are
  Mathlib's.

No replacement cell, test-function space, distribution notion, support notion, measure
normalization, abstract orbital-integration operator or representation is introduced.

## Hypotheses that are deliberately absent

- No surjectivity, support or continuity premise on `I`, and no assertion that an `I`
  with the evaluation formula exists. The existence and uniqueness of such an `I`, with
  surjectivity and a support bound, is the separate published statement
  `Langlands.Whittaker.BruhatOrbitalIntegrationStatement`, proved by the published
  `Langlands.Whittaker.bruhatOrbitalIntegration`; it is neither a premise nor a
  consequence of the present proposition.
- No continuity, boundedness or positivity of `D` or `τ`.
- No Weyl-transpose invariance of `D`, no cell-stability (`MapsTo`) hypothesis and no
  global distribution on `GL_{n+1}`. Only the positive-character bi-equivariance is
  assumed.
- `SFinite μ` and right invariance of `μ` and `ν` are explicit hypotheses and are not
  inferred from the Haar property inside the proposition. For actual Haar measures they
  are dischargeable obligations: the published `Langlands.Whittaker.bruhatHaarMeasure`
  proves `BruhatHaarMeasureStatement`, which gives σ-finiteness and right invariance of
  every Haar measure on `U` and on every `P`, for the same Borel structures; the
  published `upperUnipotent_sFinite_of_isHaarMeasure` gives s-finiteness on `U`.
- No normalization of `μ` or `ν`. Both are arbitrary within their hypotheses, and `τ`
  is attached to the given pair. Informally, by uniqueness, replacing `ν` by `c • ν`
  multiplies the unique `τ` by `c`, and replacing `μ` by `c • μ` multiplies it by `c⁻²`;
  this remark is not stated in Lean.
- No hypothesis on `ψ` beyond its type, which forces continuity and nontriviality.
- No restriction on `p`, `F`, `n` or `w`.

## The case n = 0

For `n = 0` the published `compatibleTorus_rankOne` gives
`compatibleTorus ψ 0 w = Set.univ`. A test function vanishing on all of `H` is zero, so
every `τ` lies in `supportedOn Set.univ` and the support clause is automatic. The
factorization clause and its uniqueness remain genuine assertions in rank one. The case
is kept in the quantification, not excluded.

## Relation to Shalika, Lemma 1.10, (1.11) and Propositions 1.8, 1.12, 1.13

The registered original is `shalika-1974-multiplicity-one`: J. A. Shalika, *The
multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193. The copy
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`. Worker
1035 read the text of printed pp.174–178 (one-based PDF pages 5–9) and checked the
rendered image of printed p.177 (PDF page 8). Worker 634 earlier read printed
pp.173–179 and visually checked pp.176–178. No source-specific errata note
for this paper exists in the project literature pointers or the Library notes.

- **Printed p.175, Proposition 1.8.** `T` is a distribution on the cell `G_w` with
  `T(L_{u₁⁻¹} R_{u₂} f) = χ(u₁u₂) T(f)` for `u₁, u₂ ∈ U`. With the source's translations
  `(L_x f)(y) = f(x⁻¹y)` and `(R_x f)(y) = f(yx)` (printed p.174) the translated test
  function is `g ↦ f(u₁ g u₂)`, and `χ(u₁u₂) = χ(u₁)χ(u₂)`, so this is
  `IsBiEquivariantBruhatCellDistribution`, as explained in the public Markdown of
  `BruhatCellDistribution`.
- **Printed p.176, Lemma 1.10 and (1.11).** `M₁ = U × H × U`, `π(u₁, h, u₂) = u₁ w h u₂`
  onto `M₂ = G_w`. Lemma 1.10 attaches to each `α ∈ C_c^∞(M₁)` a unique
  `f_α ∈ C_c^∞(M₂)` by an integration identity and states that `α ↦ f_α` is a continuous
  surjection with `Supp f_α ⊂ π(Supp α)`. With the action
  `u * m = (u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂)` of `U_w⁺` the source derives formula (1.11),
  `f_α(π(m)) = ∫_{U_w⁺} α(u * m) du⁺`. The hypothesis on `I` is (1.11).
- **Printed p.177, the `U × U` actions.** The source defines an action of `U × U` on
  `M₁` and on `M₂` by `(u₁, u₂) ∘ m = u₁ m u₂⁻¹`, with an inverse on the second factor.
  The extracted PDF text drops the superscript `⁻¹`, but the rendered page shows it. On
  `M₁` this is read as acting on the outer factors,
  `(v₁, h, v₂) ↦ (u₁ v₁, h, v₂ u₂⁻¹)`, which makes `π` equivariant. `U × U` then acts on
  functions by duality, and the source notes that `α ↦ f_α` commutes with these
  actions. The inverse is what makes this a left action of the group `U × U`. Without
  it, applying `(c, d)` and then `(a, b)` sends `m` to `a c m d b`, while `(ac, bd)`
  sends it to `a c m b d`; these differ for noncommuting `b, d`, which exist in `U`
  from rank three on.

  The Lean statement does not use this action. It uses the direct bi-translations
  `g ↦ a g b`: `bruhatCellBiTranslate a b` on the cell, and in step 1 below
  `(z₁, (y, z₂)) ↦ (a z₁, (y, z₂ b))` on `M`. The direct bi-translation `m ↦ a m b` is
  the source action evaluated at `(a, b⁻¹)`. Its pullback `f ↦ f(a · b)` is
  `L_{a⁻¹} R_b f` in the source's notation (printed p.174). Since `b ↦ b⁻¹` is a
  bijection of `U`, commuting with the source action at every `(u₁, u₂)` is the same as
  commuting with the pullback along every direct bi-translation. So, as the source
  concludes, `T*(α) = T(f_α)` satisfies the hypothesis of Proposition 1.12,
  `T*(L_{u₁⁻¹} R_{u₂} α) = χ(u₁u₂) T*(α)`. Written with direct bi-translations this is
  `T*(α(u₁ · u₂)) = χ(u₁) χ(u₂) T*(α)`, with the same two positive character factors
  as Proposition 1.8. These are the positive factors in
  `IsBiEquivariantBruhatCellDistribution` and in step 1 below. The Lean conclusion uses
  the same signs: `characterAverageDual` weights by the inverse of both character values,
  which is Shalika's `χ̄(u₁u₂)`.
- **Printed p.177, Propositions 1.12 and 1.13.** **Proposition 1.12**
  defines `β_α(h) = ∫ α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂`, asserts that `α ↦ β_α` is
  surjective and that `T*(α) = τ(β_α)` for a unique distribution `τ` on `H`; its proof
  is omitted in the source ("similar to Lemma 21 of [11]"). `H_χ` is defined, and
  **Proposition 1.13** asserts that this `τ` has support in `H_χ`.

**What is derived, not transcribed.** The source never states one proposition with the
present content: it passes from `T` to `T*` through Lemma 1.10 and (1.11), applies
Proposition 1.12 to `T*`, and then proves Proposition 1.13 for the resulting `τ`. The
present proposition is an internal derived interface that packages this chain: for the
cell distribution `D` (the source's `T`) and any linear `I` satisfying (1.11) (the
source's `α ↦ f_α`), there is a unique `τ` supported on the compatible torus with
`τ(β_α) = D(I α)`. Further internal choices are:

- `I` is characterized only by the formula (1.11), not by the integration identity of
  Lemma 1.10, and neither its existence nor its surjectivity is asserted or assumed;
- the uniqueness clause is over `τ` satisfying both the support and the factorization
  clause; the source's uniqueness among `τ` satisfying the factorization alone, and the
  surjectivity of `α ↦ β_α`, are not stated here;
- the realization of `w` as `p_w` and of `H` as `Fin (n + 1) → F.Carrierˣ` through
  `h(d)`, with `χ̄` written as the inverse of the product of the two character values;
- arbitrary Haar measures `μ` on `U` and `ν` on `U_w⁺` with explicit s-finiteness and
  right invariance, in place of the source's fixed invariant measures;
- the full algebraic dual and the `supportedOn` convention in place of the source's
  distributions and `Supp τ`;
- the restriction to p-adic fields; the source allows any local field `k`.

The source proof of Proposition 1.13 contains a misprint: the map "β ↦ (γ − 1)β" must
be read as `β ↦ (δ − 1)β`, with the `δ` defined two lines earlier, as recorded in the
public Markdown of `BruhatCompatibleSupportStatement`. The present proposition does not
depend on that reading.

## Intended later proof (not established here)

The following outlines how the proposition is expected to be proved, in a separate
proof task. None of it is established by this module, and no theorem is claimed.

1. **Positive-character product bi-equivariance of `D.comp I`.** For `a, b ∈ U` and
   `u ∈ P`, if `bruhatFiberAct u (u₁, (d, u₂)) = (x₁, (d, x₂))`, then
   `bruhatFiberAct u (a * u₁, (d, u₂ * b)) = (a * x₁, (d, x₂ * b))`, and
   `upperBruhatTorusMap` sends `(a * x₁, (d, x₂ * b))` to `a * π(x₁, d, x₂) * b`.
   Hence `I` intertwines the product translation
   `(z₁, (y, z₂)) ↦ (a z₁, (y, z₂ b))` on `M` with the cell translation
   `bruhatCellBiTranslate a b`, on the image of `upperBruhatTorusMap`, and on the whole
   cell once surjectivity of that map onto the cell is available. The bi-equivariance of
   `D` then gives
   `D (I (α ∘ ((a·) × id × (·b)))) = ((χ a : ℂ) * (χ b : ℂ)) * D (I α)`.
2. **Generic factorization.** This is the hypothesis of the published
   `Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement` for
   `G = U`, `Y = H`, `χ` and `μ`, proved by the published
   `Langlands.HarmonicAnalysis.Distribution.characterAverageFactorization`. It yields a
   unique `τ` with `characterAverageDual χ μ τ = D.comp I`. Its topological instance
   hypotheses (Hausdorff, locally compact, non-archimedean `U`; Hausdorff, locally
   compact, totally disconnected `H`) must be supplied for the canonical topology. Its
   uniqueness rests on the published surjectivity
   `Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageSurjective`, not on any
   continuity of `τ`.
3. **Fiber invariance.** For `u ∈ P`, the composition law `u' * (u * m) = (u' u) * m`
   (`bruhatFiberAct_bruhatFiberAct`) and right invariance of `ν` show that `I` is
   unchanged when `α` is replaced by
   `Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α`.
   So `characterAverageDual χ μ τ = D.comp I` is invariant under every fiber action.
4. **Support.** The published `Langlands.Whittaker.bruhatCompatibleSupport` proves
   `BruhatCompatibleSupportStatement`, which turns this invariance into
   `τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)`. Uniqueness over the
   conjunction follows from the uniqueness in step 2.

The forward fiber average uses `ν`; the weighted product average uses `μ` with the
inverses of both character factors. No scalar normalization beyond these exact measures
enters.

## Scope

This is a statement only. It proves no factorization, support or uniqueness assertion.
It also states and proves nothing about: the existence or surjectivity of `I`,
surjectivity of `upperBruhatTorusMap` onto the cell, the intertwining of step 1,
surjectivity of the character average, transpose invariance, closed restriction or
supported descent, Shalika's Propositions 1.8, 1.12 or 1.13 as stated in the source,
global distribution invariance, or multiplicity one.

## Provenance

The Lean text is Worker 634's private type-checked design, reproduced exactly from the
task objective, placed in its final namespace and module by Worker 1035 and checked here
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (diagnostic
`af4adeda-8bd8-4dd2-a660-25b739b59136`: no errors or warnings, statement returns `Prop`).
The formulation is internal derived content, as explained above; its sources are
Shalika (1974), Proposition 1.8 (printed p.175), Lemma 1.10 and formula (1.11) (printed
p.176), and Propositions 1.12 and 1.13 (printed p.177).

## Consumers

The proposition is an intermediate target for the exact Shalika distribution-invariance
work (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, Worker 634) and, through it, the
Whittaker multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`, Worker 16).
A separate proof task follows publication of this statement.
