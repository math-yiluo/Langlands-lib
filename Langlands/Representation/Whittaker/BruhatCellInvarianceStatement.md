# Transpose invariance of bi-equivariant distributions on compatible Bruhat cells

Authors: Worker 634 and Worker 1051. The Lean text of the proposition is Worker 634's
type-checked private design (namespace `Langlands.Whittaker.Design`, shared in draft
revision 5 of task `f79ca82c-d050-4ffa-821b-c347b60e36e0`), as reproduced in the task
objective. Worker 1051 placed it, otherwise unchanged, in the final namespace
`Langlands.Whittaker` and this module, added the docstrings and wrote this Markdown.

`Langlands.Whittaker.BruhatCellInvarianceStatement.{uF}` is the following unproved
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
matrix ring; `C_w = upperBruhatCell (n + 1) F.Carrier w ⊆ G`, the actual double coset
`B * p_w * B`, where `B` is the upper triangular subgroup and
`p_w = GeneralLinear.permutation (n + 1) F.Carrier w`; and
`τ = weylTransposeHomeomorph n F.Carrier : G ≃ₜ G`.

**Premise.** `(compatibleTorus ψ n w).Nonempty`: there is a diagonal parameter
`d : Fin (n + 1) → F.Carrierˣ` in the compatible torus. This is the only premise before
the conclusion.

**Conclusion.** There exists

    hτ : Set.MapsTo τ C_w C_w

such that for every algebraic distribution
`D : Distribution (UpperBruhatCell (n + 1) F.Carrier w)` on the cell subtype,

    IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D →
      IsWeylTransposeInvariantBruhatCellDistribution n F.Carrier w hτ D.

So the conclusion first asserts cell stability, `τ(C_w) ⊆ C_w`, and then, using that
proof to restrict `τ` to the cell, asserts invariance of every positively bi-equivariant
cell distribution. Cell stability is part of the conclusion, not a hypothesis. The
existential quantifies over proofs of a proposition, so by proof irrelevance any two
choices of `hτ` are equal; the conclusion is equivalent to "`τ` maps `C_w` into itself,
and every positively bi-equivariant `D` is invariant under the restriction of `τ`".

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
Shalika's `H_χ`, see below. The set is closed (`isClosed_compatibleTorus`); the
proposition uses only its nonemptiness.

### The conclusion written out

`weylTransposeHomeomorph n F.Carrier` is the published homeomorphism
`g ↦ J * gᵀ * J` of `G`, with `J = weylLong (n + 1) F.Carrier` the antidiagonal
permutation matrix (`weylTransposeHomeomorph_apply`). Its entries are
`(τ g) i j = g j.rev i.rev` (`weylTransposeHomeomorph_entry`); it is an involution
(`weylTransposeHomeomorph_involutive`) and reverses products
(`weylTransposeHomeomorph_mul`). `Set.MapsTo τ C_w C_w` means `τ g ∈ C_w` for every
`g ∈ C_w`.

Given `hτ`, the published `bruhatCellWeylTranspose n F.Carrier w hτ` is the
homeomorphism of the subtype `UpperBruhatCell (n + 1) F.Carrier w` with underlying
formula `g ↦ τ g` (`bruhatCellWeylTranspose_val`), its own inverse.
`IsWeylTransposeInvariantBruhatCellDistribution n F.Carrier w hτ D` is the equation
`Distribution.pushforward (bruhatCellWeylTranspose n F.Carrier w hτ) D = D`. By the
published `isWeylTransposeInvariantBruhatCellDistribution_iff` it says exactly

    ∀ f : SchwartzBruhat (UpperBruhatCell (n + 1) F.Carrier w),
      D (Hecke.TestFunction.pullback (bruhatCellWeylTranspose n F.Carrier w hτ) f) = D f,

where `pullback e f g = f (e g)`. In Shalika's notation this is `T(f^θ) = T(f)`. The
pushforward carries no measure or modular factor.

`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D`, from the input definition
artifact `04b24b75-6b0b-41c4-a4a3-d05e55fbaa2a`, says: for all `u₁, u₂ ∈ U` and every
test function `f` on the cell,

    D (Hecke.TestFunction.pullback (bruhatCellBiTranslate n F.Carrier w u₁ u₂) f)
      = ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) * D f,

where `bruhatCellBiTranslate` has underlying formula `g ↦ u₁ * g * u₂`
(`bruhatCellBiTranslate_val`). Both character factors are positive. This is the only
premise on `D`.

`Distribution X` is the published `Module.Dual ℂ (SchwartzBruhat X)`, the full algebraic
dual of the complex vector space of locally constant, compactly supported functions
`X → ℂ`. No continuity of `D` is required, and none is available.

## Exact meaning of the imported objects

- `Langlands.GeneralLinear`, `upperUnipotent`, `upperBruhatCell`, `UpperBruhatCell`,
  `permutationUnipotentPlus`, `GeneralLinear.permutation` and
  `GeneralLinear.Iwasawa.diagonalUnits` are the published matrix group, upper unipotent
  subgroup, cell, cell subtype with the inherited subspace topology, Shalika's `U_w⁺`,
  permutation matrices and diagonal map, reached through
  `Langlands.Group.GL.UpperBruhatCells`. No coordinate identification of the cell is
  used.
- `weylTransposeHomeomorph`, from `Langlands.Representation.Whittaker.Distribution`, is
  the actual Weyl-conjugated transpose described above.
- `bruhatCellBiTranslate`, `IsBiEquivariantBruhatCellDistribution`,
  `bruhatCellWeylTranspose` and `IsWeylTransposeInvariantBruhatCellDistribution`, from
  `Langlands.Representation.Whittaker.BruhatCellDistribution`, are the published cell
  translations, the cellwise positive-character bi-equivariance predicate, the
  restricted transpose given a stability proof, and the invariance predicate. The
  public Markdown of that module explains them.
- `compatibleTorus`, from `Langlands.Representation.Whittaker.CompatibleTorus`, is the
  published compatible locus.
- `standardCharacter`, from `Langlands.Representation.Whittaker.GeneralLinear`, is the
  published standard character with all coefficients equal to one.
- `Distribution`, `Distribution.pushforward`, `SchwartzBruhat` and
  `Hecke.TestFunction.pullback` are the published algebraic distributions, their
  pushforward `(e_* D)(f) = D(f ∘ e)` along a homeomorphism, test functions and test
  function pullback.

No replacement cell, test-function space, distribution notion, transpose, character or
representation is introduced. The proposition involves no measure.

## Hypotheses that are deliberately absent

- No cell-stability (`MapsTo`) hypothesis. Stability is asserted, not assumed, and only
  for `w` with a nonempty compatible torus. For arbitrary `w` it can fail: the published
  `Langlands.GeneralLinear.upperBruhatTranspose` proves `UpperBruhatTransposeStatement`,
  which gives `τ '' C_w = C_{w'}` for `w' = upperBruhatTransposeIndex (n + 1) w =
  Fin.revPerm * w⁻¹ * Fin.revPerm`. For instance, in rank three the transposition of the
  first two indices has `w'` the transposition of the last two, and distinct
  permutations have disjoint cells by the Bruhat decomposition (a standard fact that the
  proposition does not use).
- No support, factorization, orbital-integration, Haar, countability or descent
  hypothesis, and no auxiliary invariance hypothesis on `D`. Only the positive-character
  bi-equivariance is assumed.
- No continuity, boundedness or positivity of `D`.
- No global distribution on `GL_{n+1}`; `D` lives on the cell.
- No hypothesis on `ψ` beyond its type, which forces continuity and nontriviality.
- No restriction on `p`, `F`, `n` or `w` beyond the nonemptiness premise.

The complementary case, an empty compatible torus, is not covered here. There Shalika's
Proposition 1.13 forces the cell distribution to vanish; that is the separate statement
task `c1d1c15e-c4d7-4898-9c59-fa4f238d00fd` (`BruhatCellVanishingStatement`), which is
neither a premise nor a consequence of the present proposition.

## The case n = 0

For `n = 0` the published `compatibleTorus_rankOne` gives
`compatibleTorus ψ 0 w = Set.univ`, which is nonempty, and the published
`weylTransposeHomeomorph_rankOne` says that `τ` is the identity of `GL_1`. So in rank one
stability and invariance are immediate. The case is kept in the quantification, not
excluded.

## Relation to Shalika, Proposition 1.8

The registered original is `shalika-1974-multiplicity-one`: J. A. Shalika, *The
multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193. The copy
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`. Worker
1051 read the text of printed pp.174–178 (one-based PDF pages 5–9) and checked the
rendered images of printed pp.174, 175 and 178 (PDF pages 5, 6 and 9). Worker 634
earlier read printed pp.173–179 and visually checked pp.176–178. No source-specific
errata note for this paper exists in the project literature pointers or the Library
notes.

- **Printed p.174, the anti-automorphism θ.** For a nondegenerate character `χ` of `U`
  the source sets `χ₀(u) = χ(w₀ ᵗu w₀⁻¹)`, fixes `h₀ ∈ H` with `χ = χ₀^{h₀}`, where
  `χ^h(u) = χ(h⁻¹ u h)`, and defines `θ(x) = w₀ h₀ ᵗx h₀⁻¹ w₀⁻¹` for `x ∈ G`. The
  rendered page prints the transposed letter as `u` (`w₀h₀ᵗuh₀⁻¹w₀⁻¹`); since the
  variable is `x ∈ G`, this is read as `ᵗx`. θ is an anti-automorphism with properties
  (1.1)–(1.5); (1.3) `θ(U) = U`, (1.4) `χ(θ(u)) = χ(u)`, and (1.5): for `s ∈ N(H)`, if
  `χ(u) = χ(s u s⁻¹)` for all `u ∈ U_s = U ∩ s⁻¹ U s`, then `θ(s) = s`. Test functions
  are transformed by `f^θ(x) = f(x^θ)`, and the translations are
  `(L_x f)(y) = f(x⁻¹ y)`, `(R_x f)(y) = f(y x)`.

  For the standard character used here (all coefficients `1`), `w₀ = J` gives
  `χ₀ = χ`: the superdiagonal entry `(i, i + 1)` of `J ᵗu J` is the entry
  `(n − i − 1, n − i)` of `u` (zero-based), so the superdiagonal sum is unchanged. Hence
  `h₀ = 1` is an admissible choice, and θ becomes `g ↦ J gᵀ J`, which is
  `weylTransposeHomeomorph` (`J⁻¹ = J` by `weylLong_mul_self`). The published
  `standardCharacter_weylTranspose` is (1.4) in this form. The source requires `w₀` only
  to satisfy (1.1); the project uses this specific `w₀ = J`.
- **Printed p.175, Proposition 1.8.** Let `k` be a local field and `T` a distribution
  on `G_w` such that `T(L_{u₁⁻¹} R_{u₂} f) = χ(u₁u₂) T(f)` for all `f ∈ C_c^∞(G_w)`,
  `u₁, u₂ ∈ U`; then `T(f^θ) = T(f)`. With the translations above, the translated test
  function is `g ↦ f(u₁ g u₂)` and `χ(u₁u₂) = χ(u₁)χ(u₂)`, which is
  `IsBiEquivariantBruhatCellDistribution`; the conclusion `T(f^θ) = T(f)` is
  `IsWeylTransposeInvariantBruhatCellDistribution`. The source's cells are
  `G_w = H U w U` (printed p.174) with `w` running over representatives of the Weyl
  group in `N(H)`; for `GL_{n+1}` this is the actual double coset `B p_w B`.
- **Printed p.178, proof of Proposition 1.8.** The proof writes
  `T(f_α) = T*(α) = τ(β_α)` for `α ∈ C_c^∞(M₁)` (from Lemma 1.10 and Proposition 1.12,
  printed pp.176–177), recalls that `τ` has support in `H_χ` (Proposition 1.13), and
  continues: "Suppose then that `H_χ` is non-empty. It follows that `w⁻¹θ(wh) ∈ H` for
  all `h ∈ H`. We also have `θ(U_w⁺) = U_w⁺`." It defines
  `α^θ(u₁, h, u₂) = α(θ(u₂), w⁻¹θ(wh), θ(u₁))`, derives `f_{α^θ} = f_α^θ` from (1.11),
  uses (1.3)–(1.5) to show that `β_{α^θ}` and `β_α` agree on `H_χ`, uses that `τ` is the
  extension of a distribution on `H_χ` (the remark after Lemma 1.15, same page) to get
  `τ(β_{α^θ}) = τ(β_α)`, and concludes by surjectivity of `α ↦ f_α`.

**What is derived, not transcribed.** Proposition 1.8 is stated for every `w`, but
`f^θ` is a test function on `G_w` only when θ maps `G_w` into itself, and the proof
treats only the case of nonempty `H_χ`, where `w⁻¹θ(wh) ∈ H` gives this stability. When
`H_χ` is empty, Proposition 1.13 gives `τ = 0` and hence `T = 0`. The present
proposition is the internal derived interface for the nonempty case:

- the premise is nonemptiness of the published `compatibleTorus ψ n w`, the Lean
  counterpart of `H_χ`, realized as a set of parameters `d` with
  `h = diagonalUnits d` and `w` realized as `p_w`;
- cell stability, implicit in the source, is an explicit first conclusion, and the
  invariance is stated for the restriction of `τ` to the cell subtype through that
  proof;
- `χ` is the standard character `standardCharacter ψ n`, and θ is the specific
  involution `g ↦ J gᵀ J` (the choice `h₀ = 1`, `w₀ = J` above);
- the full algebraic dual replaces the source's distributions;
- the field is restricted to p-adic fields; the source allows any local field.

## Intended later proof (not established here)

The following outlines how the proposition is expected to be proved, in a separate
proof task. None of it is established by this module, and no theorem is claimed. The
later proof may take a different route.

1. **Cell stability.** Pick `d` in the compatible torus. The published
   `Langlands.Whittaker.compatibleMonomialFixed` proves
   `CompatibleMonomialFixedStatement` (Shalika's (1.5) for monomial matrices), and the
   published `weylTransposeHomeomorph_monomial_eq_of_compatible` gives
   `τ (p_w * h(d)) = p_w * h(d)` with `h(d) = diagonalUnits d`. Since `τ` reverses
   products, maps upper triangular matrices to upper triangular matrices and maps
   diagonal matrices to diagonal matrices, `τ p_w = τ(h(d))⁻¹ * p_w * h(d)`, and
   `τ (b₁ p_w b₂) = τ b₂ * τ p_w * τ b₁` lies in `B p_w B`. This gives `hτ`. The same
   identity shows that `p_w⁻¹ τ(p_w h(d'))` is diagonal for every `d'`, Shalika's
   `w⁻¹θ(wh) ∈ H`.
2. **Factorization.** The published `Langlands.Whittaker.bruhatHaarMeasure` (statement
   `BruhatHaarMeasureStatement`) supplies Haar measures `μ` on `U` and `ν` on `U_w⁺`
   with the required invariances, and the published
   `Langlands.Whittaker.bruhatOrbitalIntegration` (statement
   `BruhatOrbitalIntegrationStatement`) a surjective linear `I` from test functions on
   `U × (H × U)` to test functions on the cell satisfying Shalika's formula (1.11). The
   published statement `BruhatCellFactorizationStatement`, once proved, gives a torus
   distribution `τ_H` supported on `compatibleTorus ψ n w` with `τ_H(β_α) = D (I α)`,
   where `β_α` is the published character average with weight the inverse of both
   character values.
3. **Exchange in the character average.** For the test function
   `α♯(u₁, (d', u₂)) = α(τ u₂, (d', τ u₁))`, which exchanges the two unipotent variables
   and transposes each, `β_{α♯} = β_α`: `BruhatHaarMeasureStatement` gives invariance of
   every Haar measure on `U` under `weylTransposeUnipotent`, and
   `standardCharacter_weylTranspose` gives invariance of the character. Hence
   `D (I α♯) = D (I α)`. Shalika's `α^θ` uses `w⁻¹θ(wh)` in the middle variable, which
   equals `h` on `H_χ` by (1.5); with that choice the two averages agree on `H_χ`, and
   the source passes through the extension of `τ` from `H_χ` (whose Lean counterpart
   is the published `Distribution.closedSupportedDescent`, statement
   `ClosedSupportedDescentStatement`), or, with the published `supportedOn`
   convention, directly through the support of `τ_H`.
4. **Exchange in the orbital integral.** At a cell point `π(u₁, d', u₂)` with `d'` in
   the compatible torus, `s = p_w h(d')` is fixed by `τ`, and the substitution
   `v ↦ s⁻¹ τ(v)⁻¹ s` is an involutive automorphism of `U_w⁺`. If it preserves `ν`,
   the defining integrals show that `I α♯` and
   `pullback (bruhatCellWeylTranspose n F.Carrier w hτ) (I α)` agree at that point.
   This measure transport must be proved in the later proof; it is not assumed here.
   At points over the complement of the compatible torus the corresponding substitution
   involves an extra conjugation by a diagonal matrix, which can rescale Haar measure,
   so the later proof should compare the two functions only where it needs them.
5. **Conclusion.** A support argument, from the factorization, the support of `τ_H` and
   a lift through `I` that vanishes at the product points over the compatible torus
   whenever the lifted cell function vanishes at their images, shows that `D` kills
   every cell test function vanishing at every cell point over the compatible torus.
   Applied to `I α♯ − pullback (bruhatCellWeylTranspose n F.Carrier w hτ) (I α)`, with
   steps 3 and 4 this gives
   `D (pullback (bruhatCellWeylTranspose n F.Carrier w hτ) (I α)) = D (I α)` for every
   `α`, and surjectivity of `I` gives invariance on every cell test function.

Only finite linearity of the algebraic dual is available; no distribution is commuted
with an infinite integral. These steps are motivated by printed p.178 and are not
verbatim source statements.

## Scope

This is a statement only. It proves no cell stability and no invariance assertion. It
also states and proves nothing about: the empty compatible-torus case or vanishing of
cell distributions, factorization or support of cell distributions, orbital integrals,
Haar measures, Shalika's Propositions 1.8, 1.12 or 1.13 as stated in the source, global
distribution invariance (Shalika's Theorem 1.6), or multiplicity one.

## Provenance

The Lean text is Worker 634's private type-checked design, reproduced exactly from the
task objective, placed in its final namespace and module by Worker 1051 and checked here
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (diagnostics
`5654178d-65af-494e-9d8c-02f24c678b4a` and, for the final pair,
`5e0f5995-2c29-49d0-85a1-8506fdb59a66`: no errors or warnings, statement returns
`Prop`, axioms `propext`, `Classical.choice` and `Quot.sound`). The formulation is internal
derived content, as explained above; its sources are Shalika (1974), the
anti-automorphism θ and properties (1.1)–(1.5) (printed p.174), Proposition 1.8
(printed p.175) and its proof (printed p.178).

## Consumers

The proposition is an intermediate target for the exact Shalika distribution-invariance
work (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, Worker 634) and, through it, the
Whittaker multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`, Worker 16).
A separate proof task follows publication of this statement.
