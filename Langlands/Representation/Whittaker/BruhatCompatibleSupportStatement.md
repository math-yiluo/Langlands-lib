# Support on the compatible torus from invariance under Shalika's fiber action

Authors: Worker 885 and Worker 634. The Lean text of the proposition is Worker 634's
type-checked private design. Worker 885 placed it, otherwise unchanged, in the final
namespace `Langlands.Whittaker` and this module, and wrote this Markdown.

`Langlands.Whittaker.BruhatCompatibleSupportStatement.{uF}` is the following
proposition. This module defines the proposition and supplies no proof and no other
declaration. Its proof, `Langlands.Whittaker.bruhatCompatibleSupport`, whose type is
exactly this proposition at the same universe, is in the companion module
`Langlands.Representation.Whittaker.BruhatCompatibleSupportProof`. This module imports,
unchanged, the published modules
`Langlands.Representation.Whittaker.BruhatFiberAverage`,
`Langlands.HarmonicAnalysis.Distribution.CharacterAverage` and
`Langlands.HarmonicAnalysis.Distribution.Subspace`.

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
  occurs.
- `ψ : UnitaryAdditiveCharacter F.Carrier` is an arbitrary continuous, nontrivial
  unitary additive character. The published structure
  `Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter` bundles an additive character
  `F.Carrier → Circle` with the fields `continuous_toFun` (continuity) and
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
- `M = U × (H × U)`, the right-associated product, with the product topology.

It equips `U` with its Borel σ-algebra (`letI := borel U`) and records that this is a
Borel space (`letI : BorelSpace U := ⟨rfl⟩`). Then, further quantified:

- `μ : Measure U` is a Haar measure (`Measure.IsHaarMeasure μ`), s-finite (`SFinite μ`)
  and right invariant (`μ.IsMulRightInvariant`). Haar supplies left invariance and
  finiteness on compact sets; right invariance is a separate hypothesis.
- `τ : Distribution H` is an arbitrary algebraic distribution on `H` (see below).

**Hypothesis (fiber invariance).** For every `u : P` and every test function
`α : SchwartzBruhat M`,

    Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α)
      = Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ α.

**Conclusion.** `τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)`.

### The invariance equation written out

Write `χ = standardCharacterContinuous ψ n`, `h(d) = GeneralLinear.Iwasawa.diagonalUnits d`
for `d : H`, and `β_α = SchwartzBruhat.characterAverage χ μ α` for `α : SchwartzBruhat M`.
By the published evaluation laws:

- `characterAverageDual χ μ τ α = τ β_α` (`characterAverageDual_apply`), and

      β_α d = ∫ z : U × U, α (z.1, (d, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)

  (`characterAverage_apply`). The weight is the inverse of both character values; for
  the unitary character `χ` this is Shalika's `χ̄(u₁u₂)`.
- `pullback e α m = α (e m)` (`Hecke.TestFunction.pullback_apply`), with `e` itself, not
  its inverse.
- `bruhatFiberActHomeomorph (n + 1) F.Carrier w u` is the homeomorphism `M ≃ₜ M` whose
  forward map is `bruhatFiberAct (n + 1) F.Carrier w u`:

      bruhatFiberAct u (u₁, (d, u₂)) =
        (u₁ * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹, (d, u * u₂)),

  computed in `GeneralLinear (n + 1) F.Carrier`; the first entry lies in `U` by the
  published `bruhatFiberAct_fst_mem`, and `u * u₂` uses the inclusion `P ≤ U`. The diagonal
  matrix `h(d)` stands to the right of `p_w`, as in `π(u₁, d, u₂) = u₁ * p_w * h(d) * u₂`.

So the hypothesis says: for every `u ∈ P` and every `α`, `τ β_{α^u} = τ β_α`, where
`α^u (u₁, (d, u₂)) = α (u₁ * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹, (d, u * u₂))`, and

    β_{α^u} d = ∫ z : U × U,
        α (z.1 * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹, (d, u * z.2)) *
          ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

This is the only premise on `τ`.

### The support convention

`Distribution H` is the published `Module.Dual ℂ (SchwartzBruhat H)`: every complex
linear functional on the space of locally constant, compactly supported functions
`H → ℂ`. It is the full algebraic dual; no continuity, boundedness or positivity of `τ`
is required, and none is available.

`Distribution.supportedOn Z` is the published submodule whose carrier is

    {D | ∀ f : SchwartzBruhat H, (∀ z ∈ Z, f z = 0) → D f = 0}

(`mem_supportedOn_iff`). So the conclusion says: `τ f = 0` for every test function `f` on
`H` that vanishes at every point of `compatibleTorus ψ n w`. Since a test function is
locally constant with compact support, such an `f` has a compact open support disjoint
from the compatible torus. The compatible torus is closed (`isClosed_compatibleTorus`),
so the condition says that `τ` vanishes on the open complement of the torus, which is the
usual meaning of "the support of `τ` lies in the torus". This remark explains the
convention and is not stated in Lean.

### The compatible torus

`compatibleTorus ψ n w` is the published set of `d : H` for which `p_w * h(d)` is a
character-compatible representative: whenever `u, v ∈ U` satisfy
`(p_w * h(d)) * u * (p_w * h(d))⁻¹ = v`, the standard character takes the same value at
`u` and `v`. By the published `mem_compatibleTorus_iff_permutationUnipotentPlus` this is
Shalika's condition: `χ(p_w h(d) u h(d)⁻¹ p_w⁻¹) = χ(u)` for every `u ∈ U_w⁺`. The
standard character `standardCharacter ψ n` sends `g ∈ U` to `ψ` of the sum of the first
superdiagonal entries of `g`; `standardCharacterContinuous ψ n` is the same homomorphism
packaged as a continuous homomorphism `U → ℂˣ`.

## Exact meaning of the imported objects

- `Langlands.GeneralLinear`, `upperUnipotent`, `permutationUnipotentPlus`,
  `GeneralLinear.permutation` and `GeneralLinear.Iwasawa.diagonalUnits` are the published
  matrix group, subgroups, permutation matrices and diagonal map, reached through
  `Langlands.Group.GL.UpperBruhatCells`.
- `bruhatFiberAct` and `bruhatFiberActHomeomorph`, from
  `Langlands.Representation.Whittaker.BruhatFiberAverage`, are the published action of
  `P` on `M` and its fixed-`u` homeomorphisms, with inverse the map for `u⁻¹`.
- `compatibleTorus`, from `Langlands.Representation.Whittaker.CompatibleTorus`, is the
  published closed compatible locus.
- `SchwartzBruhat.characterAverage` and `Distribution.characterAverageDual`, from
  `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, are the published
  complex-linear weighted product average and its algebraic dual
  `D ↦ D ∘ characterAverage χ μ`. They require `[SFinite μ]`,
  `[IsFiniteMeasureOnCompacts μ]` and an opens-measurable structure on `U`; the last two
  come from the Haar hypothesis and the Borel structure.
- `Hecke.TestFunction.pullback`, from `Langlands.Representation.Hecke.TestFunction`, is
  the published complex-linear equivalence of test-function spaces attached to a
  homeomorphism.
- `Distribution` and `Distribution.supportedOn`, from
  `Langlands.HarmonicAnalysis.Distribution.Basic` and `.Subspace`, are as described
  above.

No replacement support notion, assumed vanishing conclusion, representation, abstract
stabilizer, quotient space or orbital-integration premise is introduced.

## Hypotheses that are deliberately absent

- No continuity, boundedness or positivity of `τ`.
- No countability hypothesis. `SFinite μ` is assumed; for actual p-adic Haar measures it
  is a dischargeable obligation, proved for every Haar measure on `U` by the published
  `upperUnipotent_sFinite_of_isHaarMeasure` in
  `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement` (for the
  topology `F.canonicalTopologicalData.topology`, which is by definition the topology of
  `F.canonicalNormedField`).
- Right invariance is assumed explicitly and is not inferred from the Haar property. For
  the published normalized measure `Langlands.RankinSelberg.unipotentHaar` it is the
  published instance `unipotentHaar_isMulRightInvariant`, a theorem about unipotent
  groups, not a consequence of left invariance.
- No hypothesis on `ψ` beyond its type. Continuity and nontriviality of `ψ` are not
  separate premises, but both are required by the type `UnitaryAdditiveCharacter`, so
  the proposition covers exactly the continuous nontrivial unitary characters, as in
  Shalika's setting.
- No restriction on `p`, `F`, `n` or `w`.

## The case n = 0

For `n = 0` the published `compatibleTorus_rankOne` gives
`compatibleTorus ψ 0 w = Set.univ`. A test function vanishing on all of `H` is zero, so
every `τ` lies in `supportedOn Set.univ` and the proposition holds trivially in rank one.
The case is kept in the quantification, not excluded.

## Relation to Shalika, Proposition 1.13

The registered original is `shalika-1974-multiplicity-one`: J. A. Shalika, *The
multiplicity one theorem for GL_n*, Ann. of Math. (2) **100** (1974), 171–193. The copy
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`. Printed
pp.176–177 (one-based PDF pages 7–8) were read and visually checked. No errata for these
pages are recorded in the project's literature pointers or notes.

- **Printed p.176.** `M₁ = U × H × U`, `π(u₁, h, u₂) = u₁ w h u₂`, and the action of
  `U_w⁺` on `M₁`: `u * m = (u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂)`, used in formula (1.11). This
  is the published `bruhatFiberAct`, with `w` realized as `p_w` and `h` as `h(d)`.
- **Printed p.177, Proposition 1.12.** For `T*` on `M₁` with
  `T*(L_{u₁⁻¹} R_{u₂} α) = χ(u₁u₂) T*(α)`, Shalika defines
  `β_α(h) = ∫_{U×U} α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂`, asserts that `α ↦ β_α` is surjective
  and that `T*(α) = τ(β_α)` for a unique distribution `τ` on `H`. The published
  `characterAverage χ μ α` is `β_α`.
- **Printed p.177, definition of `H_χ`.** `H_χ` is the set of `h ∈ H` with
  `χ(whuh⁻¹w⁻¹) = χ(u)` for all `u ∈ U_w⁺`. This is `compatibleTorus ψ n w`.
- **Printed p.177, Proposition 1.13.** "τ has support in `H_χ`", for the `τ` attached by
  Proposition 1.12 to `T*(α) = T(f_α)`, where `T` is a distribution on the cell as in
  Proposition 1.8. The proof starts from `τ(β_α) = T(f_α) = T(f_{α^u}) = τ(β_{α^u})` for
  `u ∈ U_w⁺`, where `α^u(m) = α(u * m)`.

**What is derived, not transcribed.** The paper states Proposition 1.13 only for the
`τ` produced from a cell distribution `T` through Lemma 1.10, formula (1.11) and
Proposition 1.12. Its proof uses about `τ` only the identity `τ(β_{α^u}) = τ(β_α)`. The
present proposition takes exactly this identity as its hypothesis, for an arbitrary
algebraic distribution `τ`, and drops the cell, `T`, `f_α` and the factorization
`T* = τ ∘ β`. It is therefore an internal derived formulation. The source statement over
p-adic fields would follow from it once that identity is established for the source's
`τ`; this is not done here. Further internal choices are the realization of `H` as `Fin (n + 1) → F.Carrierˣ`
through `h(d)`, the use of the full algebraic dual, the `supportedOn` convention above in
place of the source's `Supp τ`, an arbitrary s-finite right-invariant Haar measure `μ` on
`U` in place of the source's fixed Haar measure, and the restriction to p-adic fields
(the source allows any local field `k`).

In the source proof, `f_{α^u}` and `β_{α^u}` are the objects attached to `α^u`. The proof
contains one misprint, which affects only its reading: the map "β ↦ (γ − 1)β" must be
read as `β ↦ (δ − 1)β`, with the `δ` defined two lines earlier; no `γ` is defined
there.

## Intended proof (now proved in the companion module)

The following outline was written with the statement, before the proof existed. The
implemented proof `bruhatCompatibleSupport` follows this route; its own Markdown,
`BruhatCompatibleSupportProof.md`, describes the argument as implemented. It takes
step 1 from the published `Langlands.Whittaker.bruhatFiberCharacterCovariance`, which
proves `BruhatFiberCharacterCovarianceStatement`. That theorem gives
`β_{α^u} d = (compatibilityDefect ψ n w u d)⁻¹ · β_α d`, with `u ∈ P` viewed in `U`.
This agrees with the formula of step 1 below: for `u ∈ P`, `compatibilityDefect_eq_div`
and multiplicativity of `χ` give
`compatibilityDefect ψ n w u⁻¹ d = (compatibilityDefect ψ n w u d)⁻¹`. This identity is
an explanatory remark and is not stated in Lean. The implemented proof carries out steps 3 and 4 on clopen level
sets of the defect and glues them by an induction over a finite clopen cover.

1. **Inverse-defect covariance.** For `u ∈ P` and `d ∈ H`, write `s = p_w * h(d)` and
   `y = s * u⁻¹ * s⁻¹ ∈ U`. In the integral for `β_{α^u} d`, substitute `z.1 ↦ z.1 * y⁻¹`
   (right invariance of `μ`) and `z.2 ↦ u⁻¹ * z.2` (left invariance). Multiplicativity
   of `χ` turns the inverse weight into `χ(y) χ(u) ((χ z.1)(χ z.2))⁻¹`, so

       β_{α^u} d = χ(s u⁻¹ s⁻¹) χ(u) · β_α d = compatibilityDefect ψ n w u⁻¹ d · β_α d,

   where `u⁻¹` is viewed in `U`. Indeed the published `compatibilityDefect ψ n w v d` is
   `χ(s v s⁻¹) / χ(v)` for `v ∈ U` with `p_w v p_w⁻¹ ∈ U` (`compatibilityDefect_eq_div`),
   and `χ(u⁻¹)⁻¹ = χ(u)`. Shalika's `δ(h) = χ(whu⁻¹h⁻¹w⁻¹) χ(u)` is this defect at
   `u⁻¹`. The product-measure change of variables uses `SFinite μ`.
2. **Surjectivity.** With `δ_u = compatibilityDefect ψ n w u⁻¹`, the hypothesis becomes
   `τ((δ_u − 1) · β_α) = 0` for every `α`. By surjectivity of `α ↦ β_α`, this gives
   `τ((δ_u − 1) · g) = 0` for every test function `g` on `H` and every `u ∈ P`.
   Surjectivity is the published generic proposition
   `Langlands.HarmonicAnalysis.SchwartzBruhat.CharacterAverageSurjectiveStatement`,
   applied to `G = U` and `Y = H`. It is proved by the published
   `Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageSurjective` in
   `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof`. The
   published `CharacterAverageSurjectiveStatement.surjective_standardCharacterAverage`
   specializes it to `standardCharacterAverage F n ψ μ`, which is `characterAverage χ μ`
   on this `U` and `H`, for every Haar measure `μ`.
3. **Local constancy of a nontrivial defect.** If `d₀ ∉ compatibleTorus ψ n w`, the
   published `mem_compatibleTorus_iff_defect` and the fact that `P` is closed under
   inverses give `u ∈ P` with `δ_u d₀ ≠ 1`. The defect is `ψ` of a continuous function of
   `d` times a constant; a continuous unitary character of the p-adic field is locally
   constant, so `δ_u` is constant on a compact open neighbourhood `V` of `d₀`.
4. **Finite compact-support partition.** Let `f` vanish on the compatible torus. Its
   support is compact, open and disjoint from the torus. Cover it by finitely many
   compact open sets `V` as in step 3 and refine the cover to a finite disjoint family of
   compact open sets `V₁, …, V_k`, each with some `u_i ∈ P` and constant
   `c_i = δ_{u_i}|_{V_i} ≠ 1`. Then `f = Σ_i 1_{V_i} f` and
   `1_{V_i} f = (δ_{u_i} − 1) · ((c_i − 1)⁻¹ 1_{V_i} f)`, a product with a test function.
   By step 2 each `τ(1_{V_i} f)` vanishes, and linearity of `τ` over the finite sum gives
   `τ f = 0`.

Only finite linear combinations are fed to `τ`. The algebraic distribution is never
interchanged with an integral, and no continuity of `τ` is used.

## Scope

This module is a statement only. It proves no support assertion; the support
assertion is proved by `bruhatCompatibleSupport` in the companion module. The covariance
law of step 1 and surjectivity of the average are not stated or proved here; they are
proved by the published `bruhatFiberCharacterCovariance` and
`characterAverageSurjective`, cited above. This module also states and proves nothing
about factorization of a bi-equivariant distribution through the average, closed restriction or
supported descent, cellwise or global invariance of distributions, Shalika's Propositions
1.8, 1.12 or 1.13 as stated in the source, or multiplicity one.

## Provenance

The Lean text is Worker 634's private type-checked design (diagnostic
`ce1c51d9-fc93-4a8d-8d30-fec306813ac4`), placed in its final namespace and module by
Worker 885 and checked here in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The
formulation with explicit fiber invariance and the algebraic dual is internal derived
content, as explained above; the source is Shalika (1974), printed p.176 and
Proposition 1.13 on printed p.177.

## Consumers

The proposition is an intermediate target for the exact Shalika distribution-invariance
work (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, Worker 634) and, through it, the
Whittaker multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`, Worker 16).
Its proof is `Langlands.Whittaker.bruhatCompatibleSupport` in
`Langlands.Representation.Whittaker.BruhatCompatibleSupportProof`.
