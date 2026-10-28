# Surjectivity of character-weighted product averaging

This module states, as a proposition, that the published character average
`Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverage` is surjective.
It does not prove this. The module also proves two auxiliary theorems. They show
that the proposition applies to the published upper-unipotent average
`Langlands.HarmonicAnalysis.standardCharacterAverage` for every Haar measure.
All declarations below are in the namespace
`Langlands.HarmonicAnalysis.SchwartzBruhat`.

The module imports the published
`Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, which defines the
map. It also imports `Langlands.Group.GL.CompactOpen` and
`Langlands.Group.GL.CountabilityProof` for the canonical p-adic topology facts
used in the specialization. No imported published pair is changed.

## The proposition

`CharacterAverageSurjectiveStatement.{uG, uY} : Prop` is the following assertion.

For all types `G : Type uG` and `Y : Type uY`, the universes `uG` and `uY`
being arbitrary and independent, assume:

- `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`: `G` is a topological
  group;
- `[T2Space G]`: `G` is Hausdorff;
- `[LocallyCompactSpace G]`: `G` is locally compact;
- `[NonarchimedeanGroup G]`: every neighbourhood of the identity contains an
  open subgroup;
- `[MeasurableSpace G] [BorelSpace G]`: the σ-algebra on `G` is the Borel
  σ-algebra of its topology;
- `[TopologicalSpace Y]`: `Y` is a topological space.

Then for every continuous character `χ : ContinuousMonoidHom G ℂˣ` and every
measure `μ : Measure G` with `[μ.IsHaarMeasure] [SFinite μ]`,

    Function.Surjective (characterAverage (Y := Y) χ μ).

Here `characterAverage χ μ` is the published complex-linear map

    SchwartzBruhat (G × (Y × G)) →ₗ[ℂ] SchwartzBruhat Y.

Both spaces are the published spaces of locally constant, compactly supported
complex functions. No replacement space or new average is introduced.

### Parenthesization and formula

The triple product is the right-associated product `G × (Y × G)`. A point is
`(g₁, (y, g₂))`, and the integration variable `z : G × G` stands for
`(g₁, g₂) = (z.1, z.2)`. The published law `characterAverage_apply` gives, for
`α : SchwartzBruhat (G × (Y × G))` and `y : Y`,

    characterAverage χ μ α y =
      ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

The integral is Mathlib's Bochner integral over `G × G` for the product
measure `μ.prod μ`. The weight is the inverse of the product of BOTH outer
character values. Surjectivity therefore says: for every
`f : SchwartzBruhat Y` there is an `α : SchwartzBruhat (G × (Y × G))` such
that the displayed integral equals `f y` for every `y : Y`.

### Measure hypotheses

- `IsHaarMeasure μ` supplies the following: `μ` is finite on compact sets,
  invariant under left multiplication, and positive on nonempty open sets. The
  published map needs finiteness on compact sets, which is found from this
  instance.
- `SFinite μ` is a separate hypothesis. The published map requires it because
  Mathlib's `Measure.prod` is controlled only for an s-finite second factor (see
  `CharacterAverage.md`).
- No right invariance and no unimodularity of `μ` is assumed. The intended
  proof below uses only that `μ` is positive and finite on a compact open
  subgroup.

### What is not assumed

- About `Y`: no Hausdorff property, local compactness, total disconnectedness,
  countability or nonemptiness.
- About `G`: no second countability, σ-compactness, unimodularity or
  commutativity.
- About `χ`: no local constancy, unitarity or open kernel. These are not
  premises. Local constancy follows from continuity and the nonarchimedean
  hypothesis: the published `Langlands.isOpen_ker_of_continuous_complex_character`
  shows that the kernel of a continuous character `G →* ℂˣ` on a
  nonarchimedean group is open.

## Specialization to upper unipotents of `GL_(n+1)`

### s-finiteness of Haar measures

`upperUnipotent_sFinite_of_isHaarMeasure F n` is a proved theorem. Take a
prime `p` with `[Fact p.Prime]`, a canonical p-adic field
`F : PadicField.{uF} p` in an arbitrary universe, and `n : ℕ`. Use the topology
`F.canonicalTopologicalData.topology` and the Borel σ-algebra
`borel (upperUnipotent n F.Carrier)`. Then every Haar measure `μ` on the upper
unipotent subgroup `upperUnipotent n F.Carrier` is s-finite.

The Lean proof runs as follows.

1. The published
   `Langlands.PadicField.TopologicalData.generalLinearSecondCountableTopology` makes
   `GeneralLinear n F.Carrier` second countable.
2. The subgroup inherits second countability as a subspace
   (`TopologicalSpace.Subtype.secondCountableTopology`).
3. The published `Langlands.PadicField.canonicalUpperUnipotentLocallyCompactSpace`
   makes it locally compact.
4. `infer_instance` closes the goal through Mathlib instances. A locally compact,
   second countable space is σ-compact
   (`sigmaCompactSpace_of_locallyCompact_secondCountable`). A Haar measure on a
   σ-compact group is σ-finite (`IsHaarMeasure.sigmaFinite`, or equivalently
   `SigmaFinite.of_isFiniteMeasureOnCompacts`). A σ-finite measure is s-finite.

### The specialization theorem

`CharacterAverageSurjectiveStatement.surjective_standardCharacterAverage` is a
proved theorem. Its hypothesis is `h : CharacterAverageSurjectiveStatement.{uF, uF}`,
the proposition with both universes equal to the universe of `F`. Its data are:

- a prime `p` with `[Fact p.Prime]`;
- a canonical p-adic field `F : PadicField.{uF} p`, for every universe `uF`;
- every `n : ℕ`, including `n = 0`;
- every unitary additive character `ψ : UnitaryAdditiveCharacter F.Carrier`;
- every Haar measure `μ` on `upperUnipotent (n + 1) F.Carrier` for its Borel
  σ-algebra.

Its conclusion is `Function.Surjective (standardCharacterAverage F n ψ μ)`. The
`SFinite μ` instance needed by `standardCharacterAverage` is supplied inside the
statement by `upperUnipotent_sFinite_of_isHaarMeasure F (n + 1) μ`. It is not an
added premise. The finiteness on compact sets comes from `IsHaarMeasure`.

The proof applies `h` with:

- `G = upperUnipotent (n + 1) F.Carrier`, the actual upper unipotent subgroup
  of `GL_(n+1)(F)`;
- `Y = Fin (n + 1) → F.Carrierˣ`, the parameter space of the diagonal subgroup;
- `χ = standardCharacterContinuous ψ n`.

The instances needed by `h` are the published canonical ones in the namespace
`Langlands.PadicField`: `canonicalUpperUnipotentTopologicalGroup`,
`canonicalUpperUnipotentT2Space`, `canonicalUpperUnipotentLocallyCompactSpace`
and `canonicalUpperUnipotentNonarchimedean`. `BorelSpace` holds by `rfl`. The
published `standardCharacterAverage F n ψ μ` is by definition
`characterAverage (standardCharacterContinuous ψ n) μ`, so `h` applies exactly.
No `T2Space` or other hypothesis on `Y` is required.

For `n = 0`, the group is `upperUnipotent 1 F.Carrier`, the upper unipotent
subgroup of `GL_1`; mathematically it contains only the identity. The standard
character is then trivial: the published `standardCharacter_apply` evaluates it
through an empty sum. The specialization theorem covers this case like every
other `n`; no separate lemma about `n = 0` is stated.

The eventual Shalika target can therefore use this proposition for every Haar
measure, with no `SFinite` hypothesis of its own.

## Intended proof (not formalized here)

The following argument is a plan for the separate proof task. Nothing in this
module proves it.

1. **A compact open subgroup in the kernel.** By
   `Langlands.isOpen_ker_of_continuous_complex_character`, `ker χ` is open. By
   local compactness, `1` has a compact neighbourhood `C`. The nonarchimedean
   hypothesis gives an open subgroup `K` contained in `ker χ` and in the
   interior of `C`. An open subgroup is closed, so `K` is compact.
2. **Normalization.** `0 < μ K < ∞`, by positivity on nonempty open sets and
   finiteness on compact sets. Let `φ = (μ K)⁻¹ · 1_K`. It is locally constant
   with compact support.
3. **The preimage.** For `f : SchwartzBruhat Y`, let
   `α (g₁, (y, g₂)) = φ g₁ * f y * φ g₂`. It is locally constant, with compact
   support contained in `K × (support f × K)`.
4. **Evaluation.** On `K × K` the weight `((χ g₁ : ℂ) * (χ g₂ : ℂ))⁻¹` equals
   `1`, and `(μ.prod μ) (K ×ˢ K) = μ K * μ K`. Hence
   `characterAverage χ μ α y = (μ K)⁻² · (μ K)² · f y = f y`.

This argument uses neither right invariance of `μ` nor any property of `Y`.

## Source correspondence and provenance

J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193, is the registered source
`shalika-1974-multiplicity-one`. The original PDF is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.

Printed p.177 (PDF page 8), Proposition 1.12, defines for `α ∈ C_c^∞(M₁)`,
`M₁ = U × H × U`,

    β_α(h) = ∫ α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂,

and asserts that the map `α ↦ β_α` onto `C_c^∞(H)` is surjective. The
correspondence is:

- `U`, `H` and Haar measure `du` are `G`, `Y` and `μ`;
- `(u₁, h, u₂)` is the point `(z.1, (y, z.2))` of `G × (Y × G)`;
- `du₁ du₂` is `μ.prod μ`;
- `χ̄(u₁u₂)` is `((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹`. For the source's unitary
  character the conjugate equals the inverse, and multiplicativity splits
  `χ(u₁u₂)` into both factors;
- `β_α` is `characterAverage χ μ α`.

In the specialization, Shalika's `n` is `n + 1`, his `χ` is the Library's
`standardCharacter ψ n` (all coefficients `aᵢ = 1`), and the diagonal subgroup
`H` is modelled by its parameter space `Fin (n + 1) → F.Carrierˣ`.

Provenance: the proposition is internal derived generality, not a verbatim
theorem of the paper. The paper has the specific groups `U` and `H` of `GL_n`
over a local field. Here `G` is any Hausdorff, locally compact, nonarchimedean
group, `Y` is any topological space, and `μ` is any s-finite Haar measure. The
statement covers only nonarchimedean `G`; Shalika's archimedean case, with
smooth rather than locally constant test functions, is not covered. The
s-finiteness hypothesis, the specialization theorems and the intended proof are
internal content authored by Worker 793.

## Limitations

This module proves no surjectivity. It also proves none of: translation
covariance of the average (a separate sibling statement), the factorization of
distributions through the average (the existence and uniqueness of `τ` in
Proposition 1.12), Bruhat cell descent, or Shalika invariance. None of these is
encoded as a field, premise or assumed theorem.
