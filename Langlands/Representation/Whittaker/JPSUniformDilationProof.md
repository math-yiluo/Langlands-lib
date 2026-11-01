# Uniform small-coordinate dilation for actual JPS function spaces (proof)

Author: Worker 941. This unit proves the published proposition
`Langlands.Whittaker.JPSUniformDilationStatement.{uF}` (module
`Langlands.Representation.Whittaker.JPSUniformDilationStatement`, statement
artifact `8461c160-2445-4e4c-83a8-dafc1e1f1300`). The statement is the
small-coordinate dilation step in the proof of JPS (1979), Lemma (2.2.1),
printed p.182. The statement pair and everything it imports are unchanged.

## Declarations

The closing theorem is
`Langlands.Whittaker.jpsUniformDilation : JPSUniformDilationStatement.{uF}`.
It proves the whole closed target, unapplied and with all its quantifiers. Its
proof is
`jpsUniformDilation_of_unitInvariance_of_recurrence jpsCoordinateUnitInvariance
jpsBoundedDilationRecurrence`, with two published theorems:

- `Langlands.Whittaker.jpsCoordinateUnitInvariance` proves
  `JPSCoordinateUnitInvarianceStatement.{uF}`, in module
  `Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceProof`
  (artifact `a313ec54-80de-4856-b8fc-a604418de77b`, proof task
  `97e96190-2043-4279-bd83-d5b3ec8911b4`, Library commit
  `6789e5106aba61566887427750f5444a494d5879`).
- `Langlands.Whittaker.jpsBoundedDilationRecurrence` proves
  `JPSBoundedDilationRecurrenceStatement.{uF}`, the uniform-region recurrence for
  powers of a bounded coordinate dilation, in module
  `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof`
  (statement artifact `fe9dd1eb-3328-4d44-a518-477bb975447d`, statement task
  `48bd2fbc-532c-4b84-b411-a180058a1107`; proof artifact
  `f93626e1-1239-43d1-ae2a-5cf84e39c67b`, proof task
  `9c6a43b4-5ac4-4220-9372-304a353e06a5`, Library commit
  `9a8ca758097242bde4147f33304f43fceef22fa4`).

This unit imports both and reproves neither.

The new auxiliary declarations are in the namespace
`Langlands.Whittaker.JPSUniformDilationProof` and have the unrestricted field universe
`uF` as their only universe parameter, as does the closing theorem. The finite-minimum
lemma `exists_common_threshold`, the submodule `smallVanishing`, its membership,
antitonicity and germ-kernel helpers, and `exists_threshold_of_finiteDimensional` are
reused from `Langlands.Whittaker.JPSBoundedDilationRecurrenceProof`. The generic
finite-minimum lemma has no field parameter and allows an arbitrary index universe.

- `jpsUniformDilation_of_unitInvariance_of_recurrence
  (hU : JPSCoordinateUnitInvarianceStatement.{uF})
  (hrec : JPSBoundedDilationRecurrenceStatement.{uF}) :
  JPSUniformDilationStatement.{uF}`. It derives the whole target from the two
  propositions.
- `uniformDilation_of_unitSubgroup` proves the four clauses of the target for
  one `T`, `n`, `W` and `i`. Its inputs are `HasFiniteCoordinateOperatorSpan W T i`,
  the data of uniform coordinate-unit invariance for that `W` and `i`, and the
  data of the recurrence for the uniformizer on that `W` and `i`:
  - a subgroup `U ≤ F.Carrierˣ` that is open for the units topology of
    `T.topology`, with `T.normalizedAbs (u : F.Carrier) = 1` and
    `sigma W T i u = id` for `u ∈ U`, and for each `f` one `ε > 0` such that
    `(coordinateRepresentation W i u f).val a = f.val a` for every `u ∈ U` and
    every torus tuple `a` with `T.normalizedAbs (a i : F.Carrier) < ε`.
    Compactness of `U` is not used.
  - one length `D : ℕ` and one coefficient family `d : ℕ → Fin D → ℂ`, and for
    each `f` one `δ > 0` such that for every `m : ℕ` and every torus tuple `a`
    with `T.normalizedAbs (a i : F.Carrier) < δ`,
    `(ρ(π^m) f)(a) = ∑_{j<D} d m j · (ρ(π^j) f)(a)`.

`jpsUniformDilation_of_unitInvariance_of_recurrence` introduces `p`, the
`Fact p.Prime` instance, `F`, `T`, `n`, `W`, `i`, the hypothesis
`IsLocallyConstantSpace W T` and the hypothesis
`HasFiniteCoordinateOperatorSpan W T i`. It applies `hU` to these same arguments,
and `hrec` to `p`, `F`, `T`, `n`, `W`, `i`, the finite-span hypothesis and the
bounded unit `c = π` (`normalizedAbs_uniformizerUnit_le_one`). It passes the
resulting data to `uniformDilation_of_unitSubgroup`. The two hypotheses of the
target are the only hypotheses used. Local constancy is used only through `hU`.
Rank zero is covered because `Fin 0` is empty.

## Notation and conventions

`|x|` is `T.normalizedAbs x`. `π` is `uniformizerUnit T`, the published
uniformizer of `T` as a unit, with `|π^m| = q^{-m}` for `m : ℤ`
(`uniformizerUnit_zpow_abs`), where `q = T.residueCardinality > 1`.
`ρ(b)` is `coordinateRepresentation W i b`, `σ(b)` is `sigma W T i b`, and
`[f]` is `germMap W T i f`. `𝒜` is the complex span of the range of `σ` in
`Module.End ℂ (CoordinateGerm W T i)`, finite-dimensional by hypothesis.
For `δ : ℝ`, `smallVanishing W T i δ` is the submodule of `f ∈ W` with
`f.val a = 0` for every tuple `a` with `|a_i| < δ`. By the published
`germMap_eq_zero_iff`, `[f] = 0` exactly when `f` lies in
`smallVanishing W T i δ` for some `δ > 0`.

## Absolute-value lemmas

- `normalizedAbs_uniformizerUnit_pow_le_one`: `|π^m| ≤ 1` for `m : ℕ`.
- `normalizedAbs_uniformizerUnit_le_one`: `|π| ≤ 1`, the hypothesis needed to
  apply the recurrence to `c = π`.
- `exists_uniformizerUnit_pow_mul_normOne`: if `|b| ≤ 1` then
  `b = π^m w` with `m = ord b ≥ 0` and `|w| = 1`.
- `exists_finset_unit_cover`: for an open subgroup `U`, finitely many units
  `r ∈ R` satisfy: every `w` with `|w| = 1` has some `r ∈ R` with
  `r⁻¹ w ∈ U`. The proof covers the compact set of norm-one units
  (`T.isCompact_normalizedAbs_eq_one_units`) by the open translates `r U`.

## Step 1: a basis of `𝒜` made of bounded dilations

`exists_bounded_operator_basis` produces a finite type `κ`, units `β k` with
`|β k| ≤ 1`, and coefficient functions `η k : F.Carrierˣ → ℂ` such that

- `σ(b) = ∑_k η_k(b) σ(β k)` for every unit `b`;
- `η` is injective as a map `κ → (F.Carrierˣ → ℂ)`;
- `η_k(b)` depends only on `σ(b)`;
- `η_k(b a) = ∑_l η_l(a) η_k(b β l)` for all `b`, `a`.

Proof. Let `V₊` be the span in `Module.End ℂ (CoordinateGerm W T i)` of the
`σ(b)` with `|b| ≤ 1`. The published `Langlands.boundedSpan_eq_span`
(module `Langlands.Representation.Smooth.FiniteOperatorExpansionProof`), applied
to the representation `σ` with the finite-dimensionality instance given by the
hypothesis, says `V₊ = 𝒜`. This is the source's remark that `𝒜` is spanned by
the `σ(a)` with `|a| ≤ 1`. So every `σ(b)` is in `V₊`, and lifting the spanning
argument into the subtype `𝒜` shows that the elements `σ(b)` of `𝒜` with
`|b| ≤ 1` span all of `𝒜`.

Mathlib's `exists_linearIndependent'` then selects a linearly independent
subfamily `σ(β k)` of these bounded generators with the same span, which is
all of `𝒜`. `Module.Basis.mk` turns it into a basis of `𝒜`, and `η_k(b)` is
the `k`-th coordinate of `σ(b)` in this basis. The basis is finite because
`𝒜` is finite-dimensional. Injectivity of `η` follows from
`η_k(β l) = δ_{kl}`. The last identity is the coordinate form of
`σ(ba) = σ(b) ∑_l η_l(a) σ(β l) = ∑_l η_l(a) σ(b β l)`.

## Step 2: the finite set `Y` and the operators `A`

In `uniformDilation_of_unitSubgroup`, `Y` is the image of `η` (a `Finset`),
and `A χ = ρ(β k)` when `χ = η k`, chosen with `Classical.choose`; `A χ = 0`
for `χ` outside the image. Injectivity of `η` gives `A (η k) = ρ(β k)` and
turns sums over `Y` into sums over `κ`.

- *Clause 2.* `A (η k) = ρ(β k)` with `|β k| ≤ 1`, so it is one of the
  spanning operators.
- *Clause 3.* By `sigma_apply_mk` and Step 1,
  `[ρ(b) f] = σ(b)[f] = ∑_k η_k(b) σ(β k)[f] = [∑_k η_k(b) ρ(β k) f]` for every
  unit `b`, with no restriction on `|b|`.
- *Clause 1, continuity.* For `u ∈ U`, `σ(u) = 1`, so `σ(bu) = σ(b)` and
  `η_k(bu) = η_k(b)`. Hence `η_k` is constant on each coset `xU`. These cosets
  are open (`xU` is the preimage of `U` under `y ↦ x⁻¹y`, continuous by
  `continuous_const_mul`), so `η_k` is locally constant
  (`IsLocallyConstant.iff_eventually_eq`) and therefore continuous for the
  units topology of `T.topology`.
- *Clause 1, finite translates.* By the last identity of Step 1, each
  translate `a ↦ η_k(b a)` equals `∑_l η_k(b β l) η_l`. All translates lie in
  the span of the finitely many `η_l`, which is finite-dimensional.

## Step 3: the uniformizer recurrence

The recurrence is the published `jpsBoundedDilationRecurrence`, applied once to
`c = π`, before `f` is fixed. It gives `D` and `d`, independent of `f`, and for
each `g ∈ W` a threshold `δ_g > 0` such that
`(ρ(π^m) g)(a) = ∑_{j<D} d m j · (ρ(π^j) g)(a)` for all `m : ℕ` and all tuples
`a` with `|a_i| < δ_g`. This unit does not reprove it.

## Step 4: one threshold for all `|b| ≤ 1` (clause 4)

Fix `f`. The threshold is `ε = min(ε₀, δ₁, δ₂)`, chosen before the tuple `a`
and before `b`.

- `ε₀` is the unit-invariance threshold of `f` for `U`.
- `R` is the finite set of representatives from `exists_finset_unit_cover`.
  For each `r ∈ R`, Step 3 applied to `g = ρ(r) f` gives a positive threshold
  for the recurrence, valid for every `m`. `δ₁` is their minimum, computed by
  `exists_common_threshold`, a finite-minimum lemma over a `Finset`.
- `L` is the span of the finitely many functions `ρ(π^j) ρ(r) f` (`r ∈ R`,
  `j < D`) and `ρ(β k) f` (`k ∈ κ`). It is finite-dimensional.
  `P = L ∩ coordinateVanishing W T i` is a finite-dimensional space of
  functions with zero germ. `exists_threshold_of_finiteDimensional` gives one
  `δ₂ > 0` with `P ⊆ smallVanishing W T i δ₂`. It takes a finite spanning set
  of `P`, the threshold of each spanning vector, and their minimum.

Now let `|a_i| < ε` and `|b| ≤ 1`. Write `b = π^m w` with `|w| = 1`, and pick
`r ∈ R` with `u = r⁻¹ w ∈ U`. Then `b = b₀ u` with `b₀ = π^m r` and
`|b₀| = |b| ≤ 1`.

1. `ρ(b) f (a) = f(a e_i(b₀) e_i(u)) = f(a e_i(b₀)) = ρ(b₀) f (a)`, by the
   threshold `ε₀`, because the `i`-th coordinate of `a e_i(b₀)` has absolute
   value `|a_i| |b₀| < ε₀`.
2. `η_k(b) = η_k(b₀)`, because `u ∈ U`.
3. Let `x = ρ(b₀) f = ρ(π^m) ρ(r) f`, `y = ∑_{j<D} d m j · ρ(π^j) ρ(r) f`
   and `z = ∑_k η_k(b₀) ρ(β k) f`. Both `y` and `z` lie in `L`. By Step 3 with
   `g = ρ(r) f` and threshold `δ₁`, `x - y` vanishes at every tuple `a'` with
   `|a'_i| < δ₁`, so `[x - y] = 0`. By clause 3, `[x - z] = 0`. Hence
   `[y - z] = [x - z] - [x - y] = 0`, and `y - z ∈ P`. So `(y - z)(a) = 0`
   (threshold `δ₂`), and `x(a) = y(a) = z(a)` (thresholds `δ₁` and `δ₂`).

Together, `ρ(b) f (a) = ∑_k η_k(b) (ρ(β k) f)(a) = ∑_{χ ∈ Y} χ(b) (A χ f)(a)`.
This proves clause 4. Coefficients are never matched pointwise: `δ₂` is the
common threshold of a finite-dimensional space of germ-zero functions.

## Topology and normalized absolute value

Only `T.topology` is installed on `F.Carrier`, with Mathlib's units topology
on `F.Carrierˣ`, exactly as in the statement. It is used for the openness of
`U`, the compactness of the norm-one units in `exists_finset_unit_cover`, and
the continuity of the `η_k`. All thresholds use `T.normalizedAbs`, with
multiplicativity `T.normalizedAbs_mul`, the formula
`T.normalizedAbs_of_ne_zero` (`|x| = q^{-ord x}` on units) and
`T.residueCardinality_gt_one`.

## Dependencies

- `Langlands.Representation.Whittaker.JPSUniformDilationStatement` (target)
  and `Langlands.Representation.Whittaker.JPSFunctionSpace`, through it:
  `coordinateRepresentation_apply`, `coordinateEmbedding_same`,
  `germMap_eq_zero_iff`, `sigma_apply_mk`, `coordinateVanishing`.
- `Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceProof`:
  the published theorem `jpsCoordinateUnitInvariance`, which proves
  `JPSCoordinateUnitInvarianceStatement.{uF}`, the first hypothesis of
  `jpsUniformDilation_of_unitInvariance_of_recurrence`. That proof uses the
  published generic results `Langlands.Topology.baireFiniteDimensionalGermConstancy`
  and `Langlands.Topology.compactGroupClosedSubgroupCover`. This unit uses
  neither of them directly.
- `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceProof`: the
  published theorem `jpsBoundedDilationRecurrence`, which proves
  `JPSBoundedDilationRecurrenceStatement.{uF}`, the second hypothesis.
- `Langlands.Representation.Smooth.FiniteOperatorExpansionProof`: the published
  `Langlands.boundedSpan_eq_span`, used in Step 1.
- `Langlands.LocalField.SmoothCharacterNormProof`:
  `PadicField.TopologicalData.isCompact_normalizedAbs_eq_one_units`, and
  through its imports `Langlands.LocalField.Uniformizer` (`uniformizerUnit`,
  `uniformizerUnit_zpow_abs`) and the normalization lemmas.
- Mathlib: finite-dimensional linear algebra (`exists_linearIndependent'`,
  `Module.Basis.mk`, `FiniteDimensional.span_of_finite`,
  `Submodule.fg_iff_finiteDimensional`) and local constancy
  (`IsLocallyConstant.iff_eventually_eq`).

lean_check `42bcff47-29d1-4257-a4f3-9b7fff3e69f6` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: 0 errors, 0 warnings; the closing
theorem has level parameter `uF` and axioms `propext`, `Classical.choice`,
`Quot.sound`.

## Source provenance

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
GL(3) I*, Ann. of Math. (2) 109 (1979), 169–212 (registered source
`jps-1979-gl3-i`), printed pp.181–182. The source applies its p.181 remarks on
smooth representations with a finite-dimensional operator algebra to `σ_n`,
then says that for a given `φ` one may find `c` so small that the expansion
holds for every `|b| ≤ 1` and all other coordinates. The implemented route is
internal and differs in detail. The regularity the source takes from
smoothness comes from the published unit-invariance proof. The uniform threshold
comes from the finite cover of the norm-one units modulo `U`, the published
uniformizer recurrence, and the common threshold of a finite-dimensional space.
