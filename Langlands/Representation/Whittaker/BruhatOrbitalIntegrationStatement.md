# Orbital integration onto test functions on an upper Bruhat cell

Authors: Worker 883 and Worker 634. Worker 634 wrote the exact Lean
proposition in the task objective, and it is used here verbatim. Worker 883
wrote the module and this Markdown.

This module states one proposition,
`Langlands.Whittaker.BruhatOrbitalIntegrationStatement.{uF} : Prop`. It does
not prove it, and it contains no other declaration. It imports only the
published `Langlands.Representation.Whittaker.BruhatFiberAverage`. That module
supplies the fiber action `bruhatFiberAct` and the raw fiber average
`bruhatFiberAverage`. Through its own imports it also supplies the groups, the
cell and the torus map of `Langlands.Group.GL.UpperBruhatCells`, the
test-function space `Langlands.HarmonicAnalysis.SchwartzBruhat`, the p-adic
fields and Mathlib's measure theory. No imported published pair is changed. No
new group, cell, test-function space, measure or quotient is defined.

## The proposition

The proposition quantifies over:

- every prime `p`, with `_hp : Fact p.Prime`;
- every p-adic field `F : PadicField.{uF} p`, that is, every finite extension
  of `Padic p`, with carrier `F.Carrier` in an arbitrary universe `uF`;
- every `n : ℕ`, including `n = 0`, so the rank `n + 1` is every positive rank;
- every permutation `w : Equiv.Perm (Fin (n + 1))`;
- every measure `μ : Measure P` with `[Measure.IsHaarMeasure μ]` and
  `[μ.IsMulRightInvariant]`, where `P` is given below.

It asserts that there is exactly one complex-linear map

    I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C

satisfying all three of the following clauses.

1. **Formula.** For every `α : SchwartzBruhat M` and every `m : M`,
   `I α (upperBruhatTorusMap (n + 1) w m) = bruhatFiberAverage (n + 1) F.Carrier w μ α m`.
2. **Surjectivity.** `Function.Surjective I`.
3. **Support.** For every `α : SchwartzBruhat M`,
   `tsupport (I α : C → ℂ) ⊆ upperBruhatTorusMap (n + 1) w '' tsupport (α : M → ℂ)`.

### The actual groups

All groups are subgroups of the published actual matrix group
`Langlands.GeneralLinear (n + 1) F.Carrier` of invertible matrices. The
published names are in `Langlands.GeneralLinear`.

- `U = upperUnipotent (n + 1) F.Carrier`: upper triangular matrices with unit
  diagonal.
- `P = permutationUnipotentPlus (n + 1) F.Carrier w`: by definition
  `U ∩ {g | p_w * g * p_w⁻¹ ∈ U}`, where
  `p_w = permutation (n + 1) F.Carrier w` is the published permutation matrix
  sending `e_j` to `e_(w j)`. This is Shalika's `U_w⁺ = U ∩ w⁻¹ U w`.
- `H = Fin (n + 1) → F.Carrierˣ`: the parameter space of the diagonal torus.
  The diagonal matrix with entries `d i` is
  `h(d) = Iwasawa.diagonalUnits d`.
- `M = U × (H × U)`: Lean's product is right-associated, so a point is
  `m = (u₁, (d, u₂))`, written `(u₁, d, u₂)`.
- `C = UpperBruhatCell (n + 1) F.Carrier w`: the subtype of the actual double
  coset `{g | ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * p_w * b₂}`, where `B` is the upper
  triangular subgroup. This is Shalika's cell `G_w = B w B`.

### Multiplication order and action

The published torus map is

    upperBruhatTorusMap (n + 1) w (u₁, d, u₂) = u₁ * p_w * h(d) * u₂,

with the diagonal factor `h(d)` to the RIGHT of `p_w`. It is written `π` below.
The published action of `u ∈ P` on `M` is

    bruhatFiberAct (n + 1) F.Carrier w u (u₁, d, u₂)
      = (u₁ * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹, d, u * u₂).

It is a left action. The published `upperBruhatTorusMap_bruhatFiberAct` says
that `π` is constant on its orbits.

### Topology

The statement installs `letI := F.canonicalNormedField`. This is the published
spectral-norm `NontriviallyNormedField` structure on `F.Carrier`. Its topology
is the canonical p-adic topology. The published
`Langlands.PadicField.canonicalTopologicalData_normTopology`, in the module
`Langlands.LocalField.CanonicalProof` (not imported here), proves
`F.canonicalTopologicalData.topology = F.canonicalNormedField.toUniformSpace.toTopologicalSpace`
by `rfl`. So this is the topology used by the published
`padic_bruhatFiberAverage`. The other topologies are the inherited ones.

- `Langlands.GeneralLinear (n + 1) F.Carrier` carries Mathlib's topology on
  the units of the matrix ring.
- `U`, `P` and `C` carry the subspace topology.
- `F.Carrierˣ` carries the units topology, `H` the product topology, and `M`
  the product topology.

The normed field supplies the instances `IsTopologicalRing F.Carrier` and
`T2Space F.Carrier` needed by `bruhatFiberAverage`. `SchwartzBruhat X` is the
published ℂ-submodule of `X → ℂ` of locally constant, compactly supported
functions. So `I` sends test functions on `M` to test functions on the cell
`C`.

### Measure hypotheses

`P` carries `letI := borel P`, the Borel σ-algebra of its subspace topology. No
σ-algebra on `M` or `C` is used.

- `Measure.IsHaarMeasure μ` is Mathlib's Haar class: `μ` is finite on compact
  sets, invariant under left multiplication, and positive on nonempty open
  sets. `bruhatFiberAverage` needs only `IsFiniteMeasureOnCompacts μ`, which
  is found from this instance.
- `μ.IsMulRightInvariant` is an explicit separate hypothesis: `μ` is invariant
  under every right multiplication `u ↦ u * g`. The intended proof needs it
  because the orbit of `v • m` is reparametrized by `u ↦ u * v`.
- No `SFinite`, σ-finiteness, regularity or normalization hypothesis is
  assumed. The raw average is a Bochner integral of a single continuous,
  compactly supported function on `P`, so it needs no product measure.

The proposition is about every such `μ`. It does not assert that such a
measure exists. A right-invariant Haar measure on the actual `P` is expected
to exist, because `P` is a unipotent group and hence unimodular. Providing one
is a separate later obligation and is not claimed here.

### The integral formula

The published `bruhatFiberAverage_apply` evaluates the right side of the
formula clause by definition:

    bruhatFiberAverage (n + 1) F.Carrier w μ α m
      = ∫ u, α (bruhatFiberAct (n + 1) F.Carrier w u m) ∂μ.

This is Mathlib's Bochner integral over `P`. The integrand is the restriction
of `α` to the `P`-orbit of `m`, with no character weight. So the formula
clause says

    I α (u₁ * p_w * h(d) * u₂) = ∫ u, α (u • (u₁, d, u₂)) ∂μ

for every `α` and every `(u₁, d, u₂)`. The left side is the value of the test
function `I α` on the cell at the point `π(u₁, d, u₂)`. The raw average is a
function on `M`. The statement asserts that it factors through `π` as a test
function on `C`; this is not assumed.

### Uniqueness

`∃! I, A I ∧ B I ∧ S I` says that one complex-linear map satisfies the whole
conjunction, and that every complex-linear map satisfying the whole
conjunction equals it. The intended proof gets uniqueness from the formula
clause alone. Every point of `C` has the form `π m` (see the proof plan), so
the formula fixes `I α` at every point of `C`. The Lean statement claims only
uniqueness among maps satisfying all three clauses.

### Surjectivity

`Function.Surjective I` says that every `f : SchwartzBruhat C` equals `I α` for
some `α : SchwartzBruhat M`. So every test function on the cell is an orbital
integral of a test function on the torus coordinates.

### Topological-support inclusion

For every `α`, the closed support `tsupport (I α)` in `C` lies in the image
under `π` of the closed support `tsupport α` in `M`. Both supports are Mathlib's
`tsupport`, the closure of the nonzero set. The image is not closed up again.

## Source correspondence and provenance

J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193, is the registered source
`shalika-1974-multiplicity-one`. The original PDF is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.176–177 (one-based PDF pages 7–8) were read and visually checked
by Worker 883. No source-specific erratum was found.

On printed p.176 Shalika puts `M₁ = U × H × U` and `M₂ = G_w`, and defines
`π(u₁, h, u₂) = u₁ w h u₂`. **Lemma 1.10**, for a local field `k`, says: given
`α ∈ C_c^∞(M₁)`, there is a unique `f_α ∈ C_c^∞(M₂)` with

    ∫_{U×H×U} F(u₁ w h u₂) α(u₁, h, u₂) du₁ dh du₂
      = ∫_{U×H×U_w⁻} F(u₁ w h u₂⁻) f_α(u₁ w h u₂⁻) du₁ dh du₂⁻

for all `F ∈ C_c^∞(M₂)`. Moreover `α ↦ f_α` is a continuous surjection, and
`Supp f_α ⊂ π(Supp α)`. Shalika then defines the action
`u * m = (u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂)` of `U_w⁺` on `M₁`, and derives from the
uniqueness in Lemma 1.10 the **formula (1.11)**

    f_α(π(m)) = ∫_{U_w⁺} α(u * m) du⁺.

Printed p.177 adds that `du⁺` is a fixed Haar measure on `U_w⁺`, and that the
`U_w⁺`-orbits on `M₁` are exactly the fibers of `π`.

The correspondence is:

- Shalika's `n` is `n + 1`, his `k` is a p-adic field `F.Carrier`, and his
  matrix `w` is `p_w`;
- `H` is modelled by its parameter space `Fin (n + 1) → F.Carrierˣ`, and `h`
  by `h(d)`;
- `M₁`, `M₂`, `π` and `u * m` are `M`, `C`, `upperBruhatTorusMap (n + 1) w`
  and `bruhatFiberAct (n + 1) F.Carrier w u m`;
- `du⁺` is `μ`, and `α ↦ f_α` is `I`;
- the formula clause is (1.11), the surjectivity clause is the surjectivity
  in Lemma 1.10, and the support clause matches `Supp f_α ⊂ π(Supp α)`.

The proposition is an internal formulation, not a verbatim statement of the
paper. The following parts are internal.

- **Universal Haar formulation.** The source fixes one Haar measure `du⁺`, and
  its `f_α` is tied to the invariant measures and differential forms chosen
  on p.176. The proposition quantifies over every left Haar measure on `P`
  that is also right invariant. This is a precise internal consequence of the
  one-measure version, intended for the later proof. On the locally compact
  group `P`, two left Haar measures differ by a scalar `c` with `0 < c < ∞`.
  Replacing `μ` by `c • μ` multiplies the raw average by the real number
  `c`. So the map `c • I` satisfies all three clauses for `c • μ`.
- **Support inclusion.** In this formulation the support clause is a precise
  internal consequence of the formula clause, intended for the later proof,
  not taken from Harish-Chandra's argument. If `I α (π m) ≠ 0`, the published
  `exists_bruhatFiberAct_mem_tsupport_of_mem_support` gives `u` with
  `u • m ∈ tsupport α`, and `π (u • m) = π m`. So the nonzero set of `I α`
  lies in `π '' tsupport α`. This set is compact, since `tsupport α` is
  compact and `π` is continuous, and hence closed in the Hausdorff space `C`.
  So it contains `tsupport (I α)`.
- **Characterization by (1.11).** The source defines `f_α` by the integral
  identity of Lemma 1.10 and derives (1.11). Here `I` is characterized directly
  by (1.11), with uniqueness among maps satisfying all three clauses.
- **What is left out.** The integral identity of Lemma 1.10 against every `F`
  is not formalized. Neither is continuity of `α ↦ f_α`, for which no topology
  on the test-function spaces is used. The archimedean case, with smooth
  rather than locally constant test functions, is not covered.

## Intended proof (not formalized here)

The following plan is for the separate proof task. Nothing in this module
proves it. It uses the trivialization of the fibers of `π` by coordinates.

1. **Geometry.** Use the published statements
   `Langlands.GeneralLinear.UpperUnipotentFactorizationStatement` and
   `Langlands.GeneralLinear.UpperBruhatCoordinatesStatement`, once their exact
   proofs are published (tasks `a8e4c0ca-ae06-4409-a11f-83ea76aefd10` and
   `fd59b42f-6374-40fa-91ea-0dd9de25ea17`). The first gives a homeomorphism
   `P × U_w⁻ ≃ₜ U`, `(u⁺, u⁻) ↦ u⁺ * u⁻`, where
   `U_w⁻ = permutationUnipotentMinus (n + 1) F.Carrier w`. The second gives a
   homeomorphism `U × (H × U_w⁻) ≃ₜ C`, `(u₁, d, v) ↦ u₁ * p_w * h(d) * v`. In
   particular `π` is surjective.
2. **Trivialized fibers.** Combine them into a homeomorphism `Φ : C × P ≃ₜ M`
   with `Φ (eT (u₁, d, v), u) = u • (u₁, d, v)`. Here `eT` is the second
   homeomorphism, and `v ∈ U_w⁻` is viewed in `U`. For the inverse, write
   `u₂ = u⁺ * u⁻` by step 1.
   Then `(u₁, d, u₂) = u⁺ • (u₁', d, u⁻)` with
   `u₁' = u₁ * p_w * h(d) * u⁺ * h(d)⁻¹ * p_w⁻¹`, which lies in `U` because
   `u⁺ ∈ P`. Under `Φ`, `π` becomes the projection to `C`, and the action of
   `v ∈ P` becomes left multiplication by `v` on the `P` factor.
3. **Existence.** Put `I α c = ∫ u, α (Φ (c, u)) ∂μ`. Since `α ∘ Φ` is locally
   constant with compact support on `C × P`, its support lies in finitely many
   products of compact open sets. So `I α` is locally constant with compact
   support, and `I` is complex linear. For `m = Φ (c, u₀)`, the composition law
   gives `u • m = Φ (c, u * u₀)`, and right invariance of `μ` gives the formula
   clause.
4. **Surjectivity.** `P` is a closed subgroup of `GL_(n+1)(F)`. It is locally
   compact and has a compact open subgroup `K`, and `0 < μ K < ∞`. Given
   `f : SchwartzBruhat C`, take `φ = (μ K)⁻¹ · 1_K` and
   `α = (f ⊗ φ) ∘ Φ⁻¹`. Then `∫ φ ∂μ = 1`, so `I α = f`.
5. **Uniqueness and support.** Uniqueness follows from surjectivity of `π`, as
   explained above. The support clause follows by the argument given under
   provenance.

## Limitations

This module proves nothing. It proves, and assumes as a premise, none of:
the geometry of the cell or of `U`, surjectivity of `π`, fiber transitivity,
descent of the raw average to the cell, local constancy or compact support of
any average, surjectivity of orbital integration, or the existence of a
right-invariant Haar measure on `P`. It also proves no Shalika distribution
invariance, cellwise or global. The proposition has no geometry, surjectivity,
descent, orbital-integration or invariance premise. It supplies an
intermediate analysis target for Worker 634's Shalika distribution invariance
task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, toward Worker 16's multiplicity
one task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`. It proves neither parent
theorem.
