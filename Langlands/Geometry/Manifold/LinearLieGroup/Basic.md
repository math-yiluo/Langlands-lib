# Linear Lie groups

`Langlands.Geometry.Manifold.LinearLieGroup.Basic`. A small theory of Lie subgroups of the units of
a finite-dimensional normed real algebra `𝔸`, with exponential charts. Namespace
`Langlands.LinearLieGroup`.

## The structure

`IsExpLieAlgebra G 𝔤`, for a subgroup `G : Subgroup 𝔸ˣ` and a subspace `𝔤 : Submodule ℝ 𝔸`, has two
fields:

- `expUnit_mem`: `exp X ∈ G` for every `X ∈ 𝔤`;
- `exists_nhds`: there is an open `U ∋ 0` inside the source of `expPartialHomeomorph 𝔸` such that
  `X ∈ U` and `exp X ∈ G` imply `X ∈ 𝔤`.

So `𝔤` is the Lie algebra of `G` and `exp` identifies a neighbourhood of `0` in `𝔤` with a
neighbourhood of `1` in `G`. The structure keeps `𝔤` as an argument, because `𝔤` is the model space
of the charts (one wants `𝔤 = ⊤`, or a subspace given by explicit equations, definitionally);
`ClosedSubgroup` shows that `𝔤` is determined by `G` and that every closed subgroup has the
structure.

## The manifold

From a choice of `U` (`nhd`) and its image `nhdOne` under `exp`:

- `chart g : OpenPartialHomeomorph G 𝔤` sends `x` to the projection to `𝔤` of `log (g⁻¹ x)`, for
  `g⁻¹ x ∈ nhdOne`; its inverse is `X ↦ g · exp X`. On its source the logarithm already lies in
  `𝔤` (`symm_mem_lie`), so the projection `subspaceProj 𝔤` only serves to land in the subtype.
- `chartedSpace : ChartedSpace 𝔤 G` has these charts. It is a definition marked
  `@[instance_reducible]`, **not an instance**: statements install it with
  `letI := h.chartedSpace`. On `⊤ : Subgroup 𝔸ˣ` it is a different charted space from Mathlib's
  instance on `𝔸ˣ` (single chart `Units.val`), and an instance would create a diamond.
- `isManifold`: the transition maps `X ↦ proj (log (c · exp X))` are smooth
  (`contDiffOn_proj_symm_mul_exp`), so `G` is a smooth manifold modelled on `𝔤`.
- `contMDiff_val`: the inclusion `G → 𝔸` is smooth (in the chart at `x` it is `X ↦ x · exp X`).
- `contMDiffAt_of_val`: a map `f : M → G` from any manifold is smooth at `x` when
  `y ↦ (f y : 𝔸)` is: the chart at `f x` is a smooth function of the ambient coordinate near
  `f x`.
- `lieGroup`: multiplication and inversion are smooth, by `contMDiffAt_of_val` and the smoothness
  of multiplication and `Ring.inverse` in `𝔸`.

## Tests of smoothness and the exponential map

- `expG : 𝔤 → G` is the exponential map; `expG 0 = 1`, `expG (-X) = (expG X)⁻¹`,
  `expG ((s + t) • X) = expG (s • X) * expG (t • X)`, and `expG` is smooth (`contMDiff_expG`).
- `contMDiffAt_iff_expG`: `f : G → E` is smooth at `g` if and only if `Y ↦ f (g · exp Y)` is smooth
  at `0`; `contMDiff_iff_expG`: `f` is smooth if and only if `Y ↦ f (g · exp Y)` is smooth on `𝔤`
  for every `g`.
- `prodExp X t = ∏ᵢ exp (tᵢ Xᵢ)` (ordered product): the coordinates of the second kind, studied in
  `ProductCoordinates`.

## Topology

- `IsExpLieAlgebra.isClosed`: `G` is closed in `𝔸ˣ`. For `x` in the closure, pick `g₀ ∈ G` with
  `g₀⁻¹ x` close to `1`; then `g₀⁻¹ x` is a limit of elements `u` of `G` near `1`, whose logarithms
  lie in the closed subspace `𝔤`, so `log (g₀⁻¹ x) ∈ 𝔤` and `g₀⁻¹ x = exp (log (g₀⁻¹ x)) ∈ G`.
- `locallyCompactSpace`: `G` is locally compact, as a manifold modelled on a finite-dimensional
  space.
- `secondCountableTopology_subgroup`: every subgroup of `𝔸ˣ` is second countable (it embeds in
  `𝔸`, `isEmbedding_coe_coe`).

## Literature

Linear Lie groups and exponential charts: B. C. Hall, *Lie groups, Lie algebras, and
representations*, 2nd edition (Springer GTM 222, 2015), chapter 3: Definition 3.18, p. 56 (the Lie
algebra of a matrix Lie group); Theorem 3.42, p. 68 (for some `ε`, `A ∈ exp(U_ε)` lies in `G` if and
only if `log A ∈ 𝔤`: the field `exists_nhds`); Corollaries 3.44 and 3.45, p. 70, with the charts
`A = A₀ e^X` in the proof on p. 71; and chapter 2, Theorem 2.8, p. 38 (the matrix logarithm). Hall
works with the closed subgroups of `GL(n; ℂ)` (Definition 1.4, p. 4) and defines `𝔤` from `G`; here
`G` is a subgroup of the units of a finite-dimensional normed real algebra and `𝔤` is given with the
two properties of `IsExpLieAlgebra`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`, from these parts of files under `src/`:

| Source | Lines | Content here |
|---|---|---|
| `GroundTheory/AutomorphicForms/RealGroupsLie.lean` | 187–381 | `subspaceProj`, `IsExpLieAlgebra`, `nhd`, `nhdOne`, `expG`, `chart`, `chartedSpace`, `isManifold`, `contMDiff_val`, `contMDiffAt_of_val`, `lieGroup` |
| `GroundTheory/AutomorphicForms/DixmierMalliavinBasic.lean` | 18–53 | `expG_add_smul`, `prodExp`, `chart_self`, `contMDiffAt_iff_expG`, `locallyCompactSpace` |
| `GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean` | 84–90, 95–121 | `expG_zero`, `expG_neg`, `contMDiff_expG`, `contMDiff_expG_comp`, `contMDiff_iff_expG` |
| `GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean` | 194–201 | `isEmbedding_coe_coe`, `secondCountableTopology_subgroup` |
| `GroundTheory/AutomorphicForms/GKModules/Garding.lean` | 16–19 | the same second countability, stated for every subgroup |
| `GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean` | 111–144 | `IsExpLieAlgebra.isClosed` |

The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- The pieces are merged into one module in the namespace `Langlands.LinearLieGroup` (source:
  `GroundTheory.Automorphic`).
- The exponential lemmas lose their field argument (`expUnit 𝔸`, `expPartialHomeomorph 𝔸`,
  `contDiff_exp 𝔸`; see `Exponential`).
- `isEmbedding_coe_coe` and the second countability are stated for every subgroup of `𝔸ˣ`, outside
  the namespace `IsExpLieAlgebra` (the source has `IsExpLieAlgebra.secondCountableTopology`, with an
  unused hypothesis, and `secondCountableTopology_subgroup_units`); the latter is renamed
  `secondCountableTopology_subgroup`.
- The file option `linter.unusedSectionVars false` is removed; section variables a declaration does
  not use (mostly `[FiniteDimensional ℝ 𝔸]`) are left out with `omit … in`.
- In tactic proofs `letI`/`haveI` of a charted space or a Lie group instance are written `let`/`have`
  (Mathlib style linter); in statements `letI := h.chartedSpace` is kept.
- `import Mathlib` is replaced by the modules the file uses.
- A module docstring and a docstring for every declaration and field are added.
- Statements and proofs are otherwise unchanged.
