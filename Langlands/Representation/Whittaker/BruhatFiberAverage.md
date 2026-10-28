# Shalika's fiber action on torus coordinates and the raw fiber integral

Author: Worker 724.

This pair constructs Shalika's action of `U_w⁺` on the torus-coordinate space of an upper
Bruhat cell, proves its elementary algebraic and topological laws, and constructs the
unweighted orbit integral of a test function as a complex linear map into complex
functions. All declarations are in `Langlands.Whittaker`. The pair imports without
modification the published actual matrix group `Langlands.GeneralLinear r K`, the
subgroups `upperUnipotent r K` and `permutationUnipotentPlus r K w`, the permutation
matrices `GeneralLinear.permutation r K w`, the diagonal map
`GeneralLinear.Iwasawa.diagonalUnits`, the multiplication map `upperBruhatTorusMap r w`
into `UpperBruhatCell r K w`, the test-function space `SchwartzBruhat`, and Mathlib's
Bochner integral. It defines no new group, cell, permutation, test-function space,
measure or quotient space.

## Source

The registered original is `shalika-1974-multiplicity-one`: J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193. The
copy at `/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed p.176 (one-based PDF page 7) was read. There `M₁ = U × H × U`, `M₂ = G_w` is
the Bruhat cell, and `π : M₁ → M₂`, `π(u₁, h, u₂) = u₁ w h u₂`, is the multiplication
map onto the cell. For a local field `k` and `α ∈ C_c^∞(M₁)`, Lemma 1.10 gives a unique
function `f_α ∈ C_c^∞(M₂)` on the cell, characterized by an integral identity. After
Lemma 1.10 the paper defines an action of `U_w⁺` on `M₁` by

`u * m = (u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂)` for `m = (u₁, h, u₂) ∈ M₁` and `u ∈ U_w⁺`,

and derives formula (1.11):

`f_α(π(m)) = ∫_{U_w⁺} α(u * m) du⁺` for `m ∈ M₁`.

The left side is the cell function `f_α` of Lemma 1.10 evaluated at `π(m)`. The right
side is an integral over the `U_w⁺`-orbit of `m` in `M₁`. Here `U_w⁺ = U ∩ w⁻¹ U w`
(printed p.174). No matching source-specific errata note was found.

In the source, `du⁺` is the measure on `U_w⁺` obtained when the invariant measure `du` of
`U` is written as an iterated integral over the decomposition `U = U_w⁺ · U_w⁻`
(printed p.176).

This pair formalizes the source's action and the right side of (1.11) only.
`bruhatFiberAverage r K w μ α` is the raw function `A_α(m) = ∫ α(u • m) dμ(u)` on the
coordinate space `M = U × (H × U)`, which corresponds to `M₁`. It is not a function on
the cell. The source's cell function `f_α` on `M₂` is not constructed here, and the
identity `A_α = f_α ∘ π` under the source's choice of `du⁺` is not formalized. That
identity is the content of (1.11) together with Lemma 1.10, and it belongs to cell
descent. The following are internal deductions, not attributed to the paper: the
generality of an arbitrary field and topological field below, an arbitrary Borel measure
finite on compact sets instead of `du⁺`, the raw function-valued linear map, the
closed-embedding argument for compact support, the support law and the right-invariance
law.

## Notation, factor order and orientation

Fix a field `K` in an arbitrary universe, a natural rank `r` (including `r = 0`) and a
permutation `w` of `Fin r`. Write

- `U = upperUnipotent r K` and `P = permutationUnipotentPlus r K w`, both subgroups of the
  actual group `Langlands.GeneralLinear r K` of invertible matrices;
- `H = Fin r → Kˣ` and `h(d) = Iwasawa.diagonalUnits d`, the diagonal matrix with entries
  `d i`;
- `p = permutation r K w`, the published permutation matrix sending `e_j` to `e_(w j)`;
  it is the source's matrix `w`, as in `Langlands.Group.GL.UpperBruhatCells`;
- `M = U × (H × U)`. Lean's product is right-associated, so `m.1 = u₁`, `m.2.1 = d` and
  `m.2.2 = u₂` for `m = (u₁, d, u₂)`.

The action is `bruhatFiberAct r K w u m`, which is

`(u₁ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹, d, u * u₂)`.

The products in the first component are products in `Langlands.GeneralLinear r K`,
evaluated left to right; the result is bundled in `U`. The last component is the
product in `U` of the image of `u` under the actual inclusion
`Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent r K w)` with `u₂`. This
is exactly Shalika's action, with `h` written as `h(d)`. It is a left action:
`u • (v • m) = (u * v) • m`.

## Declarations

| Lean name | Meaning |
| --- | --- |
| `permutation_diagonal_conj_inv_mem_upperUnipotent` | For `u ∈ P` and `d : H`, `p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹ ∈ U`. |
| `bruhatFiberAct_fst_mem` | The first component `u₁ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹` lies in `U`. |
| `bruhatFiberAct` | The action map `P → M → M` displayed above. |
| `bruhatFiberAct_fst_val` | Evaluation of the first component in the general linear group. |
| `bruhatFiberAct_fst_matrix` | The same evaluation as a product of the six underlying matrices. |
| `bruhatFiberAct_snd_fst` | The diagonal parameter is unchanged. |
| `bruhatFiberAct_snd_snd`, `bruhatFiberAct_snd_snd_val` | The last component is `inclusion u * u₂`, with underlying matrix `u * u₂`. |
| `bruhatFiberAct_one` | `1 • m = m`. |
| `bruhatFiberAct_bruhatFiberAct` | `u • (v • m) = (u * v) • m`. |
| `bruhatFiberMulAction`, `bruhatFiberMulAction_smul` | The action bundled as `MulAction P M`. This is a definition, not a global instance; its `•` is `bruhatFiberAct`. |
| `upperBruhatTorusMap_bruhatFiberAct` | Fiber law: `upperBruhatTorusMap r w (u • m) = upperBruhatTorusMap r w m`. |
| `continuous_bruhatFiberAct` | Joint continuity of `(u, m) ↦ u • m` on `P × M`. |
| `continuous_bruhatFiberAct_left`, `continuous_bruhatFiberAct_orbit` | Continuity in `m` for fixed `u`, and in `u` for fixed `m`. |
| `bruhatFiberActHomeomorph` | For fixed `u`, the map `m ↦ u • m` as a homeomorphism `M ≃ₜ M` whose inverse is `m ↦ u⁻¹ • m` (`bruhatFiberActHomeomorph_apply`, `bruhatFiberActHomeomorph_symm_apply`). |
| `continuous_bruhatFiberAct_slice` | For a test function `α` on `M`, the slice `u ↦ α (u • m)` is continuous. |
| `isClosed_permutationUnipotentPlus` | `P` is closed in `Langlands.GeneralLinear r K`. |
| `isClosedEmbedding_bruhatFiberAct_orbit` | For fixed `m`, `u ↦ u • m` is a closed embedding `P → M`. |
| `hasCompactSupport_bruhatFiberAct_slice` | Each slice `u ↦ α (u • m)` has compact support on `P`. |
| `integrable_bruhatFiberAct_slice` | Each slice is Bochner integrable for `μ`. |
| `bruhatFiberAverage` | The complex linear map `SchwartzBruhat M →ₗ[ℂ] (M → ℂ)`, `α ↦ (m ↦ ∫ u, α (u • m) ∂μ)`. |
| `bruhatFiberAverage_apply` | The pointwise evaluation law, by definition. |
| `exists_bruhatFiberAct_mem_support_of_mem_support` | If the average of `α` is nonzero at `m`, then `α (u • m) ≠ 0` for some `u : P`. |
| `exists_bruhatFiberAct_mem_tsupport_of_mem_support` | Under the same hypothesis, `u • m ∈ tsupport α` for some `u : P`. |
| `bruhatFiberAverage_bruhatFiberAct` | If `μ` is invariant under right multiplication on `P`, then the average of `α` takes the same value at `v • m` and at `m`. |
| `padic_bruhatFiberAverage_hypotheses` | The canonical topology of every p-adic field is a Hausdorff topological ring. |
| `padic_bruhatFiberAverage` | The p-adic specialization described below. |

## Hypotheses and generality

The algebraic section assumes only `[Field K]`. The continuity results assume
`[TopologicalSpace K] [IsTopologicalRing K]`. Closedness of `P`, the closed embedding
and everything about the average also assume `[T2Space K]`. No local compactness,
total disconnectedness or countability is assumed.

The topology of `Langlands.GeneralLinear r K` is Mathlib's topology on the units of the
matrix ring; `U` and `P` carry the subspace topology. `Kˣ` carries the units topology,
`H` the product topology, and `M` and `P × M` the product topology. Test functions on
`M` are the imported `SchwartzBruhat M`: locally constant compactly supported complex
functions.

The measure is a variable
`μ : (letI := borel P; Measure P)`, together with the hypothesis
`[IsFiniteMeasureOnCompacts μ]`. So `P` carries its Borel σ-algebra, defined as
`borel P` from its subspace topology, and `μ` is any measure on that σ-algebra that is
finite on compact sets. No invariance, Haar, regularity or σ-finiteness hypothesis
enters the construction. The invariance law has the additional explicit hypothesis
`hμ : (letI := borel P; μ.IsMulRightInvariant)`, invariance under the maps
`u ↦ u * g`. No left-invariance or unimodularity hypothesis is assumed or used.
No character appears in the integrand.

## Proofs of the elementary laws

**Membership of the first component.** Let `u ∈ P`. The defining membership
`mem_permutationUnipotentPlus_iff` gives `p * u * p⁻¹ ∈ U`; taking inverses, and
rewriting by the group identity `(p * u * p⁻¹)⁻¹ = p * u⁻¹ * p⁻¹`, gives
`p * u⁻¹ * p⁻¹ ∈ U`. The published diagonal-normalization law
`monomial_conj_mem_upperUnipotent` (from `Langlands.Representation.Whittaker.CompatibleTorus`,
applied to `g = u⁻¹`) then gives `(p * h(d)) * u⁻¹ * (p * h(d))⁻¹ ∈ U`, which equals
`p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹` by the `group` tactic. That law conjugates the diagonal
factor entrywise: the entries become `d (w⁻¹ i) * g (w⁻¹ i) (w⁻¹ j) * d (w⁻¹ j)⁻¹`, so
vanishing and unit diagonal are unchanged. This is
`permutation_diagonal_conj_inv_mem_upperUnipotent`. Reassociating as
`u₁ * (p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹)` and using `u₁ ∈ U` and closure of `U` under
multiplication gives `bruhatFiberAct_fst_mem`.

**Evaluation laws.** `bruhatFiberAct_fst_val`, `bruhatFiberAct_snd_fst`,
`bruhatFiberAct_snd_snd` and `bruhatFiberAct_snd_snd_val` hold by definition.
`bruhatFiberAct_fst_matrix` follows from `bruhatFiberAct_fst_val` and `Units.val_mul`.

**Identity and composition.** Both are proved componentwise by `Prod.ext` and
`Subtype.ext`. For the identity, the first component is
`u₁ * p * h(d) * 1⁻¹ * h(d)⁻¹ * p⁻¹ = u₁`, by `group`, and the last is `1 * u₂ = u₂`.
For composition, the diagonal parameter of `v • m` is again `d`, so the first component
of `u • (v • m)` is
`u₁ * p * h(d) * v⁻¹ * h(d)⁻¹ * p⁻¹ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹`, which `group`
identifies with `u₁ * p * h(d) * (u * v)⁻¹ * h(d)⁻¹ * p⁻¹`, using
`(u * v)⁻¹ = v⁻¹ * u⁻¹`. The last component is `u * (v * u₂) = (u * v) * u₂` by
associativity. The `MulAction` structure uses these two laws.

**Fiber law.** By `upperBruhatTorusMap_val`, the image of `u • m` has underlying matrix
`(u₁ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹) * p * h(d) * (u * u₂)`, which `group` reduces to
`u₁ * p * h(d) * u₂`, the image of `m`. Only this invariance is proved. It is not
asserted that two points of one fiber lie in one `P`-orbit.

**Continuity and homeomorphisms.** In `continuous_bruhatFiberAct` the first component
is a product of continuous maps to the topological group of units: the subtype value
maps, the constants `p` and `p⁻¹`, `h(d)` via the published `continuous_diagonalUnits`,
and inversion. The last component is `u * u₂` in the general linear group. Both lift
to the subtype `U` by `continuous_induced_rng`, and the middle component is a
projection. The fixed-`u` and fixed-`m` continuity results compose with
`m ↦ (u, m)` and `u ↦ (u, m)`. `bruhatFiberActHomeomorph u` has inverse the map
for `u⁻¹`, by the composition and identity laws together with `u⁻¹ * u = 1` and
`u * u⁻¹ = 1`.

**Closedness of `P`.** By `mem_permutationUnipotentPlus_iff`, `P` is the intersection
of `U` with the preimage of `U` under the continuous map `g ↦ p * g * p⁻¹`. The
published `UpperUnipotent.isClosed`, which uses `T2Space K`, says `U` is closed.

**Closed embedding of each orbit map.** Fix `m = (u₁, d, u₂)`. Let
`j : M → GL × (H × GL)` be the product of the subtype inclusions, with the identity
on `H`. It is a closed embedding because `U` is closed. Let
`Φ : GL → GL × (H × GL)` be
`Φ v = (u₁ * p * h(d) * v⁻¹ * h(d)⁻¹ * p⁻¹, d, v * u₂)`, defined on the whole general
linear group. `Φ` is continuous and has the continuous left inverse
`x ↦ x.2.2 * u₂⁻¹`, so `Function.LeftInverse.isClosedEmbedding` shows that `Φ` is a
closed embedding, because `GL × (H × GL)` is Hausdorff. The inclusion `P → GL` is a
closed embedding by closedness of `P`. By definition,
`j ∘ (u ↦ u • m) = Φ ∘ (P → GL)`, a composition of closed embeddings. Since `j` is a
closed embedding, `IsClosedEmbedding.of_comp_iff` gives the conclusion. This is the
recovery of `u` from the last component `u * u₂` by multiplication with `u₂⁻¹`.

## The raw average

**Compact support and integrability.** For a test function `α`, the slice
`u ↦ α (u • m)` is `α` composed with the orbit map, so it is continuous. The support
of `α` has compact closure, and the preimage of a compact set under a closed embedding
is compact. `HasCompactSupport.comp_isClosedEmbedding` packages this argument and gives
`hasCompactSupport_bruhatFiberAct_slice`. A continuous compactly supported function is
integrable for a measure finite on compact sets on a space whose σ-algebra contains the
open sets. In the proof, the Borel structure supplies `BorelSpace P` by `rfl`, and
`Continuous.integrable_of_hasCompactSupport` gives `integrable_bruhatFiberAct_slice`.

**Linearity.** `bruhatFiberAverage μ` sends `α` to `m ↦ ∫ u, α (u • m) ∂μ`. Additivity
is `integral_add` applied to the two integrable slices, and complex homogeneity is
`integral_const_mul`. `bruhatFiberAverage_apply` is the defining evaluation formula.
The codomain is the space of all functions `M → ℂ`.

**Support.** If the average of `α` is nonzero at `m` but `α (u • m) = 0` for every `u`,
then the integrand is the zero function and `integral_zero` contradicts the hypothesis.
So some `u` has `α (u • m) ≠ 0`, and `subset_tsupport` puts `u • m` in `tsupport α`.

**Right invariance.** Assume `μ` is invariant under right multiplication. By
`bruhatFiberAct_bruhatFiberAct`, the integrand at `v • m` is
`u ↦ α (u • (v • m)) = α ((u * v) • m)`. The change of variables `u ↦ u * v`, in the
form `integral_mul_right_eq_self`, turns `∫ u, α ((u * v) • m) ∂μ` into
`∫ u, α (u • m) ∂μ`. Measurability of right multiplication comes from continuity of
multiplication on `P` and the Borel structure. This direction matches the left action
`u • (v • m) = (u * v) • m`: the substitution is a right translation `u ↦ u * v`, and
only right invariance of `μ` is assumed.

## p-adic specialization

Let `p` be a prime, `F : PadicField.{uF} p`, `n : ℕ` and `w` a permutation of
`Fin (n + 1)`. `padic_bruhatFiberAverage_hypotheses` shows that the canonical topology
`F.canonicalTopologicalData.topology` makes `F.Carrier` a topological ring, using the
canonical valuative relation and local-field certificate, and that it is Hausdorff, by
the published `TopologicalData.fieldT2`.

`padic_bruhatFiberAverage` uses these canonical instances and the Borel structure on
`permutationUnipotentPlus (n + 1) F.Carrier w`. For every measure `μ` finite on compact
sets it states the following: each orbit map is a closed embedding. For every `α` and
`m`, the slice is integrable, the average evaluates by the displayed integral, the
`tsupport` conclusion holds at every point of the nonzero support, and right
invariance of `μ` implies invariance of the average under every `v`. The rank `n + 1`
includes `n = 0`. No additive character or representation is involved.

## Scope

This pair proves only the elementary laws listed above. It does not prove local
constancy of the average, does not claim that the average has compact support on `M`,
and does not construct a test function on the cell. It proves no coordinate
homeomorphism, quotient-map theorem, fiber transitivity, surjectivity of orbital
integration, Bruhat decomposition, uniqueness of coordinates, translation covariance,
Haar or unimodularity statement, or Shalika invariance of distributions. None of
these is assumed by any declaration here.
