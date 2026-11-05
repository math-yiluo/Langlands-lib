# Regular generation of the unramified compact picture by translates

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It works
with the actual Levi-normalized unramified induction of
`CompactIntertwiningFamilies` and its fixed compact picture on a compact open
subgroup `K` with `G = P K`. The main results are `regularTranslateSpan_eq_top`
and its existence form `exists_regularTranslateSpan_eq_top`. Under explicit
opposite-radical hypotheses and finite length of the inducing representation,
every compact section is a finite sum

`f = ∑ᵢ cᵢ(χ) • T_χ(gᵢ) φᵢ`,

valid at every unramified parameter `χ`. Here `T_χ(g)` is right translation by
`g ∈ G` in the induction at `χ`, read on the compact picture. Each `φᵢ` is a
compact section fixed by one compact open subgroup `L₀`. Each coefficient `cᵢ`
lies in the concrete regular algebra `unramifiedRegularFunctions ν`. The
expansion is chosen once for each `f`; it does not depend on `χ`.

The module proves nothing about intertwining operators. It is the
finite-generation input for a uniform regular numerator of the standard
compact operator.

## Finite generation of the inducing representation

`exists_orbit_generators`: a finite-length smooth representation `A` of a
group `M` has finitely many vectors `v j` such that every vector is a complex
linear combination of translates `A(m)(v j)`. Finite length gives a Noetherian
group-algebra module (Mathlib's `isFiniteLength_iff_isNoetherian_isArtinian`),
hence finitely many group-algebra generators. The complex span of their orbits
is stable under every `A(m)`, hence under the group algebra (Mathlib's
`asAlgebraHom_of` and `asModuleEquiv_map_smul`), so it is everything.

## Parameter translates and the regular translate span

- `compactTranslate χ g` is the published compact-picture equivalence at `χ`,
  composed with right translation by `g` and the inverse equivalence. It is
  multiplicative in `g` (`compactTranslate_mul`). For `k ∈ K` it is the fixed
  right action of `K` on the compact picture, for every `χ`
  (`compactTranslate_of_mem`). Its value at `k ∈ K` is the actual covariance
  extension at `k g` (`eval_compactTranslate`).
- `regularTranslateSpan φ` is the set of compact sections `f` having one
  expansion `f = ∑ᵢ cᵢ(χ) • compactTranslate χ gᵢ (φ (jᵢ))` valid for all `χ`,
  with regular `cᵢ`. It is a complex submodule, contains the generators
  (`mem_regularTranslateSpan_self`), and is stable under the action of `K`
  (`compactPictureAction_mem_regularTranslateSpan`).
- `mem_regularTranslateSpan_of_translate`: if `f` is in the span and
  `F = r(χ) • compactTranslate χ g f` for all `χ` with one regular `r`, then
  `F` is in the span.

## Compact sections supported on one double coset

`compactSection H v` is the published `compactDoubleCosetSection` on the
compact group `K`, for a compact open subgroup `H` of `K`, centered at `1`
with value `v`. Here `v` must be fixed by the Levi projections of `P ∩ H`. It is
supported on `(K ∩ P) H` and equals `A(proj p) v` at `p l`
(`eval_compactSection_mul`, `eval_compactSection_eq_zero`). `compactCell L v`
is the same section for a compact open subgroup `L` of `G`, through `L ∩ K`.
Cells are fixed by `L ∩ K`, hence by `L` when `L ⊆ K`
(`compactCell_mem_compactFixed`; the conclusion is membership in the published
`CompactFixedVectors h K A L`, which is fixedness under `L ∩ K`). Without
`L ⊆ K` full `L`-invariance can fail. Cells are linear in the value
(`compactCell_finset_sum`).

`compactSection_mem_of_le` is the averaging step. Let `S` be a complex
submodule stable under `K`, let `L` be a compact open subgroup of `G` with
`L ∩ K ⊆ H`, and let `v` be fixed by the projections of `P ∩ H` and of `P ∩ L`.
If the cell on `L` with value `v` lies in `S`, so does the section on `H`. The
published compact average over `H` of the small cell is a finite coset mean of
`K`-translates (`averageMap_eq_finiteMean_cosets` of
`CompactIntertwiningCompression`), hence lies in `S`. Its value at `1` is
`c • v`, where `c` is the number of cosets of `H ∩ L` in `H` whose chosen
representative lies in `(K ∩ P) L`, divided by the number of all cosets. This
is nonzero because the trivial coset counts. The average is fixed by `H` and vanishes off
`(K ∩ P) H`. Covariance then identifies it with `c` times the section on `H`.
`compactCell_mem_of_le` is the same statement for two compact open subgroups
of `G`.

## Factorized subgroups and Levi translates of cells

Fix a subgroup `Ubar` with `P ∩ Ubar = 1` (hypothesis `hPUbar`), normalized by
`M` (hypothesis `hMUbar`). `IsCellFactorized U M Ubar L` means that every
element of `L` is `u m n` with `u ∈ L ∩ U`, `m ∈ L ∩ M` and `n ∈ L ∩ Ubar`.

- `IsCellFactorized.projection_mem`: the Levi projection of an element of
  `P ∩ L` lies in `L`.
- `eq_one_of_mem_radical_of_mem_levi` and `factor_unique`: the decomposition
  `u m n` is unique.
- `IsCellFactorized.inf_conj`: for factorized `L₀` and `L'` and `a ∈ M`, the
  intersection `L' ∩ a⁻¹ L₀ a` is factorized. This uses uniqueness.
- `IsCellFactorized.conj`: conjugates by Levi elements are factorized.

`inductionScalar χ p` is the actual normalized twisted inducing scalar
`δ^{1/2}(p) χ(proj p)`. It is multiplicative. It equals `1` on `P ∩ K`
(`inductionScalar_of_mem`), by the published triviality of the half-character
and of unramified pullbacks on compact open subgroups. `extension_eval_mul` is
the published extension formula at `p k` in this notation.

For a factorized `L ⊆ K`, the actual extension of the cell with value `v` at
`χ` equals `inductionScalar χ p • A(proj p) v` at `p n` with `n ∈ L`
(`extension_compactCell_mul`). It vanishes off `P (L ∩ Ubar)`
(`extension_compactCell_eq_zero`). The proof of the latter writes
`x = p k` with `G = P K` and uses `eval_compactCell_eq_zero_of_factorized`.

`compactTranslate_compactCell`: let `m ∈ M`, and let `La, Lb ⊆ K` be
factorized compact open subgroups whose opposite parts satisfy
`n ∈ Lb ∩ Ubar ↔ m⁻¹ n m ∈ La ∩ Ubar`. Then for every `χ`

`compactTranslate χ m (cell La w) = inductionScalar χ m • cell Lb (A(m) w)`.

Both sides are compared at every point of `K`, using the two extension
formulas.

## The generation argument

The section `Generation` fixes `L₀ ⊆ K`, compact, open and factorized, and
`g ∈ G` with the published `Jacquet.IsIwahoriContraction L₀ U M Ubar g`. Thus
`g ∈ M`, `g⁻¹ (L₀ ∩ M) g ⊆ L₀ ∩ M`, and `g⁻ˢ (L₀ ∩ Ubar) gˢ` shrinks into
every open subgroup. The generators are all compact sections fixed by `L₀`
(`fixedGenerators L₀`). `inductionScalarRegular m` is the regular function
`χ ↦ δ^{1/2}(m) χ(m)`: a constant times the published character evaluation
`unramifiedEvaluationRegular`. `inductionScalar_inv_mul` records
`δ^{1/2}χ(m⁻¹) δ^{1/2}χ(m) = 1`.

1. Contraction (`compactCell_mem_of_contraction`). Let `L' ⊆ L₀` be
   factorized and let `v` be fixed by the projections of `P ∩ L₀`. Choose `s`
   with `g⁻ˢ (L₀ ∩ Ubar) gˢ ⊆ L'`. The subgroup `L₃ = L' ∩ g⁻ˢ L₀ gˢ` is
   factorized, and its opposite part is exactly `g⁻ˢ (L₀ ∩ Ubar) gˢ`. The
   vector `w = A(gˢ) v` is fixed by the projections of `P ∩ L₀`. The Levi
   translate formula with `m = g⁻ˢ` gives
   `cell L₃ v = δ^{1/2}χ(gˢ) • T_χ(g⁻ˢ)(cell L₀ w)` for all `χ`, and
   `cell L₀ w` is a generator. Averaging from `L₃` to `L'` finishes the step.
2. Levi step (`compactCell_mem_of_levi`). Let `L ⊆ K` be factorized and
   `m ∈ M` with `m⁻¹ L m ⊆ L₀`. Then the cell on `L` with value `A(m) v` is
   `δ^{1/2}χ(m⁻¹) • T_χ(m)` of the cell on `m⁻¹ L m` with value `v`. The latter
   lies in the span by step 1.
3. Arbitrary values (`compactCell_mem_of_factorized`). Assume vectors `v j`
   fixed by the projections of `P ∩ L₀` whose `M`-orbits span `A`, and
   arbitrarily small compact open factorized subgroups (`hbasis`). Write
   `u = ∑ c(m, j) A(m)(v j)`, a finite sum. Choose a factorized `L''` inside
   `L ∩ ⋂ m L₀ m⁻¹` over the finitely many `m` that occur. Linearity of cells
   and step 2 put the cell on `L''` with value `u` in the span. Averaging
   gives the cell on `L`.
4. `regularTranslateSpan_eq_top`. The published `compactLocalSectionSpanning`,
   applied to the compact group `K` and the closed subgroup `P ∩ K`, says that
   right translates of identity-centered double-coset sections span compact
   induction. The published `compactInclusion_bijective_of_compactSpace`
   identifies compact induction with the compact picture. Each such section on
   a compact open `H ⊆ K` is reached from a factorized `L ⊆ H` (step 3) by
   averaging. The span is stable under `K`. Small open subgroups of `K` come
   from `NonarchimedeanGroup`.

`exists_regularTranslateSpan_eq_top` derives these hypotheses from the
published `Jacquet.HasOppositeIwahoriContractionBasis U M Ubar g` and from
`A.HasFiniteLength`. Given an open `O ∋ 1`, the basis gives a compact open
`L₀ ⊆ O ∩ K` inside the open set where all finitely many generators
`v j` are fixed (smoothness of `A`). The basis provides
`IsIwahoriContraction L₀ U M Ubar g`. The opposite-order contraction
`IsIwahoriContraction L₀ Ubar M U g⁻¹` provides the factorization in the order
`U · M · Ubar`. The same basis supplies arbitrarily small factorized subgroups.

## Scope and provenance

The opposite subgroup `Ubar`, the condition `P ∩ Ubar = 1`, normalization by
`M`, the contracting element and the opposite Iwahori basis are explicit
hypotheses. The module does not construct them for the host's rational-point
radicals. It proves no statement about the standard intertwining integral, its
convergence, or rationality. The uniform numerator of the host task remains a
separate obligation; it is the intended consumer of this module.

The argument is an internal formalization of the standard fact that a parabolic
induction of a finitely generated representation is generated by vectors fixed
by a small Iwahori-factorized subgroup. It is proved with regular coefficients
in the unramified parameter. Every step is proved here from the published
Library declarations named above and Mathlib, and no literature theorem
replaces a proof.
