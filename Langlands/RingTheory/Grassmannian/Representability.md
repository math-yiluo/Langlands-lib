# The scheme representing the quotient Grassmannian

The theorem
`Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover`
constructs a scheme representing Mathlib's quotient Grassmannian on all
commutative algebra tests. Its affine opens correspond exactly to quotient
bases drawn from the original module. The primary definition
`Module.Grassmannian.SchemeRepresentation.scheme` chooses the underlying
scheme from this proved existence theorem.

The input consists of any universe-zero commutative ring `R`, any
universe-zero `R`-module `M` with an additive commutative group, and
`k : ℕ`. There is no finite generation, projectivity, freeness,
Noetherianity, positivity or nontriviality hypothesis.

## Exact representation and charts

For every commutative `R`-algebra `A`, the represented type is the actual
Mathlib type `Module.Grassmannian A (A ⊗[R] M) k`. Its elements are
submodules whose quotients are finite projective of constant stalk rank
`k`. Thus the rank refers to the quotient. Its maps are the existing
`Module.Grassmannian.map φ` for every `φ : A →ₐ[R] B`.

The theorem constructs `Gr : Scheme.{0}`, a morphism
`p : Gr ⟶ Spec R`, and equivalences

\[
 \operatorname{pt}_A:\operatorname{Grass}_k(A\otimes_R M)
 \simeq
 \{g:\operatorname{Spec}A\longrightarrow\operatorname{Gr}
       \mid g\mathbin{\gg}p=\operatorname{Spec}(\operatorname{algebraMap} R A)\}.
\]

For every `φ : A →ₐ[R] B` and point `N`, the morphism underlying
`pt B (Module.Grassmannian.map φ N)` is
`Spec φ ≫ (pt A N).1`. No flatness assumption is imposed on `φ`.

For every `x : Fin k → M` the output supplies an open subset `V x` of
`Gr`. These opens cover `Gr`, as the equality `⨆ x, V x = ⊤`, and each
is an affine open. Their membership criterion is stated for the entire
image of an affine-test morphism:

\[
 \operatorname{range}((\operatorname{pt}_A N).1)
       \subseteq V_x
 \quad\Longleftrightarrow\quad
 \left(v\longmapsto\sum_i v_i q_N(1\otimes x_i)\right)
       \text{ is bijective}.
\]

Here `q_N = N.toSubmodule.mkQ` and `v : Fin k → A`. The theorem
quantifies all such families `x`; independence in `M` is not an input.
The chart's bijectivity means that their quotient images form a basis.

The chosen `scheme R M k` is the first witness of this theorem. The
theorem's `choose_spec` supplies the structure morphism, point
equivalences and affine-open family with all the stated properties for
that chosen scheme. The definition makes no extra existence assumption.

## Implemented construction

The proof applies
`AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover`
to the Grassmannian algebra functor. Its input is established as follows.

- Mathlib's `Module.Grassmannian.map_id` and `map_comp` give the functor
  laws.
- `Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away`
  proves finite principal-open descent for the actual quotient points.
  It applies to any finite family spanning the unit ideal and compatible
  quotient points over its specified principal localizations.
- The chart predicate is the displayed quotient-basis condition. The
  theorem
  `Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset`
  proves its affine-test openness.
- For each `x`, the theorem
  `Module.Grassmannian.exists_chart_equiv_algHom_symmetricAlgebra_quotient`
  supplies a commutative chart algebra
  `S x = SymmetricAlgebra R (Fin k → M) ⧸ J x`, its natural chart
  equivalences, and their base-change compatibility. The ideal is the
  explicit chart-normalization ideal of that theorem; the proof chooses
  these supplied ideals and equivalences.
- Over any field `R`-algebra, the images of all `m : M` span the
  quotient. Applying
  `Module.Grassmannian.exists_injective_and_bijective_of_span_eq_top`
  with the identity generating family gives a quotient basis of length
  `k` drawn from `M`. This proves field-valued chart coverage.

The gluing theorem therefore constructs the scheme `X`, its structure
morphism `p`, its natural affine-test point equivalences `pt`, and
open immersions `j x : Spec (S x) ⟶ X`. The defining chart formula
expresses `pt A N` on chart elements as the composite of the spectrum
of the chart algebra homomorphism with `j x`. The opens in this module
are `V x = (j x).opensRange`. Their affineness is
`isAffineOpen_opensRange (j x)`, and joint surjectivity of the `j x`
proves the equality of their supremum with the whole scheme.

To prove the image criterion in the forward direction, a point morphism
whose image lies in `V x` factors through `j x` by
`IsOpenImmersion.lift`. The factorization lies over `Spec R`.
The helper `preimage_comp_algebraMap` converts this scalar compatibility
through the fully faithful spectrum functor. The definition `ptAlgHom`
then equips the preimage ring map with its `R`-algebra compatibility;
`spec_map_ptAlgHom` says its spectrum is the factorization itself.
Applying the inverse chart equivalence gives a chart point `N'`.
The gluing theorem's chart formula identifies the morphisms of `N'`
and `N`. Injectivity of `pt A` gives `N' = N`, so `N` satisfies the
quotient-basis condition. Conversely, that same chart formula directly
factors any chart point through `j x`, proving its image lies in `V x`.

## Source and adaptations

The original is registered as
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, distribution SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete originals read and compared are:

- `P2M/Sol/S_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover.lean`,
  lines 1–118, SHA-256
  `fef4c87db25d0b53630a26924e34674dbd2147df0fc0a72aa97dc5a893b32fd2`.
- `Theorems/Thm_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover.lean`,
  lines 1–25, SHA-256
  `27699b6b45c862a69cd447554c00eed9f051020f87e2289287a2086b460b3cd2`.

The exported theorem signature is byte-identical to the original
wrapper. The proof and its three spectrum/preimage helpers are retained.
The generated solution namespace `GrassRepS1` becomes
`Module.Grassmannian.SchemeRepresentation`, the theorem is exported
directly under the original name, and focused Library imports replace
the aggregate `Mathlib` and generated `P2M` imports. The original global
simp-attribute removals are unnecessary. No mathematical hypothesis,
construction or conclusion of the theorem changes.

The added `scheme` definition is the direct choice of the first witness
of this proved theorem. Its provenance is this internal packaging step,
not a further assertion attributed to the original wrapper.

The existing Apache 2.0 notices from the distribution are retained in
[LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE) and
[ATTRIBUTION.md](../../../licenses/Anthropic-FLT/ATTRIBUTION.md).
The source attribution table has no separate entry for these modules.

## Scope within the CM task

The scheme exists for arbitrary `M`; the theorem asserts no finite type,
smoothness, properness, projectivity or projective embedding. Its point
equivalences are natural on all commutative `R`-algebras, without an
additional claimed equivalence on a larger category of tests.

This Grassmannian construction is an intermediate geometric prerequisite.
It does not construct the polarized abelian moduli scheme, impose the
PEL determinant and Rosati conditions, or identify a scheme with the
normalized Harris CM presheaf. The exact CM representation, its
componentwise admissibility, smoothness and projectivity remain
obligations of the host `DivisionCMRepresentabilityStatement`.
