# The original-sheaf comparison with the projector sheaf of compact sections

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, proof of the Theorem, printed
pp.39–40 / PDF pp.45–46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The inverse functor sends a nondegenerate `D(X)`-module `M` to the sheaf
with `M(U) = χ_U · M` on compact opens `U`. Its last paragraph starts from a
sheaf `M`, sets `M = M_c(X)`, and notes `χ_U · M = χ_U · M(U) = M(U)` for every
compact open `U`, i.e. a section over `U` is identified with its extension by
zero, a compact section fixed by `χ_U`. This file constructs that
identification as an actual morphism of complex vector sheaves
`F ⟶ P(Γc F)` and proves its naturality. It does not prove that it is an
isomorphism; that is a separate statement for a later proof task.

## Objects and sizes

`X : Type` carries a topology with `hX : Langlands.Topology.IsLocallyProfinite X`.
`F : VectorSheafScalars.VectorSheaf X` is a Mathlib sheaf of complex vector
spaces. `Γc F` is `(CompactSectionTestModule.compactSectionFunctor hX).obj F`,
the published compact sections `CompactSupport.submodule F.presheaf` with the
pointwise test action. `P` is `ProjectorVectorSheaf.functor.{0, 0} hX`, the
complex refinement of the published `ProjectorBasisSheaf.nondegenerateFunctor`
followed by `BasisMathlib.toMathlib (compactOpenBasis hX)`. Its sections over
an open `V` are the published compatible families
`BasisAllOpen.Families (rawPresheaf hX (Γc F)) V`, indexed by compact opens
`U ⊆ V`, with values in the projector ranges `Value hX (Γc F) U`, the fixed
parts of `χ_U`. Everything is at `Type`, because `CompactSupport` ties the
universes.

## Components

- `Γgerm_extend_of_mem` and `Γgerm_extend_of_not_mem` compute the global
  germs of the published zero extension `CompactGerms.extend` from a clopen.
  Inside the clopen they are the germs of the section, by
  `CompactGerms.restrict_extend`. Outside they vanish, by
  `CompactGerms.support_extend_subset`.
- `extension F hX U hUV s` is the published `CompactGerms.compactExtension`
  of the restriction `s|_U` for a compact open `U ≤ V`. A compact open is
  clopen because `X` is Hausdorff (`ProjectorBasisSheaf.clopen`).
  `Γgerm_extension_of_mem` and `Γgerm_extension_of_not_mem` give its germs.
- `extension_mem_fixedPart` proves `χ_U • extension = extension`, using
  `CompactSectionTestModule.characteristic_smul_eq_self`. Hence `component`
  is an element of the published projector range `Value hX (Γc F) U`.
- `action_extension` proves `χ_W • extension_U(s) = extension_W(s)` for
  `W ⊆ U`. This is the projector restriction of the published
  `rawPresheaf`, so `family F hX s` is a compatible family.
- `familyHom` is additive. `extension_smul` proves complex linearity of each
  component for the original complex structure. `family_restrict` proves
  compatibility with restriction to smaller opens.
- `map_extension` and `familyMap_family` prove that the published
  `CompactSupport.map φ.hom`, via `compactSectionMap`, commutes with the
  extensions for every sheaf morphism `φ`.

All equalities of sections are proved by comparing germs at every point
(`ext_compact`, from `VectorSheafScalars.ext_germ`).

## The comparison morphisms

- `additiveComparison F hX` is the morphism of additive sheaves from
  `CompactGerms.additive F` to `(BasisMathlib.toMathlib (compactOpenBasis hX)).obj
  ((nondegenerateFunctor hX).obj (Γc F))`. `additiveComparisonNat` is its
  naturality, a natural transformation between the corresponding functors on
  `VectorSheaf X`.
- `sheafComparisonApp F hX V` is the complex-linear map on sections over `V`
  into `ProjectorVectorSheaf.familySpace`. Linearity reduces to
  `extension_smul`. It also uses the published
  `NondegenerateScalars.scalarMul_eq_of_compatible`: the canonical complex
  scalars of `Γc F` agree with the original ones, because of the scalar tower
  `CompactSectionTestModule.isScalarTower`.
- `sheafComparison F hX : F ⟶ (ProjectorVectorSheaf.functor hX).obj
  ((compactSectionFunctor hX).obj F)` is the morphism of complex vector
  sheaves. `sheafComparison_app_val` states its literal compact-open formula:
  the component at a compact open `U ⊆ V` of the image of `s` is
  `compactExtension F U _ _ (s|_U)`. `sheafComparison_forget₂` identifies its
  underlying additive map with `additiveComparison`.
- `sheafComparisonNat : 𝟭 (VectorSheaf X) ⟶ compactSectionFunctor hX ⋙
  ProjectorVectorSheaf.functor hX` is the natural transformation with these
  components.

The module-side comparison, the inverse laws, and the isomorphism and
equivalence statements are not part of this file.

Worker 184 implements this unit for Task 5338. The projector sheaf functor
`ProjectorVectorSheaf` is by Worker 188 and is imported unchanged.
