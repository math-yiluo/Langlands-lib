# The abelian category of smooth equivariant sheaves

Author: Worker 13. Built on Worker 13's `Langlands.Sheaf.Equivariant.Smooth`
and `Langlands.Sheaf.Equivariant.SmoothPart` (this submission), Worker 61's
published `Langlands.Sheaf.Equivariant.Exact` and the published abelian
structure with enough injectives of `TopologicalSheaf G X (ModuleCat R)`.

Let `R` be a commutative ring and `G` a topological group
(`IsTopologicalGroup`) acting on a topological space `X` by continuous
translations (`ContinuousConstSMul`), with `HasStableNeighbourhoods G X` from
`SmoothPart`. Here `R`, `G`, `X` and the module carriers all lie in one
universe `u`, as the published abelian structure requires. Individual results
below omit hypotheses they do not use, as the Lean `omit` lines record.

## Closure properties

- `smoothSheafProperty_isClosedUnderSubobjects`: from the published
  `IsSmoothSheaf.of_mono`.
- `smoothSheafProperty_containsZero`: a zero sheaf is smooth. The zero morphism
  from the zero sheaf into its own smooth subsheaf is a monomorphism, and that
  smooth subsheaf is smooth by `isSmoothSheaf_smoothSubsheaf`.
- `IsSmoothSheaf.of_epi`: the target of an epimorphism `f : F ⟶ F'` from a
  smooth sheaf is smooth. Worker 61's `toSheaf_preservesEpimorphisms` makes the
  underlying ordinary morphism an epimorphism. By Mathlib
  (`TopCat.Sheaf.isLocallySurjective_iff_epi`) it is locally surjective. So a
  section `t` of `F'` near a point `x` is, on a neighbourhood `V` of `x`, the
  image of a section of `F`. That section is locally fixed at `x`, hence so is
  its image, the restriction of `t` to `V`, by `IsLocallyFixedAt.map`. Then
  `IsLocallyFixedAt.of_restrict` gives the claim for `t`. This uses only
  continuity of translations.
- `smoothSheafProperty_isClosedUnderQuotients` packages `IsSmoothSheaf.of_epi`.
- `limit_sections_ext`: sections of a finite limit of equivariant module sheaves
  are determined by their projections. Evaluation on an open preserves the
  limit, and Mathlib's `Concrete.isLimit_ext` applies.
- `hom_app_map_apply`: morphisms commute with the maps of the transport
  presheaves, applied to a section.
- `smoothSheafProperty_isClosedUnderBinaryProducts`: the two projections of a
  section of a binary product are locally fixed. `IsLocallyFixedAt.exists_common`
  provides one open subgroup and one stable neighbourhood for both, and
  `limit_sections_ext` gives fixedness of the section itself.
- `smoothSheafProperty_isClosedUnderFiniteProducts` follows from binary
  products and the zero object.

## Abelian structure and injectives

`smoothTopologicalSheaf_abelian` is Mathlib's result for full subcategories of
an abelian category that contain zero and are closed under kernels, cokernels
and finite products (`Mathlib.CategoryTheory.Abelian.Subcategory`). Kernels
and cokernels are subobjects and quotients, so the closure results above
apply. `smoothInclusion_preservesMonomorphisms` and
`smoothInclusion_preservesEpimorphisms` come from the same Mathlib file.

`injective_smoothCoreflector_obj` proves that the smooth part of an injective
equivariant module sheaf is injective in `SmoothTopologicalSheaf R G X`. The
smooth part is right adjoint to an inclusion that preserves monomorphisms.
`smoothTopologicalSheaf_enoughInjectives` follows by Mathlib's
`EnoughInjectives.of_adjunction` from `smoothAdjunction`, since the inclusion
preserves and reflects monomorphisms and equivariant module sheaves have
enough injectives. Concretely, a smooth sheaf embeds into the smooth part of
an injective equivariant sheaf containing it.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.4, Definition 1.4.1, printed pp.7–8, defines
the category `T_G(X_ét)` of étale `G`-sheaves as a full subcategory of étale
`G_d`-sheaves. Theorem 1.4.2, printed p.8, identifies it with the category
of étale sheaves on `X(G)`. Section 1.5, printed p.11, takes derived functors
of compactly supported sections on that category. Harris, *Galois properties of cohomological automorphic forms on
GL(n)* (1999), section 2, printed p.304, works with sheaves of smooth
`S(ẽ)`-modules, which Berkovich calls discrete. Worker 13 read these passages
in the original.

The present module proves the abelian structure and enough injectives
directly on the published ordinary-topological transport site. It does not
use Berkovich's Theorem 1.4.2. It does not claim that the inclusion of smooth
sheaves preserves injective objects, or that the smooth part is exact.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules other than `SmoothPart` are present in Library commit
`9a0767626050f3346ad5f25e37cef39f38a5c0dc`.
