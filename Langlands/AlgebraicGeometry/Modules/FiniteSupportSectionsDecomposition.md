# Global sections of a module with finite closed support, localized at its points

Lean module: `Langlands.AlgebraicGeometry.Modules.FiniteSupportSectionsDecomposition`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`.

Author: Worker 998.

## Role and provenance

This is internal infrastructure for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`, the proof
of `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`. Its route uses
Euler characteristics of line bundles on `A ×_K A` whose higher direct images along a
projection are supported at finitely many closed points. The twist step is formula (10) in
the proof of (9.11) of Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, printed p.132,
PDF p.136). There such a direct image is compared with its twist by a line bundle that is
trivial near the support. This module supplies the sheaf-theoretic fact behind that
comparison. The global sections of a module supported at finitely many closed points are the
product of its sections over small neighbourhoods of those points. All declarations are
derived. None is a new mathematical notion or a statement target.

## Conventions

`relativeGlobalSections s` is the Library functor of relative global sections along
`s : Y ⟶ Spec R`, an `R`-module. `stalkSupport G` is the set of points where the abelian stalk
of `G` is nonzero (`Langlands.AlgebraicGeometry.Modules.ModuleSupport`).
`Scheme.Modules.restrictFunctor V.ι` restricts a module to the open subscheme `V`.

## Declarations

- `sectionsRestrict s G U`: the `R`-linear restriction map from the relative global sections
  of `G` to the relative global sections, along `U.ι ≫ s`, of the restriction of `G` to the
  open `U`. It is the image under `relativeGlobalSections s` of the unit of Mathlib's
  adjunction `restrictAdjunction U.ι`, followed by the component at the restriction of `G` of
  the Library isomorphism `relativeGlobalSectionsCompIso U.ι s` (module
  `Langlands.AlgebraicGeometry.Modules.PushforwardComparison`). That isomorphism identifies
  relative global sections along `s` of a pushforward `i_* M` with relative global sections
  of `M` along `i ≫ s`.
- `sectionsRestrict_apply`: the underlying function of `sectionsRestrict s G U` is the
  restriction map `G(⊤) ⟶ G(U.ι ''ᵁ ⊤)` of the abelian presheaf of `G`. The proof is `rfl`.
- `sectionsRestrictPi s G S V`: for a finite set `S` of points and opens `V x`, the
  `R`-linear map `t ↦ (sectionsRestrict s G (V x) t)_{x ∈ S}` into the product.
- `isClosed_finset_of_isClosed_singleton`: a finite set of closed points is closed, as a
  finite union of closed singletons.
- `sectionsRestrictPi_bijective`: let the stalks of `G` vanish outside a finite set `S` of
  closed points. For each `x ∈ S`, let `V x` be an open containing `x` whose only point of
  `S` is `x`. Then `sectionsRestrictPi s G S V` is bijective.

## Proof of `sectionsRestrictPi_bijective`

Work with the abelian sheaf `F` underlying `G`. Every section of `F` over an open that misses
`S` is zero. Its germs lie in zero stalks, so this is the Library lemma
`Langlands.Cohomology.FiniteClosedSupportSheaf.eq_zero_of_forall_not_mem`. Index a cover of
`Y` by `Option S`: `none` gives the open complement `C` of `S`, and `some x` gives
`(V x).ι ''ᵁ ⊤`, which equals `V x` (`Scheme.Opens.ι_image_top`). These opens cover `Y`:
a point of `S` lies in its own `V x`, and any other point lies in `C`. Two different opens
of the cover meet in an open that misses `S`. Indeed, `C` misses `S`, and a point of `S`
lying in `V x` and `V x'` equals both `x` and `x'`.

- Injectivity. Let `t` restrict to zero on every `V x`. Its restriction to `C` is zero
  because `C` misses `S`. By `TopCat.Sheaf.eq_of_locally_eq'`, `t = 0`.
- Surjectivity. Given sections `u x` over the `V x`, take the family `0` on `C` and `u x` on
  `V x`. It is compatible: two equal indices give equal restrictions, and on the overlap of
  two distinct opens both restrictions are zero, since that overlap misses `S`.
  `TopCat.Sheaf.existsUnique_gluing'` gives a global section that restricts to `u x` on every
  `V x`. By `sectionsRestrict_apply` this is the required preimage.

The module uses only Mathlib and the published Library modules `PushforwardComparison`
(which provides `DerivedSections`), `ModuleSupport` and
`Langlands.Cohomology.FiniteClosedSupportSheafProof`.
