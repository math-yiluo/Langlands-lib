# The hyperext abutment filtration as a functor

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextAbutmentFiltration` (`filtration`, `graded`,
`filtration_le_of_le`; Worker 61) and
`Langlands.Cohomology.HyperextAbutmentNaturality` (`filtrationPrecomp`,
`filtrationPostcomp`, `gradedPrecomp`, `gradedPostcomp` and their identity,
composition and commutation lemmas; Worker 61), and on Mathlib's t-structures,
its category `AddCommGrpCat` of additive groups and its preadditive coyoneda
functor.

Let `t` be a t-structure on a pretriangulated category `C`, and let `K` and
`B` be objects of `C`. The abutment filtration of `HyperextAbutmentFiltration`
is the decreasing filtration `F^p(K, B) = filtration t K B n p` of
`Hom(K, B⟦n⟧)` (Mathlib's `ShiftedHom K B n`), with graded pieces
`gr^p(K, B) = graded t K B n p = F^p / F^{p+1}`. The module
`HyperextAbutmentNaturality` proves that these groups are contravariant in `K`
(precomposition with `φ : K' ⟶ K`) and covariant in `B` (postcomposition with
`ψ⟦n⟧'` for `ψ : B ⟶ B'`), but it states this for single morphisms only. This
module packages the same maps as Mathlib functors with values in
`AddCommGrpCat`, and adds the inclusion and projection maps as natural
transformations.

## Setting

All declarations are in the namespace `Langlands.Cohomology.HyperextAbutment`.
The category `C` has objects in `Type u` and morphisms in `Type v`; it is
preadditive, has a zero object and a shift by `ℤ` by additive functors, and is
pretriangulated; `t : TStructure C`. These are the hypotheses of the
corresponding sections of `HyperextAbutmentFiltration` and
`HyperextAbutmentNaturality`. No `IsTriangulated C` is needed. All functors
take values in `AddCommGrpCat.{v}`.

## Functors

| Declaration | Statement |
| --- | --- |
| `filtrationFunctor t K n p` | The functor `C ⥤ AddCommGrpCat` sending `B` to `F^p(K, B)` and `ψ : B ⟶ B'` to `filtrationPostcomp t K ψ n p`, the map `f ↦ f ≫ ψ⟦n⟧'`. |
| `gradedFunctor t K n p` | The functor `C ⥤ AddCommGrpCat` sending `B` to `gr^p(K, B)` and `ψ` to `gradedPostcomp t K ψ n p`. |
| `filtrationPrecompFunctor t B n p` | The functor `Cᵒᵖ ⥤ AddCommGrpCat` sending `K` to `F^p(K, B)` and `φ : K' ⟶ K` (a morphism `op K ⟶ op K'`) to `filtrationPrecomp t φ B n p`, the map `f ↦ φ ≫ f`. |
| `gradedPrecompFunctor t B n p` | The functor `Cᵒᵖ ⥤ AddCommGrpCat` sending `K` to `gr^p(K, B)` and `φ` to `gradedPrecomp t φ B n p`. |
| `filtrationBifunctor t n p` | The functor `Cᵒᵖ ⥤ C ⥤ AddCommGrpCat` sending `K` to `filtrationFunctor t K n p` and `φ` to the natural transformation whose component at `B` is `filtrationPrecomp t φ B n p`. |
| `gradedBifunctor t n p` | The functor `Cᵒᵖ ⥤ C ⥤ AddCommGrpCat` sending `K` to `gradedFunctor t K n p` and `φ` to the natural transformation with components `gradedPrecomp t φ B n p`. |
| `filtrationFunctor_map_hom`, `gradedFunctor_map_hom`, `filtrationPrecompFunctor_map_hom`, `gradedPrecompFunctor_map_hom` | The underlying additive maps of the images of morphisms are the maps named above (`simp` lemmas, by definition). |

So `(filtrationBifunctor t n p).obj (op K)` is `filtrationFunctor t K n p`
by definition, and the component at `B` of the image of `φ` is
`(filtrationPrecompFunctor t B n p).map φ`; the same holds for the graded
versions.

## Natural transformations

Below, `F^p(K, -)` stands for `filtrationFunctor t K n p` and `gr^p(K, -)` for
`gradedFunctor t K n p`. The functor
`shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op K)` sends `B` to the additive
group `K ⟶ B⟦n⟧` and `ψ` to postcomposition with `ψ⟦n⟧'`; it is the abutment
`Hom(K, B⟦n⟧)` as a functor of `B`.

| Declaration | Statement |
| --- | --- |
| `filtrationι t K n p` | The natural transformation `F^p(K, -) ⟶ shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op K)` whose component at `B` is the inclusion of the subgroup `F^p(K, B)` of `Hom(K, B⟦n⟧)`. |
| `filtrationι_app_hom_apply` | The component at `B` sends `f ∈ F^p(K, B)` to `f` viewed in `ShiftedHom K B n` (`simp` lemma, by definition). |
| `filtrationMapOfLE t K n hpq` | For `hpq : p ≤ q`, the natural transformation `F^q(K, -) ⟶ F^p(K, -)` whose component at `B` is the inclusion `F^q(K, B) ≤ F^p(K, B)` (`filtration_le_of_le`, Mathlib's `AddSubgroup.inclusion`). |
| `filtrationMapOfLE_app_hom_apply` | The component sends `f` to `AddSubgroup.inclusion (filtration_le_of_le hpq) f` (`simp` lemma, by definition). |
| `gradedπ t K n p` | The natural transformation `F^p(K, -) ⟶ gr^p(K, -)` whose component at `B` is the quotient map `F^p(K, B) → F^p(K, B) / F^{p+1}(K, B)`. |
| `gradedπ_app_hom_apply` | The component sends `f` to its class `QuotientAddGroup.mk f` (`simp` lemma, by definition). |

## Proofs

- The functor laws of `filtrationFunctor` and `gradedFunctor` are
  `filtrationPostcomp_id`, `filtrationPostcomp_comp`, `gradedPostcomp_id` and
  `gradedPostcomp_comp` of `HyperextAbutmentNaturality`, transported along
  `AddCommGrpCat.hom_ext`.
- The functor laws of the precomposition functors are `filtrationPrecomp_id`,
  `filtrationPrecomp_comp`, `gradedPrecomp_id` and `gradedPrecomp_comp`; the
  composite `φ ≫ φ'` in `Cᵒᵖ` is the composite `φ'.unop ≫ φ.unop` in `C`, which
  is the order in which `filtrationPrecomp_comp` is stated.
- The naturality of the transformations in `filtrationBifunctor` and
  `gradedBifunctor` is `filtrationPrecomp_comp_filtrationPostcomp` and
  `gradedPrecomp_comp_gradedPostcomp` (pre- and postcomposition commute). The
  functor laws of the bifunctors follow componentwise (`NatTrans.ext`) from
  those of the precomposition functors.
- The naturality squares of `filtrationι`, `filtrationMapOfLE` and `gradedπ`
  hold by `rfl`: in each case both composites send `f` to `f ≫ ψ⟦n⟧'`, viewed
  in `ShiftedHom K B' n`, in `F^p(K, B')` or as a class in `gr^p(K, B')`.

## Provenance and interpretation

The definitions and proofs are ours, assembled from Mathlib and the Library.
Packaging the functorial maps of `HyperextAbutmentNaturality` as functors is a
derived construction; the scope note of that module recorded that the maps
were not yet packaged as Mathlib `Functor` objects. These functors let a
presheaf of coefficient objects `B` (for instance, automorphic forms of
varying level placed in degree `0` of a derived category) be composed with
`filtrationFunctor` or `gradedFunctor`, giving the filtration steps and
graded pieces of the abutment as presheaves of additive groups.

No literature was consulted for this module beyond the passage of Harris 1999
recorded in `HyperextAbutmentNaturality` (Proposition 4.10, the equivariance of
the spectral sequences as the level varies), which motivates naturality but is
not formalized here.

## Scope

- Only functors and natural transformations to additive groups are defined.
  No linearity over a coefficient ring, group action or equivariance appears.
- The graded functor is not identified with page terms of
  `hyperextSpectralSequence`, and the inclusion and projection maps are not
  assembled into short exact sequences of functors.
- The bifunctors are functorial in `K` and `B` separately and jointly, but no
  statement is made about their behaviour under shifts or exact triangles.

Dependencies: `Langlands.Cohomology.HyperextAbutmentNaturality` and
Mathlib's `Mathlib.CategoryTheory.Preadditive.Yoneda.Basic`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
