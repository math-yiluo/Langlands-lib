/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.DerivedModulePullbackComparison
import WeilConjectures.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover

/-! # Canonical relatively flat module base change

Source: Stacks Project, Tag 0A1D, and the finite affine Cech proof of
`lemma-coherent-base-change-invertible-sheaves--2`.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem isIso_of_open_restrictions
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) {K L : schemeDerivedCategory Y} (φ : K ⟶ L)
    (I : Type u) (U : I → Y.Opens)
    (hcover : ∀ y : Y, ∃ i : I, y ∈ U i)
    (hlocal : ∀ i : I,
      IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ)) : IsIso φ := by
  apply (DerivedCategory.isIso_iff _ φ).mpr
  intro n
  have hU : ⨆ i, U i = ⊤ := by
    apply le_antisymm le_top
    intro y _
    obtain ⟨i, hi⟩ := hcover y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  apply (sheaf_module_isIso_iff_isIso_over_open_cover.{u, u, u}
    Y.toRingedSpace I U hU _ _
    ((DerivedCategory.homologyFunctor _ n).map φ)).mpr
  intro i
  have := hlocal i
  have hhom : IsIso
      ((schemeOpenRestriction Y (U i)).map
        ((DerivedCategory.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      ((schemeOpenRestriction Y (U i)).mapDerivedCategoryHomologyFunctorIso n) φ).mpr
      (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ))
        exact Functor.map_isIso _ _)
  let F := (Scheme.Modules.overEquiv (U i)).functor
  have : IsIso (F.map (((DerivedCategory.homologyFunctor _ n).map φ).over (U i))) :=
    hhom
  exact isIso_of_reflects_iso _ F

/-- Relative flatness makes the canonical base-change map with ordinary module target
invertible, for any cartesian square. This does not assert that the derived-to-ordinary
pullback comparison itself is invertible.

Source: Stacks Project, Tag 0A1D; blueprint `lemma-coherent-base-change-invertible-sheaves--2`,
Steps 1--5, and `lemma-coherent-base-change-invertible-sheaves--2`.
(blueprint: lemma-coherent-base-change-invertible-sheaves--2).

Proof: Take the left-derived counit of tensor pullback at G[0] and compose it with
singleMapHomologicalComplex to obtain c. This is the comparison characterized by
IsDerivedModulePullbackComparison. On affine opens of S and S', choose a finite
ordered affine cover of the inverse image in X. Separatedness makes its intersections
affine. The finite alternating Cech complex computes Rf_*G. Relative flatness makes
all its terms flat over the base ring; hence its derived pullback is ordinary tensor
pullback. The affine section-pullback formula identifies this tensor complex with
the Cech complex for the pulled-back module. The comparison respects restrictions
and hence differentials. By baseChangeMap_cech the resulting isomorphism is exactly
schemeDerivedBaseChangeMap followed by Rf'_*c. Check invertibility on cohomology
sheaves locally to conclude globally. For a general cartesian square, identify X'
with the chosen pullback using its unique projection-preserving isomorphism. The
pullback-composition comparisons and their adjunction mates commute with this
identification, so the formula and invertibility transport. The empty cover computes
zero on an empty scheme, so no nonemptiness assumption is needed. -/
theorem exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g) [(Scheme.Modules.tensorPullback g').Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f) :
    ∃ c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G),
      IsDerivedModulePullbackComparison g' G c ∧
        IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
          (schemeDerivedDirectImage f').map c) := by
  obtain ⟨c, hc⟩ := exists_isDerivedModulePullbackComparison.{u, w} g' G
  refine ⟨c, hc, ?_⟩
  let I := {p : S.affineOpens × S'.affineOpens | p.2.1 ≤ g ⁻¹ᵁ p.1.1}
  let U : I → S'.Opens := fun p ↦ p.1.2.1
  have hcover : ∀ y : S', ∃ i : I, y ∈ U i := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g.base y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
      S'.isBasis_affineOpens.exists_subset_of_mem_open hyV (g ⁻¹ᵁ V).2
    exact ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hyW⟩
  apply isIso_of_open_restrictions S' _ I U hcover
  intro p
  exact canonicalModuleBaseChange_isIso_on_affine_open_of_affine_cases
    (fun f _ _ g _ G _ hflat c hc ↦
      canonicalModuleBaseChange_isIso_affine_of_isFlatOver f g G hflat c hc)
    f g g' f' sq G hflat c hc p.1.1 p.1.2 p.2

end AlgebraicGeometry
