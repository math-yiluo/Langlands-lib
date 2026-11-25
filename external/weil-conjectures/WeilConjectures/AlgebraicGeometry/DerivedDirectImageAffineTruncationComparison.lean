/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local truncation comparison for unbounded direct image

Source: Stacks Project, perfect.tex, Tag 08D5, final paragraph
(blueprint: lem-pc-derived-direct-image-affine-truncation-comparison).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

-- The site equivalence transports quasi-coherent presentations; compare the proved helper
-- in Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian.
open CategoryTheory.Limits TopologicalSpace in
private theorem isQuasicoherent_overEquiv (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv (X := X) U).functor.obj M).IsQuasicoherent := by
  have (V : TopologicalSpace.Opens ↥U) :
      (Over.post (X := V) U.overEquivalence.symm.functor).IsContinuous
        ((Opens.grothendieckTopology ↥U).over V)
        (((Opens.grothendieckTopology ↥X).over U).over
          (U.overEquivalence.inverse.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _

/-- On an affine open, a sufficiently low canonical truncation induces an
isomorphism on any fixed higher direct image. The assertion concerns the actual
canonical map, and does not assert quasi-coherence of either higher direct image.
Source: Stacks Project, perfect.tex, Tag 08D5, final paragraph; cohomology.tex,
Tag 08BS for open restriction
(blueprint: lem-pc-derived-direct-image-affine-truncation-comparison).

Proof:
1. Put V = f^-1(U). The induced morphism V -> U is qcqs, by base change along
   the open immersion U -> Y. The affine scheme U is quasi-compact.
2. Exact restriction of E to V has quasi-coherent cohomology. Choose a
   K-injective representative of E; kInjective_of_restrict_open says that
   its restriction is K-injective. Use schemeDerivedDirectImage_openRestriction
   to identify the restriction of Rf_*E with R(f|V)_*(E|V), naturally in E.
3. Apply exists_schemeDerivedDirectImage_uniform_truncation_bound, its second
   clause, to V -> U, E|V and q, and choose n at least the resulting n0.
   This makes the q-th higher direct image of the truncation projection an iso.
4. Exact restriction commutes with canonical truncation and its projection,
   by the standard t-structure, and with homology. Transport the iso of step 3
   through these natural comparisons. It is precisely the displayed map.
-/
theorem exists_isIso_schemeHigherDirectImage_truncGE_over_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (q : ℤ) (U : Y.affineOpens) :
    ∃ n : ℤ, IsIso
      ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U.1).map
        ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ (-n)).app E))) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U.1).toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.1.toScheme.toRingedSpace))
  let rX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ U.1)
  let eX := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ U.1)))
    (D := SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U.1).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ U.1))
  let rY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U.1
  let eY := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U.1))
    (D := SheafOfModules.{u} (moduleRings U.1.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U.1)
  let RX := rX ⋙ eX
  let RY := rY ⋙ eY
  have : rX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : rY.Additive := Functor.additive_of_preserves_binary_products _
  have : eY.Additive := Functor.additive_of_preserves_binary_products _
  have : RX.Additive := inferInstance
  have : RY.Additive := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteLimits RX :=
    CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  have : CategoryTheory.Limits.PreservesFiniteColimits RX :=
    CategoryTheory.Limits.comp_preservesFiniteColimits _ _
  have : CategoryTheory.Limits.PreservesFiniteLimits RY :=
    CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  have : CategoryTheory.Limits.PreservesFiniteColimits RY :=
    CategoryTheory.Limits.comp_preservesFiniteColimits _ _
  have hR : schemeDerivedQCohProperty (f ⁻¹ᵁ U.1).toScheme
      (RX.mapDerivedCategory.obj E) := by
    intro i
    have hq := hE i
    let := hq
    have : (rX.obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)).IsQuasicoherent := by
      exact SheafOfModules.isQuasicoherent_over.{u, u, u} _ _
    have : ((RX.obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))).IsQuasicoherent :=
      isQuasicoherent_overEquiv X (f ⁻¹ᵁ U.1) _
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (f ⁻¹ᵁ U.1).toScheme.toRingedSpace)).prop_of_iso
        ((RX.mapDerivedCategoryHomologyFunctorIso i).app E) this
  let ER : schemeDerivedQCohCategory (f ⁻¹ᵁ U.1).toScheme := ⟨_, hR⟩
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨n, hn⟩ :=
    (exists_schemeDerivedDirectImage_uniform_truncation_bound (f ∣_ U.1)).2 ER q
  refine ⟨n, ?_⟩
  have hi := hn n le_rfl
  let π := (DerivedCategory.TStructure.t.truncGEπ (-n)).app E
  let H := schemeHigherDirectImage (f ∣_ U.1) q
  let c := (RX.mapDerivedCategoryTruncGEIso (-n)).inv.app E
  have hc : IsIso c := inferInstance
  have : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE (-n) ⋙ RX.mapDerivedCategory).obj E)
      (-n) := RX.isGE_mapDerivedCategory_obj
        ((DerivedCategory.TStructure.t.truncGE (-n)).obj E) (-n)
  have hπ : (DerivedCategory.TStructure.t.truncGEπ (-n)).app
      (RX.mapDerivedCategory.obj E) ≫ c = RX.mapDerivedCategory.map π := by
    change _ ≫ DerivedCategory.TStructure.t.descTruncGE _ (-n) = _
    exact DerivedCategory.TStructure.t.π_descTruncGE _ _
  have hlocal : IsIso (H.map (RX.mapDerivedCategory.map π)) := by
    rw [← hπ, H.map_comp]
    infer_instance
  let e := Classical.choice (schemeDerivedDirectImage_openRestriction f U.1)
  have hderived : IsIso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.1.toScheme.toRingedSpace)) q).map
          (RY.mapDerivedCategory.map ((schemeDerivedDirectImage f).map π))) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor _ q)) π).2 hlocal
  have hglobal : IsIso (RY.map ((schemeHigherDirectImage f q).map π)) :=
    (NatIso.isIso_map_iff (RY.mapDerivedCategoryHomologyFunctorIso q)
      ((schemeDerivedDirectImage f).map π)).2 hderived
  change IsIso (rY.map ((schemeHigherDirectImage f q).map π))
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ eY hglobal _

end AlgebraicGeometry
