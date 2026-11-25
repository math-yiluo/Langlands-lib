/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.AffineHigherDirectImageCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction

/-! # Leray comparison on affine opens of the target

Source: Stacks Project, Tag 01XK, with open restriction Tag 01E1.
(blueprint: lem-pc-affine-open-higher-direct-image-sections-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Cohomology over the inverse image of an affine open is the group of sections of
the corresponding higher direct image. Both sides use resolutions on the original X.
Source: Stacks Project, Tag 01XK; Tags 01XJ (1), 01E1 and 01F4 (2).
(blueprint: lem-pc-affine-open-higher-direct-image-sections-iso).

Proof: Restrict f to V = f^{-1}U -> U. Restriction of M is quasi-coherent. Both
quasi-compactness and quasi-separatedness are preserved by this base change. By
Tag 01XJ (1) the higher direct images of the restriction are quasi-coherent. Since U
is affine, their positive cohomology vanishes. The Leray edge of Tag 01F4 (2) is
therefore an isomorphism in every degree, as in Tag 01XK. Restriction of an injective
resolution on X to V is injective (Tag 01E1); its section complex is the original
resolution evaluated on V. Direct image and its higher derived functors commute
with restriction to U, computed by the same restricted resolution (Tag 01E4).
These two comparisons identify the edge's source and target with the displayed
objects. Degree zero gives the ordinary section equality, including empty opens. -/
theorem nonempty_affineOpen_higherDirectImage_sections_iso
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (p : ℕ) :
    Nonempty
      ((((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ U)).rightDerived p).obj M) ≅
        (RingedSpace.openModuleSections S.toRingedSpace U).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M)) :=
  by
    let V := f ⁻¹ᵁ U
    let N := (Scheme.Modules.restrictFunctor V.ι).obj M
    let g := f ∣_ U
    let : IsAffine U.toScheme := hU
    let : M.IsQuasicoherent := hM
    have hN : N.IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor V.ι M
    have : QuasiCompact g := by dsimp [g]; infer_instance
    have : QuasiSeparated g := by dsimp [g]; infer_instance
    obtain ⟨ε, _, hε⟩ := exists_lerayEdge_isIso_of_vanishing g
    have hvan (q r : ℕ) (hr : 0 < r) :
        IsZero ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace r).obj
          (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerived q).obj N)) :=
      isZero_affine_higherDirectImage_moduleCohomology g N hN q r hr
    let : IsIso ((ε p).app N) := hε N hvan p
    obtain ⟨a⟩ := nonempty_openModuleCohomology_addEquiv_restrict_H X M V p
    obtain ⟨b, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison V.toScheme p
    let eSource :
        (((RingedSpace.openModuleSections X.toRingedSpace V).rightDerived p).obj M) ≅
          (forget₂ _ AddCommGrpCat).obj
            ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace p).obj N) :=
      (a.trans (b N).symm).toAddCommGrpIso
    obtain ⟨eRestrict⟩ := nonempty_higherDirectImage_openRestriction_iso f U M p
    let G := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat
    let L : S.Modules :=
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M
    let eSections : G.obj ((Scheme.Modules.restrictFunctor U.ι).obj L) ≅
        (RingedSpace.openModuleSections S.toRingedSpace U).obj L :=
      Scheme.Modules.restrictAppIso U.ι L ⊤ ≪≫
        L.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
    exact ⟨eSource ≪≫ asIso ((ε p).app N) ≪≫ G.mapIso eRestrict ≪≫ eSections⟩

end AlgebraicGeometry
