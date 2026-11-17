import Langlands.AlgebraicGeometry.FlatGlobalSectionsProduct
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Product comparisons for canonical affinization over a PID -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open CategoryTheory.Limits hiding prodComparison terminalComparison

namespace Langlands.AlgebraicGeometry.FlatPidAffinizationProducts

variable {R : Type u} [CommRing R]

/-- The affinization functor has exactly the prescribed structural ring map. -/
theorem obj_hom (X : Over (Spec (CommRingCat.of R))) :
    ((algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)).obj X).hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop) := rfl

/-- Affinization maps morphisms by the spectrum of their global-section maps. -/
theorem map_left {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    ((algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)).map f).left =
      Spec.map f.left.appTop := rfl

/-- Affinization preserves the terminal object over an affine base. -/
instance isIso_terminalComparison :
    IsIso (terminalComparison (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R))) := by
  have : IsIso ((Over.forget _).map
      (terminalComparison (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)))) := by
    change IsIso (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (𝟙 (Spec (CommRingCat.of R)) : _ ⟶ _).appTop))
    simp only [Scheme.Hom.id_appTop, Category.comp_id]
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget _)

variable [IsDomain R] [IsPrincipalIdealRing R]

set_option backward.isDefEq.respectTransparency false in
/-- Affinization preserves the product of flat qc separated schemes over a PID. -/
instance isIso_prodComparison (X Y : Over (Spec (CommRingCat.of R)))
    [Flat X.hom] [Flat Y.hom] [QuasiCompact X.hom] [QuasiCompact Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom] :
    IsIso (prodComparison (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)) X Y) := by
  let F := algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (FlatGlobalSectionsProduct.isPushout_appTop_pid (IsPullback.of_hasPullback X.hom Y.hom))
  have H' : IsPullback (Spec.map (pullback.fst X.hom Y.hom).appTop)
      (Spec.map (pullback.snd X.hom Y.hom).appTop)
      (F.obj X).hom (F.obj Y).hom := by
    apply H.of_iso (.refl _) (.refl _) (.refl _)
      (asIso (Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
    · simp
    · simp
    · change Spec.map X.hom.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv =
        𝟙 _ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appTop)
      simp only [Category.id_comp, Spec.map_comp]
    · change Spec.map Y.hom.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv =
        𝟙 _ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Y.hom.appTop)
      simp only [Category.id_comp, Spec.map_comp]
  have he : (prodComparison F X Y).left = H'.isoPullback.hom := by
    apply pullback.hom_ext
    · calc
        _ = (F.map (fst X Y)).left :=
          congrArg (fun k : F.obj (X ⊗ Y) ⟶ F.obj X => k.left) (prodComparison_fst F X Y)
        _ = Spec.map (pullback.fst X.hom Y.hom).appTop := rfl
        _ = _ := H'.isoPullback_hom_fst.symm
    · calc
        _ = (F.map (snd X Y)).left :=
          congrArg (fun k : F.obj (X ⊗ Y) ⟶ F.obj Y => k.left) (prodComparison_snd F X Y)
        _ = Spec.map (pullback.snd X.hom Y.hom).appTop := rfl
        _ = _ := H'.isoPullback_hom_snd.symm
  have : IsIso ((Over.forget _).map (prodComparison F X Y)) := by
    change IsIso (prodComparison F X Y).left
    rw [he]
    exact Iso.isIso_hom _
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The actual canonical isomorphism from the affinization of a product to the
product of the affinizations. -/
def affinizationProductIso (X Y : Over (Spec (CommRingCat.of R)))
    [Flat X.hom] [Flat Y.hom] [QuasiCompact X.hom] [QuasiCompact Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom] :
    (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)).obj (X ⊗ Y) ≅
      (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)).obj X ⊗
      (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)).obj Y :=
  asIso (prodComparison (algΓ (CommRingCat.of R) ⋙ algSpec (CommRingCat.of R)) X Y)

end Langlands.AlgebraicGeometry.FlatPidAffinizationProducts
