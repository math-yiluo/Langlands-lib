import Langlands.AlgebraicGeometry.Modules.BiCech.TensorFrame
import Langlands.AlgebraicGeometry.Modules.RestrictionIsoSections
import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle

/-! # Local tensor contractions on pure sections -/

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules
open Langlands.SchemeModule.SectionClearing
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

variable {S : Scheme.{u}}

/-- The image of a pure tensor of sections in the actual sheaf tensor. -/
abbrev pureSection (M N : S.Modules) (W : S.Opens) (m : Γ(M, W)) (n : Γ(N, W)) :
    Γ(tensorObj M N, W) :=
  Langlands.AlgebraicGeometry.Modules.BiCech.tsec (A := M) (B := N) m n

lemma pureSection_restrict (M N : S.Modules) {V W : S.Opens} (h : W ≤ V)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    (tensorObj M N).presheaf.map (homOfLE h).op (pureSection M N V m n) =
      pureSection M N W (M.presheaf.map (homOfLE h).op m)
        (N.presheaf.map (homOfLE h).op n) :=
  (PresheafOfModules.naturality_apply (tensorSheafifyUnit M N)
    (homOfLE h).op (m ⊗ₜ[Γ(S, V)] n)).symm

lemma tensorMap_pureSection {M M' N N' : S.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (W : S.Opens) (m : Γ(M, W)) (n : Γ(N, W)) :
    (tensorMap f g).app W (pureSection M N W m n) =
      pureSection M' N' W (f.app W m) (g.app W n) := by
  exact (congrArg (fun k => k.app (op W) (m ⊗ₜ[Γ(S, W)] n))
    (tensorSheafifyUnit_naturality f g)).symm

lemma tensorRightUnitor_hom_eq (M : S.Modules) :
    (tensorRightUnitor M).hom = (tensorHomEquiv _ _ _).symm (ρ_ M.val).hom :=
  ((sheafifyAdjunction S).homEquiv_counit _ _ _).symm

lemma tensorRightUnitor_pureSection (M : S.Modules) (W : S.Opens)
    (m : Γ(M, W)) (a : Γ(S, W)) :
    (tensorRightUnitor M).hom.app W (pureSection M (structureSheaf S) W m a) = a • m := by
  have h := congrArg (fun k => k.app (op W) (m ⊗ₜ[Γ(S, W)] a))
    (tensorSheafifyUnit_comp_tensorHomEquiv_symm M (structureSheaf S) M (ρ_ M.val).hom)
  rw [← tensorRightUnitor_hom_eq] at h
  exact h

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules

variable {S : Scheme.{u}} {M N : S.Modules} {U V : S.Opens}

/-- The given line chart with its codomain expressed as a restricted original module. -/
def lineRestrictionIso
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    N.restrict U.ι ≅ (structureSheaf S).restrict U.ι :=
  t ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm

/-- The line chart acts as an actual linear equivalence on sections of any smaller open. -/
def lineCoordinates
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : S.Opens) (h : V ≤ U) : Γ(N, V) ≃ₗ[Γ(S, V)] Γ(S, V) :=
  { (overRestrictionIso (lineRestrictionIso t)).hom.val.app
      (op (Over.mk (homOfLE h))) |>.hom with
    invFun := (overRestrictionIso (lineRestrictionIso t)).inv.val.app
      (op (Over.mk (homOfLE h)))
    left_inv := fun x => congrArg
      (fun k => k.val.app (op (Over.mk (homOfLE h))) x)
      (overRestrictionIso (lineRestrictionIso t)).hom_inv_id
    right_inv := fun x => congrArg
      (fun k => k.val.app (op (Over.mk (homOfLE h))) x)
      (overRestrictionIso (lineRestrictionIso t)).inv_hom_id }

lemma lineCoordinates_eq_modE
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (x : Γ(N, V)) :
    lineCoordinates t V h x = SerreVanishing.modE (lineRestrictionIso t) V h x :=
  overRestrictionIso_hom_app _ h x

/-- On the trivializing subscheme, contraction evaluates a pure tensor by the line chart. -/
lemma tensorRestrictionTrivialization_pureSection
    (M : S.Modules)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : U.toScheme.Opens) (m : Γ(M.restrict U.ι, W)) (n : Γ(N.restrict U.ι, W)) :
    (tensorRestrictionTrivialization M N U t).hom.app W
      ((restrictTensorHom U M N).app W
        (pureSection (M.restrict U.ι) (N.restrict U.ι) W m n)) =
      (show Γ(U.toScheme, W) from t.hom.app W n) • m := by
  have := isIso_restrictTensorHom U M N
  have hc : restrictTensorHom U M N ≫ (tensorRestrictionTrivialization M N U t).hom =
      tensorMap (𝟙 (M.restrict U.ι)) t.hom ≫
        (tensorRightUnitor (M.restrict U.ι)).hom := by
    dsimp only [tensorRestrictionTrivialization, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
    simp only [asIso_inv, IsIso.hom_inv_id_assoc]
    rfl
  have ha := congrArg (fun k => k.app W
    (pureSection (M.restrict U.ι) (N.restrict U.ι) W m n)) hc
  change (tensorRestrictionTrivialization M N U t).hom.app W
      ((restrictTensorHom U M N).app W
        (pureSection (M.restrict U.ι) (N.restrict U.ι) W m n)) =
    (tensorRightUnitor (M.restrict U.ι)).hom.app W
      ((tensorMap (𝟙 (M.restrict U.ι)) t.hom).app W
        (pureSection (M.restrict U.ι) (N.restrict U.ι) W m n)) at ha
  rw [ha, tensorMap_pureSection]
  exact tensorRightUnitor_pureSection (M.restrict U.ι) W m
    (show Γ(U.toScheme, W) from t.hom.app W n)

end Langlands.AlgebraicGeometry.Modules
