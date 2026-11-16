import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeTransport
import Langlands.AlgebraicGeometry.RelativeDifferentialsMapsCoherence
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Differential square maps pulled back to compatible sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Scheme

open Langlands.SchemeModule.RigidifiedModule (compHom compHom_assoc compHom_rfl compHom_id_left)

variable {X Y Z S T U : AlgebraicGeometry.Scheme.{u}}

/-- The canonical comparison of pullbacks along compatible sections. -/
def sectionPullbackSquareIso (g : X ⟶ Y) (b : T ⟶ S)
    (eX : T ⟶ X) (eY : S ⟶ Y) (h : eX ≫ g = b ≫ eY) :
    pullback eY ⋙ pullback b ≅ pullback g ⋙ pullback eX :=
  pullbackComp b eY ≪≫ (pullbackCongr h).symm ≪≫ (pullbackComp eX g).symm

lemma sectionPullbackSquareIso_hom_app (g : X ⟶ Y) (b : T ⟶ S)
    (eX : T ⟶ X) (eY : S ⟶ Y) (h : eX ≫ g = b ≫ eY) (M : Y.Modules) :
    (sectionPullbackSquareIso g b eX eY h).hom.app M =
      compHom b eY (eX ≫ g) h.symm M ≫ (pullbackComp eX g).inv.app M := by
  rfl

/-- Section pullback comparisons compose with the canonical comparisons on both sides. -/
lemma sectionPullbackSquareIso_comp
    (g : X ⟶ Y) (h : Y ⟶ Z) (b : U ⟶ T) (c : T ⟶ S)
    (eX : U ⟶ X) (eY : T ⟶ Y) (eZ : S ⟶ Z)
    (hg : eX ≫ g = b ≫ eY) (hh : eY ≫ h = c ≫ eZ) (M : Z.Modules) :
    (pullback b).map ((sectionPullbackSquareIso h c eY eZ hh).hom.app M) ≫
        (sectionPullbackSquareIso g b eX eY hg).hom.app ((pullback h).obj M) =
      (pullbackComp b c).hom.app ((pullback eZ).obj M) ≫
        (sectionPullbackSquareIso (g ≫ h) (b ≫ c) eX eZ
          (by rw [← Category.assoc, hg, Category.assoc, hh, ← Category.assoc])).hom.app M ≫
            (pullback eX).map ((pullbackComp g h).inv.app M) := by
  have hE : b ≫ eY ≫ h = eX ≫ g ≫ h := by
    rw [← Category.assoc, ← hg, Category.assoc]
  have hcomp : eX ≫ g ≫ h = (b ≫ c) ≫ eZ := by
    rw [← Category.assoc, hg, Category.assoc, hh, ← Category.assoc]
  have e1 := compHom_assoc eX g h (eX ≫ g) (g ≫ h) (eX ≫ g ≫ h)
    rfl rfl (Category.assoc _ _ _) rfl M
  have e2 := compHom_assoc b eY h (eX ≫ g) (eY ≫ h) (eX ≫ g ≫ h)
    hg.symm rfl (Category.assoc _ _ _) hE M
  have e3 := compHom_assoc b c eZ (b ≫ c) (eY ≫ h) (eX ≫ g ≫ h)
    rfl hh.symm hcomp.symm hE M
  simp only [compHom_rfl] at e1 e2 e3
  apply (cancel_mono ((pullback eX).map ((pullbackComp g h).hom.app M) ≫
    (pullbackComp eX (g ≫ h)).hom.app M)).mp
  simp only [sectionPullbackSquareIso_hom_app, Functor.map_comp, Category.assoc]
  rw [← e1]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [e2]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← e3, e1]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

/-- Over the same base, remove the base identity pullback. -/
lemma sectionPullbackSquareIso_id_base
    (g : X ⟶ Y) (eX : S ⟶ X) (eY : S ⟶ Y) (h : eX ≫ g = eY) (M : Y.Modules) :
    (sectionPullbackSquareIso g (𝟙 S) eX eY
        (by simpa only [Category.id_comp] using h)).hom.app M =
      (pullbackId S).hom.app ((pullback eY).obj M) ≫
        (pullbackCongr h).inv.app M ≫ (pullbackComp eX g).inv.app M := by
  subst eY
  rw [sectionPullbackSquareIso_hom_app, compHom_id_left]
  simp only [pullbackCongr, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.assoc]
  rfl

/-- The differential square map restricted to compatible sections over a base map. -/
def sectionDifferentialsSquareMap (g : X ⟶ Y) (b : T ⟶ S)
    {fX : X ⟶ T} {fY : Y ⟶ S} (w : g ≫ fY = fX ≫ b)
    (eX : T ⟶ X) (eY : S ⟶ Y) (h : eX ≫ g = b ≫ eY) :
    (pullback b).obj ((pullback eY).obj (relativeDifferentials fY)) ⟶
      (pullback eX).obj (relativeDifferentials fX) :=
  (sectionPullbackSquareIso g b eX eY h).hom.app (relativeDifferentials fY) ≫
    (pullback eX).map (relativeDifferentialsSquareMap g b w)

/-- Over the same base, this is the usual section pullback of the differential map. -/
lemma sectionDifferentialsSquareMap_id_base
    (g : X ⟶ Y) {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX)
    (eX : S ⟶ X) (eY : S ⟶ Y) (h : eX ≫ g = eY) :
    sectionDifferentialsSquareMap g (𝟙 S)
        (by simpa only [Category.comp_id] using w) eX eY
        (by simpa only [Category.id_comp] using h) =
      (pullbackId S).hom.app ((pullback eY).obj (relativeDifferentials fY)) ≫
        (pullbackCongr h).inv.app (relativeDifferentials fY) ≫
          (pullbackComp eX g).inv.app (relativeDifferentials fY) ≫
            (pullback eX).map (relativeDifferentialsMap g w) := by
  rw [sectionDifferentialsSquareMap, sectionPullbackSquareIso_id_base g eX eY h,
    relativeDifferentialsSquareMap_id_base g w]
  simp only [Category.assoc]

/-- Sequential squares give the square of the composite, using the canonical
module pullback comparison. -/
@[reassoc]
lemma sectionDifferentialsSquareMap_comp
    (g : X ⟶ Y) (h : Y ⟶ Z) (b : U ⟶ T) (c : T ⟶ S)
    {fX : X ⟶ U} {fY : Y ⟶ T} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX ≫ b) (wh : h ≫ fZ = fY ≫ c)
    (eX : U ⟶ X) (eY : T ⟶ Y) (eZ : S ⟶ Z)
    (hg : eX ≫ g = b ≫ eY) (hh : eY ≫ h = c ≫ eZ) :
    (pullback b).map (sectionDifferentialsSquareMap h c wh eY eZ hh) ≫
        sectionDifferentialsSquareMap g b wg eX eY hg =
      (pullbackComp b c).hom.app ((pullback eZ).obj (relativeDifferentials fZ)) ≫
        sectionDifferentialsSquareMap (g ≫ h) (b ≫ c)
          (by rw [Category.assoc, wh, ← Category.assoc, wg, Category.assoc])
          eX eZ (by rw [← Category.assoc, hg, Category.assoc, hh, ← Category.assoc]) := by
  have hn := (sectionPullbackSquareIso g b eX eY hg).hom.naturality
    (relativeDifferentialsSquareMap h c wh)
  dsimp only [Functor.comp_map] at hn
  simp only [sectionDifferentialsSquareMap, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Category.assoc,
    sectionPullbackSquareIso_comp g h b c eX eY eZ hg hh]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [relativeDifferentialsSquareMap_comp]

end Langlands.Scheme
