import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleComparison

/-! # Universal bundles under composite restriction of the base -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PresheafLineBundle

variable {S U V : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- The standard slice comparisons identify successive and direct restriction. -/
def baseChangeCompIso (p : U ⟶ S) (q : V ⟶ U) (r : V ⟶ S)
    (h : q ≫ p = r) :
    (Over.map q).op ⋙ (Over.map p).op ⋙ F ≅ (Over.map r).op ⋙ F :=
  (Functor.associator (Over.map q).op (Over.map p).op F).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (Over.mapComp q p)) F ≪≫
    Functor.isoWhiskerRight (NatIso.op (Over.mapCongr (q ≫ p) r h)).symm F

/-- A supplied representation of direct restriction also represents successive
restriction, with exactly the same parameter scheme. -/
def baseChangeCompRepresentation (p : U ⟶ S) (q : V ⟶ U) (r : V ⟶ S)
    (h : q ≫ p = r) {M : Over V}
    (e : ((Over.map r).op ⋙ F).RepresentableBy M) :
    ((Over.map q).op ⋙ (Over.map p).op ⋙ F).RepresentableBy M :=
  e.ofIso (baseChangeCompIso p q r h).symm

/-- Direct and successive restriction retain the same actual universal bundle
under the standard comparison of their supplied representing data. -/
def baseChangeCompUniversalIso (L : PresheafLineBundle F)
    (p : U ⟶ S) (q : V ⟶ U) (r : V ⟶ S) (h : q ≫ p = r)
    {M : Over V} (e : ((Over.map r).op ⋙ F).RepresentableBy M) :
    ((L.baseChange p).baseChange q).universal
        (baseChangeCompRepresentation p q r h e) ≅
      (L.baseChange r).universal e := by
  let a : (Over.map p).obj ((Over.map q).obj M) ⟶ (Over.map r).obj M :=
    (Over.mapComp q p).inv.app M ≫ (Over.mapCongr (q ≫ p) r h).hom.app M
  have ha : a.left = 𝟙 M.left := by simp [a]
  have hx : F.map a.op (e.homEquiv (𝟙 M)) =
      (baseChangeCompRepresentation p q r h e).homEquiv (𝟙 M) := by
    simp [baseChangeCompRepresentation, baseChangeCompIso,
      Functor.RepresentableBy.ofIso, a, Functor.map_comp]
  let c := L.pullbackIso a (e.homEquiv (𝟙 M))
    ((baseChangeCompRepresentation p q r h e).homEquiv (𝟙 M)) hx
  have c' : (LineBundle.pullback (𝟙 M.left)).obj
      ((L.baseChange r).universal e) ≅
      ((L.baseChange p).baseChange q).universal
        (baseChangeCompRepresentation p q r h e) := by
    simpa only [ha, universal, baseChange] using c
  exact c'.symm ≪≫ (LineBundle.pullbackId M.left).app _

end Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
