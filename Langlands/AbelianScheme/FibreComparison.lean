import Langlands.AbelianScheme.GroupScheme

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {T U : Over S} {V : Scheme.{u}}

/-- The canonical comparison of iterated slice pullbacks in a commuting base diagram. -/
private def fibreComparisonNatTrans (h : T ⟶ U) (s : V ⟶ T.left) :
    Over.pullback T.hom ⋙ Over.pullback s ⟶
      Over.pullback U.hom ⋙ Over.pullback (s ≫ h.left) where
  app X := Over.homMk
    (pullback.lift
      (pullback.lift
        (pullback.fst (pullback.snd X.hom T.hom) s ≫ pullback.fst X.hom T.hom)
        (pullback.snd (pullback.snd X.hom T.hom) s ≫ (s ≫ h.left))
        (by simp only [Category.assoc, Over.w];
            rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]))
      (pullback.snd (pullback.snd X.hom T.hom) s)
      (by simp)) (by simp)
  naturality {X Y} f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [Category.assoc]
    · simp

/-- The canonical group-scheme comparison between the two iterated base changes. -/
def fibreComparison (G : GroupScheme S) (h : T ⟶ U) (s : V ⟶ T.left) :
    (baseChange s).obj ((baseChange T.hom).obj G) ⟶
      (baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj G) :=
  (Functor.mapGrpCompIso.inv.app G) ≫
    (Functor.mapGrpNatTrans (fibreComparisonNatTrans h s)).app G ≫
      (Functor.mapGrpCompIso.hom.app G)

@[reassoc (attr := simp)] theorem fibreComparison_fst
    (G : GroupScheme S) (h : T ⟶ U) (s : V ⟶ T.left) :
    (fibreComparison G h s).hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom U.hom) (s ≫ h.left) ≫
          pullback.fst G.X.hom U.hom =
      pullback.fst (pullback.snd G.X.hom T.hom) s ≫ pullback.fst G.X.hom T.hom := by
  simp [fibreComparison, fibreComparisonNatTrans, Functor.mapGrpNatTrans,
    Functor.mapGrpCompIso]

@[reassoc (attr := simp)] theorem fibreComparison_snd
    (G : GroupScheme S) (h : T ⟶ U) (s : V ⟶ T.left) :
    (fibreComparison G h s).hom.hom.left ≫
        pullback.snd (pullback.snd G.X.hom U.hom) (s ≫ h.left) =
      pullback.snd (pullback.snd G.X.hom T.hom) s := by
  exact (fibreComparison G h s).hom.hom.w

end Langlands.GroupScheme
