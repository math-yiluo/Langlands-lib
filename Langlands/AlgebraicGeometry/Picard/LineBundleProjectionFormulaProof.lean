import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaStatement
import Langlands.AlgebraicGeometry.Picard.LocallyFreeTensorInvertibleProof
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Proof of the line-bundle projection formula -/

noncomputable section

universe u v u' v'

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

private def tensorInverseEquivalence
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (L N : C) (e : L ⊗ N ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft N) (tensorLeft L)
    ((leftUnitorNatIso C).symm ≪≫
      (tensoringLeft C).mapIso e.symm ≪≫ tensorLeftTensor L N)
    ((tensorLeftTensor N L).symm ≪≫
      (tensoringLeft C).mapIso ((β_ N L) ≪≫ e) ≪≫ leftUnitorNatIso C)

private def tensorInverseProjectionIso
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] (adj : F ⊣ G)
    (L N : C) (e : L ⊗ N ≅ 𝟙_ C) :
    G ⋙ tensorLeft L ≅ tensorLeft (F.obj L) ⋙ G := by
  let E := tensorInverseEquivalence L N e
  let eD : F.obj L ⊗ F.obj N ≅ 𝟙_ D :=
    Functor.Monoidal.μIso F L N ≪≫ F.mapIso e ≪≫
      (Functor.Monoidal.εIso F).symm
  let E' := tensorInverseEquivalence (F.obj L) (F.obj N) eD
  let a := E.toAdjunction.comp adj
  let b := adj.comp E'.toAdjunction
  exact (a.ofNatIsoLeft (Functor.Monoidal.commTensorLeft F N).symm).rightAdjointUniq b

open Langlands.Scheme.Modules

/-- The projection isomorphism obtained from tensor-inverse adjunctions. -/
def lineBundleProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : LineBundle Y) (M : X.Modules) :
    Langlands.Scheme.Modules.tensorObj L.obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f).obj
        (Langlands.Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj L.obj) M) := by
  let h := locallyFreeRankOneTensorInvertible Y L.obj L.property
  let N := h.choose
  let e := h.choose_spec.some
  exact (localizedTensorIso Y L.obj ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
    (tensorInverseProjectionIso (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
      (Scheme.Modules.pullbackPushforwardAdjunction f) L.obj N e).app M ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (localizedTensorIso X ((Scheme.Modules.pullback f).obj L.obj) M)

/-- The projection formula holds for every actual line bundle and module sheaf. -/
theorem lineBundleProjectionFormula : LineBundleProjectionFormulaStatement.{u} := by
  intro X Y f L M
  exact ⟨lineBundleProjectionIso f L M⟩

end Langlands.AlgebraicGeometry.Picard
