import Langlands.GroupScheme.RelativeUnipotent.LinearChartDescent
import Langlands.AlgebraicGeometry.Modules.GeometricQuasicoherentDescent
import Langlands.AlgebraicGeometry.Modules.FiniteLocalBasisDescent

/-! # Descent of point charts with an actual linear module cocycle -/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open Langlands.AlgebraicGeometry.Modules
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S X : Scheme.{u}} {p : X ⟶ S} {F : X.Modules}

/-- Finite local bases transport along an actual module-sheaf isomorphism. -/
lemma IsFiniteLocallyFree.of_iso {Y : Scheme.{u}} {A B : Y.Modules}
    (hA : IsFiniteLocallyFree A) (e : A ≅ B) : IsFiniteLocallyFree B := by
  let a := Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames.choose hA
  let b : Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames B := {
    I := a.I
    opens := a.opens
    covers := a.covers
    rank := a.rank
    frame i := a.frame i ≪≫
      (SheafOfModules.overFunctor Y.ringCatSheaf (a.opens i)).mapIso e }
  exact b.hasFiniteLocalBasis

/-- Charts into a module on the cover, compatible with an actual linear cocycle. -/
structure LinearModuleCharts (D : Datum p F) (V : GroupScheme S) where
  equiv : ∀ (T : Over S) (a : T.left ⟶ X) (_ha : a ≫ p = T.hom),
    (T ⟶ V.X) ≃* Multiplicative
      (GlobalSections ((Scheme.Modules.pullback a).obj F))
  natural : ∀ (T W : Over S) (b : W ⟶ T) (a : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (x : T ⟶ V.X),
    (equiv W (b.left ≫ a) (by rw [Category.assoc, ha, Over.w b]) (b ≫ x)).toAdd =
      ((Scheme.Modules.pullbackComp b.left a).hom.app F).app ⊤
        (pullbackSection b.left ((Scheme.Modules.pullback a).obj F)
          (equiv T a ha x).toAdd)
  compatible : ∀ (T : Over S) (a c : T.left ⟶ X)
    (ha : a ≫ p = T.hom) (hc : c ≫ p = T.hom) (x : T ⟶ V.X),
    (D.θ T.left a c (ha.trans hc.symm)).hom.app ⊤ (equiv T a ha x).toAdd =
      (equiv T c hc x).toAdd

namespace LinearModuleCharts

variable {D : Datum p F} {V : GroupScheme S} (C : LinearModuleCharts D V)
  {M : S.Modules} (Q : Str D (𝟙 S) M)

/-- The actual module comparison for a lifted test. -/
def chartIso (T : Over S) (a : T.left ⟶ X) (ha : a ≫ p = T.hom) :
    (Scheme.Modules.pullback T.hom).obj M ≅ (Scheme.Modules.pullback a).obj F :=
  Q.γ T.left a T.hom (by simpa only [Category.comp_id] using ha.symm)

/-- The additive equivalence induced by an actual module-sheaf isomorphism. -/
def sectionIsoEquiv {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B) :
    GlobalSections A ≃+ GlobalSections B :=
  AddEquiv.ofBijective (e.hom.app ⊤).hom (ConcreteCategory.bijective_of_isIso _)

lemma chartIso_sectionPullback (T W : Over S) (b : W ⟶ T)
    (a : T.left ⟶ X) (ha : a ≫ p = T.hom)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    (chartIso Q W (b.left ≫ a) (by rw [Category.assoc, ha, Over.w b])).hom.app ⊤
        (sectionPullback M b s) =
      ((Scheme.Modules.pullbackComp b.left a).hom.app F).app ⊤
        (pullbackSection b.left ((Scheme.Modules.pullback a).obj F)
          ((chartIso Q T a ha).hom.app ⊤ s)) := by
  have hγ := Q.nat T.left W.left b.left a T.hom
    (by simpa only [Category.comp_id] using ha.symm)
    (b.left ≫ a) W.hom
    (by simp only [Category.comp_id, Category.assoc, ha, Over.w b])
    rfl (Over.w b)
  change ((compIso b.left T.hom W.hom (Over.w b) M).hom ≫
      (chartIso Q W (b.left ≫ a) _).hom).app ⊤
      (pullbackSection b.left _ s) = _
  dsimp only [chartIso]
  rw [hγ]
  simp only [tr, Iso.hom_inv_id_assoc]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ← pullbackSection_naturality]
  rw [compIso_rfl]
  rfl

/-- Transport the charts along an effective structure's actual module comparisons. -/
def toLocalSectionCharts : LocalSectionCharts p V M where
  equiv T a ha := (C.equiv T a ha).trans
    (AddEquiv.toMultiplicative (sectionIsoEquiv (chartIso Q T a ha).symm))
  natural T W b a ha x := by
    apply (ConcreteCategory.bijective_of_isIso
      ((chartIso Q W (b.left ≫ a) _).hom.app ⊤)).injective
    change (chartIso Q W (b.left ≫ a) _).hom.app ⊤
        ((chartIso Q W (b.left ≫ a) _).inv.app ⊤
          (C.equiv W (b.left ≫ a) _ (b ≫ x)).toAdd) =
      (chartIso Q W (b.left ≫ a) _).hom.app ⊤
        (sectionPullback M b ((chartIso Q T a ha).inv.app ⊤
          (C.equiv T a ha x).toAdd))
    simp only [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
    rw [chartIso_sectionPullback Q T W b a ha, C.natural T W b a ha x]
    simp only [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.inv_hom_id, Scheme.Modules.Hom.id_app, Category.comp_id]
    rfl
  independent T a c ha hc x := by
    change (chartIso Q T a ha).inv.app ⊤ (C.equiv T a ha x).toAdd =
      (chartIso Q T c hc).inv.app ⊤ (C.equiv T c hc x).toAdd
    apply (ConcreteCategory.bijective_of_isIso ((chartIso Q T c hc).hom.app ⊤)).injective
    have hγ := Q.coc T.left a c T.hom
      (by simpa only [Category.comp_id] using ha.symm)
      (by simpa only [Category.comp_id] using hc.symm) (ha.trans hc.symm)
    change ((chartIso Q T a ha).inv ≫ (chartIso Q T c hc).hom).app ⊤
        (C.equiv T a ha x).toAdd =
      ((chartIso Q T c hc).inv ≫ (chartIso Q T c hc).hom).app ⊤
        (C.equiv T c hc x).toAdd
    rw [Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
    change ((chartIso Q T a ha).inv ≫ (Q.γ T.left c T.hom _).hom).app ⊤ _ = _
    rw [← hγ]
    simp only [chartIso, Iso.inv_hom_id_assoc]
    exact C.compatible T a c ha hc x

include Q in
/-- Finite local bases of the cover module descend to an effective module. -/
lemma finiteLocallyFree_of_str [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hF : IsFiniteLocallyFree F) : IsFiniteLocallyFree M :=
  hasFiniteLocalBasis_of_pullback_fppf p M
    (hF.of_iso (GeometricQuasicoherentDescent.pullbackIsoOfStr D Q).symm)

include C in
/-- Compatible actual linear charts on an affine fppf cover give the exact
vector-bundle additive predicate, without an effectivity premise. -/
lemma isVectorBundleAdditive [IsAffineHom p] [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p]
    [IsAffineHom V.X.hom] [Smooth V.X.hom]
    (hF : IsFiniteLocallyFree F) : IsVectorBundleAdditive V := by
  have : F.IsQuasicoherent := by
    obtain ⟨q, hq, _⟩ := hF
    let := hq
    exact q.quasiCoherentData.isQuasicoherent
  obtain ⟨M, hM, ⟨Q⟩⟩ := GeometricQuasicoherentDescent.exists_str D (𝟙 S)
  let := hM
  exact (C.toLocalSectionCharts Q).isVectorBundleAdditive (finiteLocallyFree_of_str Q hF)

end LinearModuleCharts
end Langlands.GroupScheme.RelativeUnipotent
