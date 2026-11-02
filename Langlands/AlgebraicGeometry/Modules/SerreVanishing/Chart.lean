import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Iterate
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Mul
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity

/-! # Local charts of iterated twisting by a line bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.SchemeModule.SectionClearing
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

section Strip

variable (T : X.Opens) (L : X.Modules)
  (e : L.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)

/-- After pulling back to a trivializing open, right multiplication by `σ` becomes
multiplication by the coefficient of `σ` in the trivialization. -/
lemma pullback_twistMul_comp (σ : structureSheaf X ⟶ L) (M : X.Modules)
    {R : T.toScheme.Modules} (Θ : (Scheme.Modules.pullback T.ι).obj M ≅ R) :
    (Scheme.Modules.pullback T.ι).map ((tensorRightUnitor M).inv ≫ tensorMap (𝟙 M) σ) ≫
      pullbackTensorComparisonApp T.ι M L ≫ tensorMap Θ.hom (pullbackTriv T L e).hom ≫
        (tensorRightUnitor R).hom =
    Θ.hom ≫ (unitEndCoefficient (chartMulOf T L e σ) ⊤ • 𝟙 R) := by
  have hU := pullbackTensorRightUnitor T.toScheme X T.ι M
  have hA : tensorMap (𝟙 ((Scheme.Modules.pullback T.ι).obj M)) (pullbackUnitIso T.ι).hom ≫
      tensorMap (𝟙 ((Scheme.Modules.pullback T.ι).obj M)) (pullbackUnitIso T.ι).inv =
      𝟙 _ := by
    rw [tensorMap_comp, Iso.hom_inv_id, Category.id_comp]
    exact (tensorFunctor _).map_id _
  have hU' : (Scheme.Modules.pullback T.ι).map (tensorRightUnitor M).inv ≫
      pullbackTensorComparisonApp T.ι M (structureSheaf X) =
      (tensorRightUnitor ((Scheme.Modules.pullback T.ι).obj M)).inv ≫
        tensorMap (𝟙 ((Scheme.Modules.pullback T.ι).obj M)) (pullbackUnitIso T.ι).inv := by
    calc _ = (Scheme.Modules.pullback T.ι).map (tensorRightUnitor M).inv ≫
          (pullbackTensorComparisonApp T.ι M (structureSheaf X) ≫
            tensorMap (𝟙 ((Scheme.Modules.pullback T.ι).obj M)) (pullbackUnitIso T.ι).hom ≫
            (tensorRightUnitor ((Scheme.Modules.pullback T.ι).obj M)).hom) ≫
          (tensorRightUnitor ((Scheme.Modules.pullback T.ι).obj M)).inv ≫
            tensorMap (𝟙 ((Scheme.Modules.pullback T.ι).obj M))
              (pullbackUnitIso T.ι).inv := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, hA]
          exact congrArg
            (fun g => (Scheme.Modules.pullback T.ι).map (tensorRightUnitor M).inv ≫ g)
            (Category.comp_id _).symm
      _ = _ := by
          rw [hU, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat := pullbackTensorComparisonApp_naturality T.ι (𝟙 M) σ
  have hT : tensorMap (𝟙 ((Scheme.Modules.pullback T.ι).obj M)) (pullbackUnitIso T.ι).inv ≫
      tensorMap ((Scheme.Modules.pullback T.ι).map (𝟙 M))
        ((Scheme.Modules.pullback T.ι).map σ) ≫
      tensorMap Θ.hom (pullbackTriv T L e).hom =
      tensorMap Θ.hom (𝟙 (structureSheaf T.toScheme)) ≫
        tensorMap (𝟙 R) (chartMulOf T L e σ) := by
    rw [tensorMap_comp, tensorMap_comp, tensorMap_comp, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Category.comp_id]
    rfl
  rw [Functor.map_comp, Category.assoc, reassoc_of% hnat, reassoc_of% hU', reassoc_of% hT,
    tensorMap_id_unitEnd, ← Category.assoc (tensorMap Θ.hom _), tensorRightUnitor_naturality,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- One strip: an identification of pullbacks extends across a further twist by `L`. -/
def stripStep {A B : X.Modules}
    (Θ : (Scheme.Modules.pullback T.ι).obj A ≅ (Scheme.Modules.pullback T.ι).obj B) :
    (Scheme.Modules.pullback T.ι).obj (tensorObj A L) ≅ (Scheme.Modules.pullback T.ι).obj B :=
  SectionClearing.pullbackTensorIso T A L ≪≫ tensorMapIso Θ (pullbackTriv T L e) ≪≫
    tensorRightUnitor ((Scheme.Modules.pullback T.ι).obj B)

variable (s : GlobalSections L) (Z : X.Modules)

/-- Identification of the pulled-back twists of `Z` with the pullback of `Z`, from a
trivialization of `L`. -/
def stripIso : (m : ℕ) →
    ((Scheme.Modules.pullback T.ι).obj ((twistIter L m).obj Z) ≅
      (Scheme.Modules.pullback T.ι).obj Z)
  | 0 => Iso.refl ((Scheme.Modules.pullback T.ι).obj Z)
  | m + 1 => stripStep T L e (stripIso m)

/-- In the identifications `stripIso`, multiplication by `s` is multiplication by the
coefficient of `s`. -/
lemma stripIso_succ (m : ℕ) :
    (Scheme.Modules.pullback T.ι).map ((stepNat L s m).app Z) ≫ (stripIso T L e Z (m + 1)).hom =
      (stripIso T L e Z m).hom ≫
        (unitEndCoefficient (chartMulOf T L e (sectionHom L s)) ⊤ • 𝟙 _) :=
  pullback_twistMul_comp T L e (sectionHom L s) ((twistIter L m).obj Z) (stripIso T L e Z m)

/-- The restricted twists of `Z` identified with the restriction of `Z`. -/
def twistChartIso (m : ℕ) : ((twistIter L m).obj Z).restrict T.ι ≅ Z.restrict T.ι :=
  (Scheme.Modules.restrictFunctorIsoPullback T.ι).app _ ≪≫ stripIso T L e Z m ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback T.ι).app Z).symm

lemma twistChartIso_succ (m : ℕ) :
    (Scheme.Modules.restrictFunctor T.ι).map ((stepNat L s m).app Z) ≫
        (twistChartIso T L e Z (m + 1)).hom =
      (twistChartIso T L e Z m).hom ≫
        (unitEndCoefficient (chartMulOf T L e (sectionHom L s)) ⊤ • 𝟙 _) := by
  simp only [twistChartIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback T.ι).hom.naturality,
    Category.assoc, reassoc_of% (stripIso_succ T L e s Z m)]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

end Strip

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
