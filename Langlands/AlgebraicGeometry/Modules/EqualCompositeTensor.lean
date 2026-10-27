import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorStatement

/-! # Tensor compatibility of equal-composite pullback comparisons -/

universe u
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule Langlands.SchemeModule.RigidifiedModule

/-- Generalized composition comparisons respect the actual tensor comparison. -/
lemma compHom_tensor {U X Y : Scheme.{u}} (a : U ⟶ X) (p : X ⟶ Y) (q : U ⟶ Y)
    (h : a ≫ p = q) (M N : Y.Modules) :
    compHom a p q h (tensorObj M N) ≫ pullbackTensorComparisonApp q M N =
      (Scheme.Modules.pullback a).map (pullbackTensorComparisonApp p M N) ≫
        pullbackTensorComparisonApp a ((Scheme.Modules.pullback p).obj M)
          ((Scheme.Modules.pullback p).obj N) ≫
        tensorMap (compHom a p q h M) (compHom a p q h N) := by
  subst q
  simpa only [compHom_rfl] using pullbackTensorComposition U X Y a p M N

/-- The equal-composite comparison intertwines the two iterated tensor comparisons. -/
lemma equalCompositeIso_tensor {U X Y : Scheme.{u}} (p : X ⟶ Y) (a b : U ⟶ X)
    (h : a ≫ p = b ≫ p) (M N : Y.Modules) :
    (equalCompositeIso p a b h (tensorObj M N)).hom ≫
        (Scheme.Modules.pullback b).map (pullbackTensorComparisonApp p M N) ≫
        pullbackTensorComparisonApp b ((Scheme.Modules.pullback p).obj M)
          ((Scheme.Modules.pullback p).obj N) =
      (Scheme.Modules.pullback a).map (pullbackTensorComparisonApp p M N) ≫
        pullbackTensorComparisonApp a ((Scheme.Modules.pullback p).obj M)
          ((Scheme.Modules.pullback p).obj N) ≫
        tensorMap (equalCompositeIso p a b h M).hom
          (equalCompositeIso p a b h N).hom := by
  let e := (tensorFunctor U).mapIso
    (((Scheme.Modules.pullbackComp b p).app M).prod
      ((Scheme.Modules.pullbackComp b p).app N))
  apply (cancel_mono e.hom).mp
  change _ ≫ tensorMap ((Scheme.Modules.pullbackComp b p).hom.app M)
      ((Scheme.Modules.pullbackComp b p).hom.app N) =
    _ ≫ tensorMap ((Scheme.Modules.pullbackComp b p).hom.app M)
      ((Scheme.Modules.pullbackComp b p).hom.app N)
  simp only [Category.assoc]
  rw [← pullbackTensorComposition U X Y b p M N]
  rw [equalCompositeIso_hom_eq_compHom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [compHom_tensor]
  rw [tensorMap_comp]
  simp [equalCompositeIso_hom_eq_compHom]

/-- The tensor unit contracts a tensor of two endomorphisms to their composite. -/
lemma tensorUnitMap_hom {X : Scheme.{u}}
    (e d : structureSheaf X ⟶ structureSheaf X) :
    tensorMap e d ≫ (tensorLeftUnitor (structureSheaf X)).hom =
      (tensorLeftUnitor (structureSheaf X)).hom ≫ e ≫ d := by
  have he : tensorMap e (𝟙 (structureSheaf X)) ≫
        (tensorLeftUnitor (structureSheaf X)).hom =
      (tensorLeftUnitor (structureSheaf X)).hom ≫ e := by
    rw [tensorUnitors_equal]
    exact tensorRightUnitor_naturality e
  calc
    _ = (tensorMap e (𝟙 (structureSheaf X)) ≫
        tensorMap (𝟙 (structureSheaf X)) d) ≫
          (tensorLeftUnitor (structureSheaf X)).hom := by
      rw [tensorMap_comp]
      simp
    _ = _ := by
      rw [Category.assoc, tensorLeftUnitor_naturality, ← Category.assoc, he, Category.assoc]

/-- The canonical tensor and unit comparisons respect the contraction `O ⊗ O → O`. -/
lemma pullbackTensor_unit {X Y : Scheme.{u}} (a : X ⟶ Y) :
    pullbackTensorComparisonApp a (structureSheaf Y) (structureSheaf Y) ≫
        tensorMap (pullbackUnitIso a).hom (pullbackUnitIso a).hom ≫
          (tensorLeftUnitor (structureSheaf X)).hom =
      (Scheme.Modules.pullback a).map (tensorLeftUnitor (structureSheaf Y)).hom ≫
        (pullbackUnitIso a).hom := by
  have ht : tensorMap (pullbackUnitIso a).hom (pullbackUnitIso a).hom =
      tensorMap (pullbackUnitIso a).hom
          (𝟙 ((Scheme.Modules.pullback a).obj (structureSheaf Y))) ≫
        tensorMap (𝟙 (structureSheaf X)) (pullbackUnitIso a).hom := by
    rw [tensorMap_comp]
    erw [Category.comp_id]
  rw [ht, Category.assoc, tensorLeftUnitor_naturality]
  have hu := pullbackTensorLeftUnitor X Y a (structureSheaf Y)
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ (pullbackUnitIso a).hom) hu

/-- Tensor two actual pullback trivializations through the canonical tensor comparison. -/
def tensorPullbackTrivialization
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) {M N : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ structureSheaf X)
    (β : (Scheme.Modules.pullback p).obj N ≅ structureSheaf X) :
    (Scheme.Modules.pullback p).obj (tensorObj M N) ≅ structureSheaf X := by
  letI := preservation p
  exact (asIso (pullbackTensorComparison p)).app (M, N) ≪≫
    (tensorFunctor X).mapIso (α.prod β) ≪≫ tensorLeftUnitor (structureSheaf X)

/-- Pulling the tensor trivialization back and normalizing the unit is the tensor
of the two normalized pulled-back trivializations. -/
lemma tensorPullbackTrivialization_pullback_hom
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {U X Y : Scheme.{u}} (p : X ⟶ Y) (a : U ⟶ X) {M N : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ structureSheaf X)
    (β : (Scheme.Modules.pullback p).obj N ≅ structureSheaf X) :
    (Scheme.Modules.pullback a).map (tensorPullbackTrivialization preservation p α β).hom ≫
        (pullbackUnitIso a).hom =
      (Scheme.Modules.pullback a).map (pullbackTensorComparisonApp p M N) ≫
        pullbackTensorComparisonApp a ((Scheme.Modules.pullback p).obj M)
          ((Scheme.Modules.pullback p).obj N) ≫
        tensorMap ((Scheme.Modules.pullback a).map α.hom ≫ (pullbackUnitIso a).hom)
          ((Scheme.Modules.pullback a).map β.hom ≫ (pullbackUnitIso a).hom) ≫
        (tensorLeftUnitor (structureSheaf U)).hom := by
  simp only [tensorPullbackTrivialization, Iso.trans_hom, Iso.app_hom,
    asIso_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change _ = _ ≫ _ ≫ tensorMap (_ ≫ _) (_ ≫ _) ≫ _
  rw [← tensorMap_comp]
  simp only [Category.assoc]
  change (Scheme.Modules.pullback a).map (pullbackTensorComparisonApp p M N) ≫
      (Scheme.Modules.pullback a).map (tensorMap α.hom β.hom) ≫
      (Scheme.Modules.pullback a).map (tensorLeftUnitor (structureSheaf X)).hom ≫
      (pullbackUnitIso a).hom = _
  rw [← reassoc_of% (pullbackTensorComparisonApp_naturality a α.hom β.hom)]
  rw [pullbackTensor_unit]


/-- The canonical comparison intertwines normalized trivializations with the
transported unit automorphism. -/
lemma equalCompositeUnitAut_intertwine {U X Y : Scheme.{u}}
    (p : X ⟶ Y) (a b : U ⟶ X) (h : a ≫ p = b ≫ p) {M : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ structureSheaf X) :
    (equalCompositeIso p a b h M).hom ≫
        (Scheme.Modules.pullback b).map α.hom ≫ (pullbackUnitIso b).hom =
      ((Scheme.Modules.pullback a).map α.hom ≫ (pullbackUnitIso a).hom) ≫
        (equalCompositeUnitAut p a b h α).hom := by
  rw [equalCompositeUnitAut_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, α.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Tensoring actual pullback trivializations multiplies their normalized
canonical actions on the structure module. -/
lemma equalCompositeUnitAut_tensor
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {U X Y : Scheme.{u}} (p : X ⟶ Y) (a b : U ⟶ X)
    (h : a ≫ p = b ≫ p) {M N : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ structureSheaf X)
    (β : (Scheme.Modules.pullback p).obj N ≅ structureSheaf X) :
    equalCompositeUnitAut p a b h (tensorPullbackTrivialization preservation p α β) =
      equalCompositeUnitAut p a b h α ≪≫ equalCompositeUnitAut p a b h β := by
  let γ := tensorPullbackTrivialization preservation p α β
  let φ := (Scheme.Modules.pullback a).mapIso γ ≪≫ pullbackUnitIso a
  apply Iso.ext
  apply (cancel_epi φ.hom).mp
  change ((Scheme.Modules.pullback a).map γ.hom ≫ (pullbackUnitIso a).hom) ≫ _ =
    ((Scheme.Modules.pullback a).map γ.hom ≫ (pullbackUnitIso a).hom) ≫ _
  rw [← equalCompositeUnitAut_intertwine]
  rw [show γ = tensorPullbackTrivialization preservation p α β from rfl,
    tensorPullbackTrivialization_pullback_hom,
    tensorPullbackTrivialization_pullback_hom]
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% (equalCompositeIso_tensor p a b h M N)]
  rw [reassoc_of% (tensorMap_comp (equalCompositeIso p a b h M).hom
      ((Scheme.Modules.pullback b).map α.hom ≫ (pullbackUnitIso b).hom)
      (equalCompositeIso p a b h N).hom
      ((Scheme.Modules.pullback b).map β.hom ≫ (pullbackUnitIso b).hom)),
    equalCompositeUnitAut_intertwine, equalCompositeUnitAut_intertwine,
    ← tensorMap_comp]
  simp only [Category.assoc]
  rw [tensorUnitMap_hom]

end Langlands.Scheme.Modules
