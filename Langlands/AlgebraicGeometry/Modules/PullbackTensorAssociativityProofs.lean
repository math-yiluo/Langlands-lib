import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorAssociativity
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs

noncomputable section
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

private lemma left_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (M N P : Y.Modules) :
    localizedPullbackTensorComparisonApp f (M ⊗ N) P ≫
      (localizedPullbackTensorComparisonApp f M N ⊗ₘ 𝟙 ((Scheme.Modules.pullback f).obj P)) ≫
      ((localizedTensorIso X ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom ⊗ₘ 𝟙 ((Scheme.Modules.pullback f).obj P)) ≫
      (localizedTensorIso X (tensorObj ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) ((Scheme.Modules.pullback f).obj P)).hom =
    (Scheme.Modules.pullback f).map
      (((localizedTensorIso Y M N).hom ⊗ₘ 𝟙 P) ≫
        (localizedTensorIso Y (tensorObj M N) P).hom) ≫
      pullbackTensorComparisonApp f (tensorObj M N) P ≫
      tensorMap (pullbackTensorComparisonApp f M N) (𝟙 ((Scheme.Modules.pullback f).obj P)) := by
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [localizedPullbackTensorComparisonApp_eq, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← localizedTensorIso_inv_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  have ht := tensorMap_comp
    ((Scheme.Modules.pullback f).map (localizedTensorIso Y M N).hom)
    (pullbackTensorComparisonApp f M N)
    (𝟙 ((Scheme.Modules.pullback f).obj P)) (𝟙 ((Scheme.Modules.pullback f).obj P))
  simp only [Category.id_comp] at ht
  rw [← ht, ← Category.assoc (pullbackTensorComparisonApp f (M ⊗ N) P)]
  have hn := pullbackTensorComparisonApp_naturality f (localizedTensorIso Y M N).hom (𝟙 P)
  rw [(Scheme.Modules.pullback f).map_id] at hn
  rw [← hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  rw [← localizedTensorIso_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]

private lemma right_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (M N P : Y.Modules) :
    localizedPullbackTensorComparisonApp f M (N ⊗ P) ≫
      (𝟙 ((Scheme.Modules.pullback f).obj M) ⊗ₘ localizedPullbackTensorComparisonApp f N P) ≫
      (𝟙 ((Scheme.Modules.pullback f).obj M) ⊗ₘ
        (localizedTensorIso X ((Scheme.Modules.pullback f).obj N)
          ((Scheme.Modules.pullback f).obj P)).hom) ≫
      (localizedTensorIso X ((Scheme.Modules.pullback f).obj M)
        (tensorObj ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj P))).hom =
    (Scheme.Modules.pullback f).map
      ((𝟙 M ⊗ₘ (localizedTensorIso Y N P).hom) ≫
        (localizedTensorIso Y M (tensorObj N P)).hom) ≫
      pullbackTensorComparisonApp f M (tensorObj N P) ≫
      tensorMap (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackTensorComparisonApp f N P) := by
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [localizedPullbackTensorComparisonApp_eq, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← localizedTensorIso_inv_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  have ht := tensorMap_comp
    (𝟙 ((Scheme.Modules.pullback f).obj M)) (𝟙 ((Scheme.Modules.pullback f).obj M))
    ((Scheme.Modules.pullback f).map (localizedTensorIso Y N P).hom)
    (pullbackTensorComparisonApp f N P)
  simp only [Category.id_comp] at ht
  rw [← ht, ← Category.assoc (pullbackTensorComparisonApp f M (N ⊗ P))]
  have hn := pullbackTensorComparisonApp_naturality f (𝟙 M) (localizedTensorIso Y N P).hom
  rw [(Scheme.Modules.pullback f).map_id] at hn
  rw [← hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  rw [← localizedTensorIso_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]

/-- The explicit equation transfers to the fixed localized tensor comparison. -/
lemma localizedPullbackTensorAssociativity_of_explicit
    (h : ExplicitPullbackTensorAssociativityStatement.{u}) :
    LocalizedPullbackTensorAssociativityStatement.{u} := by
  intro X Y f M N P
  simp only [← tensorHom_id, ← id_tensorHom]
  apply (cancel_mono
    ((𝟙 ((Scheme.Modules.pullback f).obj M) ⊗ₘ
      (localizedTensorIso X ((Scheme.Modules.pullback f).obj N)
        ((Scheme.Modules.pullback f).obj P)).hom) ≫
      (localizedTensorIso X ((Scheme.Modules.pullback f).obj M)
        (tensorObj ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj P))).hom)).1
  simp only [Category.assoc]
  rw [← localizedTensorIso_associativity]
  rw [reassoc_of% left_comparison f M N P, right_comparison]
  rw [← Functor.map_comp_assoc, ← localizedTensorIso_associativity]
  simp only [Functor.map_comp, Category.assoc]
  rw [h X Y f M N P]

/-- The canonical pullback comparison respects the localized tensor associator. -/
theorem localizedPullbackTensorAssociativity :
    LocalizedPullbackTensorAssociativityStatement.{u} :=
  localizedPullbackTensorAssociativity_of_explicit explicitPullbackTensorAssociativity

/-- Associativity for the canonical pullback comparison in both tensor conventions. -/
theorem pullbackTensorAssociativity :
    PullbackTensorAssociativityStatement.{u} :=
  ⟨localizedPullbackTensorAssociativity, explicitPullbackTensorAssociativity⟩

end Langlands.Scheme.Modules
