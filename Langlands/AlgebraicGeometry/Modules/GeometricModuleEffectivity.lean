import Langlands.AlgebraicGeometry.Modules.GeometricModuleCoalgebra

/-! # Effective geometric descent for quasi-coherent modules -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules.GeometricModuleEffectivity

open GeometricModuleCoalgebra

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- Evaluation is natural in the module on the cover. -/
@[reassoc]
lemma evaluation_naturality {A B : X.Modules} (f : A ⟶ B)
    {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullback p).map ((Scheme.Modules.pushforward p).map f)) ≫
        evaluation (F := B) a b h =
      evaluation (F := A) a b h ≫ (Scheme.Modules.pullback b).map f := by
  unfold GeometricModuleCoalgebra.evaluation
  rw [equalCompositeIso_hom_naturality_assoc, ← Functor.map_comp]
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction p).counit.naturality f
  change (Scheme.Modules.pullback p).map ((Scheme.Modules.pushforward p).map f) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction p).counit.app B =
      (Scheme.Modules.pullbackPushforwardAdjunction p).counit.app A ≫ f at hn
  rw [hn, Functor.map_comp, Category.assoc]

/-- The comparison coalgebra coaction evaluates to the canonical geometric comparison. -/
lemma comparison_coaction_evaluation (M : Y.Modules)
    {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)) ≫
        evaluation (F := (Scheme.Modules.pullback p).obj M) a b h =
      (equalCompositeIso p a b h M).hom := by
  unfold GeometricModuleCoalgebra.evaluation
  erw [equalCompositeIso_hom_naturality_assoc p a b h
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)]
  rw [← Functor.map_comp,
    (Scheme.Modules.pullbackPushforwardAdjunction p).left_triangle_components M]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

variable {F : X.Modules} [IsAffineHom p] [F.IsQuasicoherent] (D : Datum p F)

/-- A morphism from a comparison coalgebra to the cocycle coalgebra satisfies every
geometric overlap equation. -/
lemma coalgebra_hom_compatible {M : Y.Modules}
    (f : (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction p)).obj M ⟶
      coalgebra D) {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).map f.f ≫ (D.θ U a b h).hom =
      (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map f.f := by
  have hf := f.h
  change (Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) ≫
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pushforward p).map f.f) =
    f.f ≫ coaction (F := F) D at hf
  have H := congrArg (fun v ↦ (Scheme.Modules.pullback a).map v ≫
    evaluation (F := F) a b h) hf
  simp only [Functor.map_comp, Category.assoc] at H
  rw [evaluation_naturality, ← Category.assoc, comparison_coaction_evaluation,
    coaction_evaluation (F := F) D a b h] at H
  exact H.symm

/-- A compatible actual pullback isomorphism gives a geometric descent structure on the base. -/
def strOfCompatibleIso {M : Y.Modules}
    (e : (Scheme.Modules.pullback p).obj M ≅ F)
    (he : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      (Scheme.Modules.pullback a).map e.hom ≫ (D.θ U a b h).hom =
        (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom) :
    Str D (𝟙 Y) M where
  γ Z g h hs :=
    (compIso g p h (by simpa only [Category.comp_id] using hs.symm) M).symm ≪≫
      (Scheme.Modules.pullback g).mapIso e
  nat Z Z' k g h hs g' h' hs' hg hh := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [tr_comp k hh hg hg, tr_compIso_inv, tr_map]
  coc Z g₁ g₂ h hs₁ hs₂ hθ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rw [he Z g₁ g₂ hθ, equalCompositeIso_hom_eq_compIso p g₁ g₂ hθ h
      (by simpa only [Category.comp_id] using hs₁.symm)
      (by simpa only [Category.comp_id] using hs₂.symm)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Every genuine geometric quasi-coherent module cocycle along an affine flat surjection
has an actual pullback isomorphism compatible on every scheme test. -/
lemma exists_compatible_iso [Flat p] [Surjective p] :
    ∃ (M : Y.Modules) (e : (Scheme.Modules.pullback p).obj M ≅ F),
      ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
        (Scheme.Modules.pullback a).map e.hom ≫ (D.θ U a b h).hom =
          (equalCompositeIso p a b h M).hom ≫
            (Scheme.Modules.pullback b).map e.hom := by
  obtain ⟨M, ⟨e⟩⟩ := exists_module_of_pullbackCoalgebra p (coalgebra D)
  let e₀ : (Scheme.Modules.pullback p).obj M ≅ F :=
    (Comonad.forget (modulePullbackDescentComonad p)).mapIso e
  exact ⟨M, e₀, fun U a b h ↦ coalgebra_hom_compatible D e.hom a b h⟩

/-- Every genuine geometric quasi-coherent module cocycle along an affine flat surjection
is effective as an ordinary module on the base. -/
lemma exists_str [Flat p] [Surjective p] :
    ∃ M : Y.Modules, Nonempty (Str D (𝟙 Y) M) := by
  obtain ⟨M, e, he⟩ := exists_compatible_iso D
  exact ⟨M, ⟨strOfCompatibleIso D e he⟩⟩

end Langlands.AlgebraicGeometry.Modules.GeometricModuleEffectivity
