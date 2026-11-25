/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.GenericTranspose.ExternalRHomAdjunctionNaturality
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Naturality of the external evaluation transpose

Source: Stacks 08J9 and 0A90
(blueprint: lem-pur-external-rhom-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC vC uD vD uB vB
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale.ExternalRHom
/-- Pull an evaluation through the constant and tensor comparisons before specializing
categories. Source: Stacks 08J9 and 0G7E
(blueprint: lem-pur-external-rhom-evaluation-naturality). -/
noncomputable def pullEvaluationOf
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    {B : Type uB} [Category.{vB} B]
    (F : C ⥤ D) (c : B ⥤ C) (d : B ⥤ D) (α : d ≅ c ⋙ F)
    (δ : ∀ E H : C, F.obj E ⊗ F.obj H ⟶ F.obj (E ⊗ H))
    (E K : C) (Q : B) (t : c.obj Q ⊗ E ⟶ K) :
    d.obj Q ⊗ F.obj E ⟶ F.obj K :=
  (α.hom.app Q ▷ F.obj E) ≫ δ (c.obj Q) E ≫ F.map t

/-- Tensor two evaluations with the Koszul interchange before specializing categories.
Source: Stacks 08J9 and 0A90 (blueprint: lem-pur-external-rhom-evaluation-naturality). -/
noncomputable def externalEvaluationOf
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (c : B ⥤ C)
    (δ : (Functor.postcompose₂.obj c).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ C).obj c).obj c).obj (curriedTensor C))
    (Q R : B) (E H K L' : C)
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj R ⊗ H ⟶ L') :
    c.obj (Q ⊗ R) ⊗ (E ⊗ H) ⟶ K ⊗ L' :=
  (((δ.app Q).app R) ▷ (E ⊗ H)) ≫
    tensorμ (c.obj Q) (c.obj R) E H ≫ (t ⊗ₘ t')

/-- The external transpose with its adjunction left abstract. This is the same
external evaluation composite, with no extra choices of maps.
Source: Stacks 08J9 and 0A90 (blueprint: lem-pur-external-rhom-evaluation-naturality). -/
noncomputable def pairingOf
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (c : B ⥤ C) (h : Cᵒᵖ ⥤ C ⥤ B)
    (tr : ∀ (E K : C) (Q : B), (c.obj Q ⊗ E ⟶ K) → (Q ⟶ (h.obj (op E)).obj K))
    (δ : (Functor.postcompose₂.obj c).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ C).obj c).obj c).obj (curriedTensor C))
    (Q R : B) (E H K L' : C)
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj R ⊗ H ⟶ L') :
    Q ⊗ R ⟶ (h.obj (op (E ⊗ H))).obj (K ⊗ L') :=
  tr (E ⊗ H) (K ⊗ L') (Q ⊗ R) (externalEvaluationOf c δ Q R E H K L' t t')

namespace GenericTranspose
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] {B : Type uB} [Category.{vB} B]
  {c : B ⥤ C} {s : C ⥤ B} (a : c ⊣ s)
private theorem externalEvaluation_naturality
    {B C : Type*} [Category B] [MonoidalCategory B] [Category C] [MonoidalCategory C]
    [BraidedCategory C] (c : B ⥤ C)
    (δ : (Functor.postcompose₂.obj c).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ C).obj c).obj c).obj (curriedTensor C))
    {Q Q' R R' : B} {E E' H H' K K' L L' : C}
    (x : Q ⟶ Q') (y : R ⟶ R') (f : E' ⟶ E) (g : H' ⟶ H)
    (k : K ⟶ K') (l : L ⟶ L')
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj Q' ⊗ E' ⟶ K')
    (u : c.obj R ⊗ H ⟶ L) (u' : c.obj R' ⊗ H' ⟶ L')
    (ht : (c.map x ▷ E') ≫ t' = (c.obj Q ◁ f) ≫ t ≫ k)
    (hu : (c.map y ▷ H') ≫ u' = (c.obj R ◁ g) ≫ u ≫ l) :
    (c.map (x ⊗ₘ y) ▷ (E' ⊗ H')) ≫
        externalEvaluationOf c δ Q' R' E' H' K' L' t' u' =
      (c.obj (Q ⊗ R) ◁ (f ⊗ₘ g)) ≫
        externalEvaluationOf c δ Q R E H K L t u ≫ (k ⊗ₘ l) := by
  unfold externalEvaluationOf
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc,
    ← Functor.OplaxMonoidal.app_app_comp_tensorHom δ x y,
    comp_whiskerRight_assoc, tensorμ_natural_left_assoc]
  rw [tensorHom_comp_tensorHom, ht, hu]
  simp only [← tensorHom_comp_tensorHom]
  rw [← tensorμ_natural_right_assoc]
  have hδ : (δ.app Q).app R ▷ (E' ⊗ H') ≫ (c.obj Q ⊗ c.obj R) ◁ (f ⊗ₘ g) =
      c.obj (Q ⊗ R) ◁ (f ⊗ₘ g) ≫ (δ.app Q).app R ▷ (E ⊗ H) :=
    (whisker_exchange ((δ.app Q).app R) (f ⊗ₘ g)).symm
  rw [reassoc_of% hδ]

theorem pairing_naturality [MonoidalCategory B]
    (δ : (Functor.postcompose₂.obj c).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ C).obj c).obj c).obj (curriedTensor C))
    {Q Q' R R' : B} {E E' H H' K K' L L' : C}
    (x : Q ⟶ Q') (y : R ⟶ R') (f : E' ⟶ E) (g : H' ⟶ H)
    (k : K ⟶ K') (l : L ⟶ L')
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj Q' ⊗ E' ⟶ K')
    (u : c.obj R ⊗ H ⟶ L) (u' : c.obj R' ⊗ H' ⟶ L')
    (ht : (c.map x ▷ E') ≫ t' = (c.obj Q ◁ f) ≫ t ≫ k)
    (hu : (c.map y ▷ H') ≫ u' = (c.obj R ◁ g) ≫ u ≫ l) :
    (x ⊗ₘ y) ≫ tr a (E' ⊗ H') (K' ⊗ L') (Q' ⊗ R')
        (externalEvaluationOf c δ Q' R' E' H' K' L' t' u') =
      tr a (E ⊗ H) (K ⊗ L) (Q ⊗ R)
          (externalEvaluationOf c δ Q R E H K L t u) ≫
        s.map ((MonoidalClosed.pre (f ⊗ₘ g)).app (K ⊗ L)) ≫
        s.map ((ihom (E' ⊗ H')).map (k ⊗ₘ l)) := by
  rw [parameter, ← Category.assoc, source, target]
  congr 1
  simpa only [Category.assoc] using
    externalEvaluation_naturality c δ x y f g k l t t' u u' ht hu

private theorem pullEvaluation_naturality
    {B C D : Type*} [Category B] [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    (c : B ⥤ C) (d : B ⥤ D) (α : d ≅ c ⋙ F)
    {Q Q' : B} {E E' K K' : C} (x : Q ⟶ Q') (f : E' ⟶ E) (k : K ⟶ K')
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj Q' ⊗ E' ⟶ K')
    (ht : (c.map x ▷ E') ≫ t' = (c.obj Q ◁ f) ≫ t ≫ k) :
    (d.map x ▷ F.obj E') ≫
        pullEvaluationOf F c d α (Functor.LaxMonoidal.μ F) E' K' Q' t' =
      (d.obj Q ◁ F.map f) ≫
        pullEvaluationOf F c d α (Functor.LaxMonoidal.μ F) E K Q t ≫ F.map k := by
  unfold pullEvaluationOf
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, α.hom.naturality, comp_whiskerRight_assoc]
  dsimp only [Functor.comp_map]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, ht,
    F.map_comp, F.map_comp, ← Functor.LaxMonoidal.μ_natural_right_assoc]
  have hα : α.hom.app Q ▷ F.obj E' ≫ F.obj (c.obj Q) ◁ F.map f =
      d.obj Q ◁ F.map f ≫ α.hom.app Q ▷ F.obj E :=
    (whisker_exchange (α.hom.app Q) (F.map f)).symm
  rw [reassoc_of% hα]

end GenericTranspose
end AlgebraicGeometry.Etale.ExternalRHom

namespace AlgebraicGeometry.Etale.ExternalRHom.GenericExternal

universe uX vX uY vY uP vP
variable {B : Type uB} [Category.{vB} B] [MonoidalCategory B]
  {X : Type uX} [Category.{vX} X] [MonoidalCategory X] [BraidedCategory X]
  [MonoidalClosed X]
  {Y : Type uY} [Category.{vY} Y] [MonoidalCategory Y] [BraidedCategory Y]
  [MonoidalClosed Y]
  {P : Type uP} [Category.{vP} P] [MonoidalCategory P] [BraidedCategory P]
  [MonoidalClosed P]
  {cx : B ⥤ X} {sx : X ⥤ B} (ax : cx ⊣ sx)
  {cy : B ⥤ Y} {sy : Y ⥤ B} (ay : cy ⊣ sy)
  {cp : B ⥤ P} {sp : P ⥤ B} (ap : cp ⊣ sp)
  (F : X ⥤ P) [F.LaxMonoidal] (G : Y ⥤ P) [G.LaxMonoidal]
  (α : cp ≅ cx ⋙ F) (β : cp ≅ cy ⋙ G)
  (δ : (Functor.postcompose₂.obj cp).obj (curriedTensor B) ⟶
    (((Functor.whiskeringLeft₂ P).obj cp).obj cp).obj (curriedTensor P))

/-- The same external evaluation transpose with the three closed categories abstract.
Source: Stacks 08J9 and 0A90
(blueprint: lem-pur-external-rhom-evaluation-naturality). -/
noncomputable def pairing (E K : X) (H L : Y) :
    sx.obj ((ihom E).obj K) ⊗ sy.obj ((ihom H).obj L) ⟶
      sp.obj ((ihom (F.obj E ⊗ G.obj H)).obj (F.obj K ⊗ G.obj L)) :=
  GenericTranspose.tr ap (F.obj E ⊗ G.obj H) (F.obj K ⊗ G.obj L) _
    (externalEvaluationOf cp δ _ _ (F.obj E) (G.obj H) (F.obj K) (G.obj L)
      (pullEvaluationOf F cx cp α (Functor.LaxMonoidal.μ F) E K _
        (GenericTranspose.ev ax E K))
      (pullEvaluationOf G cy cp β (Functor.LaxMonoidal.μ G) H L _
        (GenericTranspose.ev ay H L)))

/-- The exact four-variance square for the canonical external evaluation transpose.
Source: Stacks 08J9 and 0A90
(blueprint: lem-pur-external-rhom-evaluation-naturality). -/
def NaturalityAt {E E' K K' : X} {H H' L L' : Y}
    (f : E' ⟶ E) (g : H' ⟶ H) (k : K ⟶ K') (l : L ⟶ L') : Prop :=
  ((sx.map ((MonoidalClosed.pre f).app K) ≫ sx.map ((ihom E').map k)) ⊗ₘ
      (sy.map ((MonoidalClosed.pre g).app L) ≫ sy.map ((ihom H').map l))) ≫
      pairing ax ay ap F G α β δ E' K' H' L' =
    pairing ax ay ap F G α β δ E K H L ≫
      sp.map ((MonoidalClosed.pre (F.map f ⊗ₘ G.map g)).app (F.obj K ⊗ G.obj L)) ≫
      sp.map ((ihom (F.obj E' ⊗ G.obj H')).map (F.map k ⊗ₘ G.map l))

/-- Evaluation, pullback constraints and the Koszul interchange are natural in all factors.
Source: Stacks 08J9 and 0A90
(blueprint: lem-pur-external-rhom-evaluation-naturality). -/
theorem naturality {E E' K K' : X} {H H' L L' : Y}
    (f : E' ⟶ E) (g : H' ⟶ H) (k : K ⟶ K') (l : L ⟶ L') :
    NaturalityAt ax ay ap F G α β δ f g k l := by
  unfold NaturalityAt pairing
  apply GenericTranspose.pairing_naturality ap δ
  · apply GenericTranspose.pullEvaluation_naturality
    exact GenericTranspose.ev_naturality ax f k
  · apply GenericTranspose.pullEvaluation_naturality
    exact GenericTranspose.ev_naturality ay g l

end AlgebraicGeometry.Etale.ExternalRHom.GenericExternal
