/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # A braided comparison through a K-flat localization

Source: Stacks Project, Tags 06YS and 06YT; uniqueness of derived bifunctors.

(blueprint: lem-pur-u2-normalized-braided-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category MonoidalCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory

variable {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory A] [BraidedCategory B] [BraidedCategory D] [BraidedCategory E]
  (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
  [Q.LaxBraided] [L.LaxBraided] [F.Braided] (e : Q ⋙ G ≅ F ⋙ L)

private def squareTargetCounit :
    (((whiskeringLeft₂ E).obj Q).obj Q).obj
      ((((whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E)) ⟶
    (((whiskeringLeft₂ E).obj F).obj F).obj
      ((postcompose₂.obj L).obj (curriedTensor B)) :=
  (((whiskeringLeft₂ E).map e.hom).app (Q ⋙ G)).app (curriedTensor E) ≫
    (((whiskeringLeft₂ E).obj (F ⋙ L)).map e.hom).app (curriedTensor E) ≫
    (((whiskeringLeft₂ E).obj F).obj F).map (μNatTrans L)

omit [MonoidalCategory A] [MonoidalCategory D] [BraidedCategory A]
  [BraidedCategory D] [Q.LaxBraided] [F.Braided] in
private theorem squareTargetCounit_app (X Y : A) :
    ((squareTargetCounit Q L F G e).app X).app Y =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) := by
  dsimp [squareTargetCounit]
  rw [tensorHom_def, assoc]
  rfl

private def squareSourceCounit :
    (((whiskeringLeft₂ E).obj Q).obj Q).obj
      ((postcompose₂.obj G).obj (curriedTensor D)) ⟶
    (((whiskeringLeft₂ E).obj F).obj F).obj
      ((postcompose₂.obj L).obj (curriedTensor B)) where
  app X :=
    { app Y := G.map (μ Q X Y) ≫ e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y)
      naturality := by
        intro Y Y' g
        dsimp
        rw [← G.map_comp_assoc, μ_natural_right, G.map_comp, assoc]
        have he := e.hom.naturality (X ◁ g)
        dsimp only [Functor.comp_map] at he
        rw [reassoc_of% he, ← L.map_comp, ← δ_natural_right, L.map_comp, assoc]
        simp only [assoc] }
  naturality := by
    intro X X' f
    ext Y
    dsimp
    rw [← G.map_comp_assoc, μ_natural_left, G.map_comp, assoc]
    have he := e.hom.naturality (f ▷ Y)
    dsimp only [Functor.comp_map] at he
    rw [reassoc_of% he, ← L.map_comp, ← δ_natural_left, L.map_comp, assoc]
    simp only [assoc]

private theorem square_monoidal [G.Monoidal] [IsIso (ε L)]
    (hη : η G = G.map (ε Q) ≫ e.hom.app (𝟙_ A) ≫ L.map (η F) ≫ inv (ε L))
    (hδ : ∀ X Y, δ G (Q.obj X) (Q.obj Y) ≫
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) =
        G.map (μ Q X Y) ≫ e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y)) :
    NatTrans.IsMonoidal e.hom where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, assoc]
    change ε G ≫ G.map (ε Q) ≫ e.hom.app (𝟙_ A) = ε L ≫ L.map (ε F)
    rw [← cancel_mono (L.map (η F))]
    simp only [assoc, ← L.map_comp, Functor.Monoidal.ε_η,
      CategoryTheory.Functor.map_id, comp_id]
    rw [← cancel_mono (inv (ε L))]
    simp only [assoc, ← hη, Functor.Monoidal.ε_η, IsIso.hom_inv_id]
  tensor X Y := by
    simp only [Functor.LaxMonoidal.comp_μ, assoc]
    change μ G (Q.obj X) (Q.obj Y) ≫ G.map (μ Q X Y) ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) ≫ L.map (μ F X Y)
    rw [← cancel_epi (δ G (Q.obj X) (Q.obj Y))]
    simp only [Functor.Monoidal.δ_μ_assoc]
    rw [← cancel_mono (L.map (δ F X Y))]
    simp only [assoc, ← L.map_comp, Functor.Monoidal.μ_δ,
      CategoryTheory.Functor.map_id, comp_id]
    exact (hδ X Y).symm

/-- Braided localization together with the monoidal factorization it constructs.
Source: Stacks Project, Tags 06YS and 06YT. The proof is the localization-square
construction, retaining its monoidal factorization conclusion.
Source: literature/stacks-project/sites-cohomology.tex; Tags 06YS and 06YT; same normalized
derived-bifunctor square as lem-sfb-braided-localization-square, retaining its
monoidal-factorization conclusion.
(blueprint: lem-pur-u2-normalized-braided-localization). -/
theorem normalizedBraidedLocalization (W : MorphismProperty A)
    [W.ContainsIdentities] [W.RespectsIso] [Q.IsLocalization W]
    [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [IsIso (ε Q)] [IsIso (ε L)]
    (hmodels : ∀ X : D, ∃ a, W.kFlat a ∧ Nonempty (Q.obj a ≅ X))
    (hQ : ∀ a b, W.kFlat b → IsIso (μ Q a b))
    (hL : ∀ (x : B) b, W.kFlat b → IsIso (μ L x (F.obj b))) :
    ∃ b : G.Braided, letI := b
      NatTrans.IsMonoidal e.hom := by
  let T := (((whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E)
  let U := (postcompose₂.obj G).obj (curriedTensor D)
  let α := squareTargetCounit Q L F G e
  let β := squareSourceCounit Q L F G e
  have : T.IsLeftDerivedFunctor₂ α W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) W.localizerMorphismKFlat α
    intro a b
    have := hL (F.obj a) b.obj b.property
    dsimp only [α, LocalizerMorphism.id_functor, Functor.id_obj]
    rw [squareTargetCounit_app]
    change IsIso ((e.hom.app a ⊗ₘ e.hom.app b.obj) ≫ μ L (F.obj a) (F.obj b.obj))
    infer_instance
  have : U.IsLeftDerivedFunctor₂ β W W := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (LocalizerMorphism.id W) W.localizerMorphismKFlat β
    intro a b
    have := hQ a b.obj b.property
    change IsIso (G.map (μ Q a b.obj) ≫ e.hom.app _ ≫ L.map (δ F _ _))
    infer_instance
  let t : U ≅ T := leftDerived₂NatIso T α W W U β (Iso.refl _)
  have ht (X Y : A) : (t.hom.app (Q.obj X)).app (Q.obj Y) ≫
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) =
      G.map (μ Q X Y) ≫ e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y) := by
    have hh := leftDerived₂NatTrans_app_app T α W W U β (𝟙 _) X Y
    rw [show (α.app X).app Y =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) from
        squareTargetCounit_app Q L F G e X Y] at hh
    change (t.hom.app (Q.obj X)).app (Q.obj Y) ≫
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ L (F.obj X) (F.obj Y) =
        (β.app X).app Y ≫ 𝟙 _ at hh
    exact hh.trans (Category.comp_id _)
  let : G.OplaxMonoidal := .ofLaxSquare t.hom (fun a ↦ e.hom.app a)
    (fun _ _ f ↦ e.hom.naturality f) ht W.kFlat hmodels hL
  have (X Y : D) : IsIso (δ G X Y) :=
    inferInstanceAs (IsIso ((t.hom.app X).app Y))
  have : IsIso (η G) := by
    change IsIso (G.map (ε Q) ≫ e.hom.app _ ≫ L.map (η F) ≫ inv (ε L))
    infer_instance
  let : G.Monoidal := .ofOplaxMonoidal G
  have hm : NatTrans.IsMonoidal e.hom :=
    square_monoidal Q L F G e rfl ht
  have hi : NatTrans.IsMonoidal e.symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.inv)
  let lb : (Q ⋙ G).LaxBraided := Functor.LaxBraided.ofNatIso e.symm
  have hb (a b : A) (ha : W.kFlat a) :
      μ G (Q.obj a) (Q.obj b) ≫ G.map (β_ (Q.obj a) (Q.obj b)).hom =
        (β_ (G.obj (Q.obj a)) (G.obj (Q.obj b))).hom ≫ μ G (Q.obj b) (Q.obj a) := by
    have := hQ b a ha
    apply (cancel_mono (G.map (μ Q b a))).1
    have hh := lb.braided a b
    change (μ G (Q.obj a) (Q.obj b) ≫ G.map (μ Q a b)) ≫
      G.map (Q.map (β_ a b).hom) =
        (β_ (G.obj (Q.obj a)) (G.obj (Q.obj b))).hom ≫
          μ G (Q.obj b) (Q.obj a) ≫ G.map (μ Q b a) at hh
    rw [assoc, ← G.map_comp, Functor.LaxBraided.braided (F := Q), G.map_comp] at hh
    simpa only [assoc] using hh
  refine ⟨{ toMonoidal := inferInstance, braided := ?_ }, hm⟩
  intro X Y
  obtain ⟨a, ha, ⟨ia⟩⟩ := hmodels X
  obtain ⟨b, hb', ⟨ib⟩⟩ := hmodels Y
  apply (cancel_epi (G.map ia.hom ⊗ₘ G.map ib.hom)).1
  rw [μ_natural_assoc, ← G.map_comp, BraidedCategory.braiding_naturality,
    G.map_comp, ← assoc, hb a b ha, assoc, ← μ_natural,
    BraidedCategory.braiding_naturality_assoc]

end CategoryTheory
