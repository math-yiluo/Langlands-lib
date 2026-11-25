/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitting

/-!
# Pulling back an explicit finite splitting

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-splitting-pullback)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Pullback preserves an explicit splitting and its sheet sections.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-splitting-pullback)

Proof. Pull each inclusion back along the induced map of ambient pullbacks.
Finite coproducts of schemes are universal, so the pulled-back inclusions still
form a coproduct. Open and closed immersions are preserved by pullback. Lift the
old inverse projection together with the identity of the new base to obtain the
new inverse projection. The two inverse identities follow by pullback uniqueness
and the old inverse identities. The same uniqueness proves the displayed section
compatibility. The construction keeps the index type, including an empty one. -/
theorem finiteEtaleTrace_splitting_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Etale f) (T Z : X.Etale) (g : Z ⟶ T)
    (D : FiniteEtaleTraceSplitting f T) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
    ∃ (E : FiniteEtaleTraceSplitting f Z) (e : D.J ≃ E.J),
      ∀ j, g ≫ D.sectionMap hf j = E.sectionMap hf (e j) ≫ B.map g := by
  classical
  let := D.finiteIndex
  let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
  let b : pullback Z.hom f ⟶ pullback T.hom f := (B.map g).left
  have hb₁ : b ≫ pullback.fst T.hom f = pullback.fst Z.hom f ≫ g.left := by
    simp [b, B, MorphismProperty.Over.pullback_map_left]
  have hb₂ : b ≫ pullback.snd T.hom f = pullback.snd Z.hom f := by
    simp [b, B, MorphismProperty.Over.pullback_map_left]
  let a (j : D.J) : Z.left ⟶ pullback Z.hom f :=
    pullback.lift (𝟙 _) (g.left ≫ D.t j ≫ D.i j ≫ pullback.snd T.hom f) (by
      rw [Category.assoc, Category.assoc, Category.assoc, ← pullback.condition]
      simp [← Category.assoc, D.inv₁])
  have ha₁ (j : D.J) : a j ≫ pullback.fst Z.hom f = 𝟙 _ := by simp [a]
  have hab (j : D.J) : a j ≫ b = g.left ≫ D.t j ≫ D.i j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hb₁]
      simp [← Category.assoc, D.inv₁, ha₁]
    · simp [Category.assoc, hb₂, a]
  let V (j : D.J) := pullback b (D.i j)
  let i (j : D.J) : V j ⟶ pullback Z.hom f := pullback.fst b (D.i j)
  let t (j : D.J) : Z.left ⟶ V j :=
    pullback.lift (a j) (g.left ≫ D.t j) (hab j)
  have hi₁ (j : D.J) : t j ≫ i j ≫ pullback.fst Z.hom f = 𝟙 _ := by
    simp [t, i, ha₁]
  have hi₂ (j : D.J) : i j ≫ pullback.fst Z.hom f ≫ t j = 𝟙 (V j) := by
    have hproj : i j ≫ pullback.fst Z.hom f ≫ g.left =
        pullback.snd b (D.i j) ≫ D.i j ≫ pullback.fst T.hom f := by
      rw [← hb₁, ← Category.assoc]
      simpa [i, Category.assoc] using
        congrArg (fun k ↦ k ≫ pullback.fst T.hom f)
          (pullback.condition (f := b) (g := D.i j))
    have hs : i j ≫ pullback.fst Z.hom f ≫ g.left ≫ D.t j =
        pullback.snd b (D.i j) := by
      calc
        _ = (i j ≫ pullback.fst Z.hom f ≫ g.left) ≫ D.t j := by simp
        _ = (pullback.snd b (D.i j) ≫ D.i j ≫ pullback.fst T.hom f) ≫
            D.t j := by rw [hproj]
        _ = _ := by simp [Category.assoc, D.inv₂]
    apply pullback.hom_ext
    · change (i j ≫ pullback.fst Z.hom f ≫ t j) ≫ i j = _
      simp only [Category.assoc, t, i, pullback.lift_fst, Category.id_comp]
      apply pullback.hom_ext
      · simp [Category.assoc, ha₁]
      · change i j ≫ pullback.fst Z.hom f ≫ a j ≫ pullback.snd Z.hom f =
          i j ≫ pullback.snd Z.hom f
        simp only [a, pullback.lift_snd]
        calc
          _ = (i j ≫ pullback.fst Z.hom f ≫ g.left ≫ D.t j) ≫ D.i j ≫
              pullback.snd T.hom f := by simp
          _ = pullback.snd b (D.i j) ≫ D.i j ≫ pullback.snd T.hom f := by rw [hs]
          _ = i j ≫ b ≫ pullback.snd T.hom f := by
            rw [← Category.assoc, ← pullback.condition]; rfl
          _ = _ := by rw [hb₂]
    · change (i j ≫ pullback.fst Z.hom f ≫ t j) ≫ pullback.snd b (D.i j) = _
      simpa [t, Category.assoc] using hs
  have hc : IsColimit (Cofan.mk (pullback Z.hom f) i) := by
    let hu := FinitaryPreExtensive.isUniversal_finiteCoproducts D.colimit
    exact (hu.nonempty_isColimit_of_pullbackCone_left D.i (𝟙 _) b
      (fun j ↦ pullback.cone b (D.i j)) (fun j ↦ pullback.isLimit _ _)
      (PullbackCone.mk (𝟙 _) b (by simp))
      (PullbackCone.IsLimit.mk _ (fun s ↦ s.fst) (by simp)
        (by intro s; simpa using s.condition) (by intro s m hm _; exact hm))
      (Cofan.mk _ i) (Iso.refl _) (by simp) (by simp [i]) (by
        intro j
        simpa [i] using pullback.condition (f := b) (g := D.i j))).some
  let E : FiniteEtaleTraceSplitting f Z :=
    { J := D.J
      finiteIndex := D.finiteIndex
      V := V
      i := i
      t := t
      colimit := hc
      inv₁ := hi₁
      inv₂ := hi₂
      openImmersion := fun j ↦ by
        let := D.openImmersion j
        dsimp [i]
        infer_instance
      closedImmersion := fun j ↦ by
        let := D.closedImmersion j
        dsimp [i]
        infer_instance }
  refine ⟨E, Equiv.refl _, ?_⟩
  intro j
  apply MorphismProperty.Over.Hom.ext
  change g.left ≫ D.t j ≫ D.i j = (t j ≫ i j) ≫ b
  simpa [t, i] using (hab j).symm

end AlgebraicGeometry.Etale
