/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Chosen pullbacks of preimages of an open cover

Let `U a` be a family of opens of a scheme `S` and `g : Z ⟶ S` a morphism. The intersections
`g⁻¹ (U a ⊓ U b)` and `g⁻¹ (U a ⊓ U b ⊓ U c)` are chosen (wide) pullbacks of the open immersions
of the `g⁻¹ U a` (`AlgebraicGeometry.Scheme.Modules.preimageChosenPullback`,
`AlgebraicGeometry.Scheme.Modules.preimageChosenPullback₃`), with diagonals
`AlgebraicGeometry.Scheme.Modules.preimageDiag`. A morphism `h : Z' ⟶ Z` over `S` restricts to
morphisms between these preimages (`AlgebraicGeometry.Scheme.Modules.resTo`), compatibly with the
projections.

This is the input for gluing modules along the open cover `g⁻¹ U a` of `Z` with
`CategoryTheory.Pseudofunctor.DescentData'.ofGlue`, and for pulling gluing morphisms back along
morphisms between stages of a cofiltered system of schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

section Res

variable {S T Z Z' : Scheme.{u}} {G : T ⟶ S} {g : Z ⟶ S}

/-- The restriction `g⁻¹ W ⟶ G⁻¹ V` of a morphism `h : Z ⟶ T` over `S`, for `W ≤ V`. -/
noncomputable def resTo (h : Z ⟶ T) (hg : h ≫ G = g) {V W : S.Opens} (hWV : W ≤ V) :
    (g ⁻¹ᵁ W).toScheme ⟶ (G ⁻¹ᵁ V).toScheme :=
  h.resLE (G ⁻¹ᵁ V) (g ⁻¹ᵁ W) (by
    subst hg
    rw [Scheme.Hom.comp_preimage]
    exact h.preimage_mono (G.preimage_mono hWV))

@[reassoc (attr := simp)]
lemma resTo_ι (h : Z ⟶ T) (hg : h ≫ G = g) {V W : S.Opens} (hWV : W ≤ V) :
    resTo h hg hWV ≫ (G ⁻¹ᵁ V).ι = (g ⁻¹ᵁ W).ι ≫ h :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma homOfLE_resTo (h : Z ⟶ T) (hg : h ≫ G = g) {V W W' : S.Opens} (e : g ⁻¹ᵁ W' ≤ g ⁻¹ᵁ W)
    (hWV : W ≤ V) (hW'V : W' ≤ V) :
    Z.homOfLE e ≫ resTo h hg hWV = resTo h hg hW'V := by
  rw [← cancel_mono (G ⁻¹ᵁ V).ι]
  simp

@[reassoc]
lemma resTo_resTo (h : Z ⟶ T) (hg : h ≫ G = g) {g' : Z' ⟶ S} (h₂ : Z' ⟶ Z) (hg₂ : h₂ ≫ g = g')
    {h' : Z' ⟶ T} (hh : h₂ ≫ h = h') (hg' : h' ≫ G = g') {V W W' : S.Opens} (hWV : W ≤ V)
    (hW'W : W' ≤ W) (hW'V : W' ≤ V) :
    resTo h₂ hg₂ hW'W ≫ resTo h hg hWV = resTo h' hg' hW'V := by
  rw [← cancel_mono (G ⁻¹ᵁ V).ι]
  simp [← hh]


@[reassoc (attr := simp)]
lemma resTo_homOfLE (h : Z ⟶ T) (hg : h ≫ G = g) {V V' W : S.Opens} (hWV : W ≤ V)
    (hVV' : V ≤ V') :
    resTo h hg hWV ≫ T.homOfLE (G.preimage_mono hVV') = resTo h hg (hWV.trans hVV') := by
  rw [← cancel_mono (G ⁻¹ᵁ V').ι]
  simp

end Res

section ChosenPullback

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {Z : Scheme.{u}} (g : Z ⟶ S)

/-- The intersection `g⁻¹ (U a ⊓ U b)` as a chosen pullback of the open immersions of `g⁻¹ U a`
and `g⁻¹ U b`. -/
@[simps]
noncomputable def preimageChosenPullback (a b : ι) :
    ChosenPullback (g ⁻¹ᵁ U a).ι (g ⁻¹ᵁ U b).ι where
  pullback := g ⁻¹ᵁ (U a ⊓ U b)
  p₁ := Z.homOfLE (g.preimage_mono inf_le_left)
  p₂ := Z.homOfLE (g.preimage_mono inf_le_right)
  condition := by simp
  isLimit := (IsOpenImmersion.isPullback (Z.homOfLE (g.preimage_mono inf_le_left))
    (Z.homOfLE (g.preimage_mono inf_le_right)) (g ⁻¹ᵁ U a).ι (g ⁻¹ᵁ U b).ι (by simp)
    (by ext x; simp)).isLimit
  p := (g ⁻¹ᵁ (U a ⊓ U b)).ι
  hp₁ := by simp

/-- The triple intersection `g⁻¹ (U a ⊓ U b ⊓ U c)` as a chosen wide pullback. -/
@[simps]
noncomputable def preimageChosenPullback₃ (a b c : ι) :
    ChosenPullback₃ (preimageChosenPullback U g a b) (preimageChosenPullback U g b c)
      (preimageChosenPullback U g a c) where
  chosenPullback :=
    { pullback := g ⁻¹ᵁ (U a ⊓ U b ⊓ U c)
      p₁ := Z.homOfLE (g.preimage_mono inf_le_left)
      p₂ := Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      condition := by simp
      isLimit := by
        refine (IsOpenImmersion.isPullback (Z.homOfLE (g.preimage_mono inf_le_left))
          (Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
          (Z.homOfLE (g.preimage_mono inf_le_right))
          (Z.homOfLE (g.preimage_mono inf_le_left)) (by simp) ?_).isLimit
        ext x
        simp only [opensRange_homOfLE, TopologicalSpace.Opens.map_coe,
          TopologicalSpace.Opens.coe_inf, Set.preimage_inter, Set.mem_inter_iff,
          Set.mem_preimage, Opens.ι_apply, homOfLE_apply, SetLike.mem_coe, iff_self_and,
          and_imp]
        exact fun _ _ ↦ x.2.2
      p := Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_right))
      hp₁ := by simp }
  p := (g ⁻¹ᵁ (U a ⊓ U b ⊓ U c)).ι
  p₁ := Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_left))
  p₃ := Z.homOfLE (g.preimage_mono inf_le_right)
  l :=
    { f := Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) }
  hp₁ := by simp
  hp₃ := by simp

variable (a b c : ι)

@[simp]
lemma preimageChosenPullback₃_p₁₂ :
    (preimageChosenPullback₃ U g a b c).p₁₂ = Z.homOfLE (g.preimage_mono inf_le_left) := rfl

@[simp]
lemma preimageChosenPullback₃_p₂₃ :
    (preimageChosenPullback₃ U g a b c).p₂₃ =
      Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) := rfl

@[simp]
lemma preimageChosenPullback₃_p₁₃ :
    (preimageChosenPullback₃ U g a b c).p₁₃ =
      Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := rfl

@[simp]
lemma preimageChosenPullback₃_p₂ :
    (preimageChosenPullback₃ U g a b c).p₂ =
      Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_right)) := rfl

/-- The diagonal `g⁻¹ U a ⟶ g⁻¹ (U a ⊓ U a)`. -/
noncomputable def preimageDiag (a : ι) :
    (g ⁻¹ᵁ U a).toScheme ⟶ (preimageChosenPullback U g a a).pullback :=
  Z.homOfLE (g.preimage_mono (le_inf le_rfl le_rfl))

@[reassoc (attr := simp)]
lemma preimageDiag_p₁ (a : ι) : preimageDiag U g a ≫ (preimageChosenPullback U g a a).p₁ = 𝟙 _ := by
  simp [preimageDiag]

@[reassoc (attr := simp)]
lemma preimageDiag_p₂ (a : ι) : preimageDiag U g a ≫ (preimageChosenPullback U g a a).p₂ = 𝟙 _ := by
  simp [preimageDiag]

end ChosenPullback

section ResTo

/-! ### Restrictions of a morphism over `S` to the chosen pullbacks -/

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {Z Z' : Scheme.{u}} {g : Z ⟶ S}
  {g' : Z' ⟶ S} (h : Z' ⟶ Z) (hg : h ≫ g = g') (a b c : ι)

lemma resTo_p₁ : resTo h hg (le_refl (U a ⊓ U b)) ≫ (preimageChosenPullback U g a b).p₁ =
    (preimageChosenPullback U g' a b).p₁ ≫ resTo h hg (le_refl (U a)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₂ : resTo h hg (le_refl (U a ⊓ U b)) ≫ (preimageChosenPullback U g a b).p₂ =
    (preimageChosenPullback U g' a b).p₂ ≫ resTo h hg (le_refl (U b)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₁₂ :
    resTo h hg (le_refl (U a ⊓ U b ⊓ U c)) ≫ (preimageChosenPullback₃ U g a b c).p₁₂ =
      (preimageChosenPullback₃ U g' a b c).p₁₂ ≫ resTo h hg (le_refl (U a ⊓ U b)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₂₃ :
    resTo h hg (le_refl (U a ⊓ U b ⊓ U c)) ≫ (preimageChosenPullback₃ U g a b c).p₂₃ =
      (preimageChosenPullback₃ U g' a b c).p₂₃ ≫ resTo h hg (le_refl (U b ⊓ U c)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₁₃ :
    resTo h hg (le_refl (U a ⊓ U b ⊓ U c)) ≫ (preimageChosenPullback₃ U g a b c).p₁₃ =
      (preimageChosenPullback₃ U g' a b c).p₁₃ ≫ resTo h hg (le_refl (U a ⊓ U c)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₁' :
    resTo h hg (le_refl (U a ⊓ U b ⊓ U c)) ≫ (preimageChosenPullback₃ U g a b c).p₁ =
      (preimageChosenPullback₃ U g' a b c).p₁ ≫ resTo h hg (le_refl (U a)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₂' :
    resTo h hg (le_refl (U a ⊓ U b ⊓ U c)) ≫ (preimageChosenPullback₃ U g a b c).p₂ =
      (preimageChosenPullback₃ U g' a b c).p₂ ≫ resTo h hg (le_refl (U b)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma resTo_p₃' :
    resTo h hg (le_refl (U a ⊓ U b ⊓ U c)) ≫ (preimageChosenPullback₃ U g a b c).p₃ =
      (preimageChosenPullback₃ U g' a b c).p₃ ≫ resTo h hg (le_refl (U c)) := by
  rw [← cancel_mono (g ⁻¹ᵁ _).ι]
  simp

lemma preimageDiag_resTo :
    preimageDiag U g' a ≫ resTo h hg (le_refl (U a ⊓ U a)) =
      resTo h hg (le_refl (U a)) ≫ preimageDiag U g a := by
  simp [preimageDiag]

end ResTo

end AlgebraicGeometry.Scheme.Modules
