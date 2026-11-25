/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transporting the class of a correspondence along an inverse image

Abstract form of the computation of the image of the class of a correspondence under the inverse
image along the diagonal, in the point normalization of the trace class.

Let `F ⊣ G` (the inverse image and the proper direct image along `c`), `G ⊣ H` (the exceptional
adjunction along `c`) and `S₁ ⊣ B₁` (the exceptional adjunction along `p₁`) be adjunctions, with
`G ⋙ S₁ ≅ 𝟭` (`c ≫ p₁ = 𝟙`) and its conjugate `B₁ ⋙ H ≅ 𝟭`. The natural transformation
`ζ : F ⟶ S₁` (`CategoryTheory.Verdier.transportζ`) identifies the inverse image with the
exceptional direct image along `p₁`. If the projection morphism `pf` of `G` is the projection
morphism of the adjunction `F ⊣ G` and `F` is braided on the relevant objects, the image under
`F` of `pf ∘ (x⁻¹ adjoint)` read through `ζ` and the counit of `S₁ ⊣ B₁` is `x` read through the
counit of `F ⊣ G` (`CategoryTheory.Verdier.transport_class`).
-/

@[expose] public section

namespace CategoryTheory.Verdier

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {S P : Type*} [Category S] [Category P] {F : P ⥤ S} {G : S ⥤ P} (adjFG : F ⊣ G)
  {S₁ : P ⥤ S} (ιΦ : G ⋙ S₁ ≅ 𝟭 S) [∀ Z, IsIso (adjFG.unit.app Z)]

/-- The comparison `ζ_Z : F Z ⟶ S₁ Z`: `F Z ≅ S₁ G F Z ≅ S₁ Z`. -/
noncomputable def transportζ (Z : P) : F.obj Z ⟶ S₁.obj Z :=
  ιΦ.inv.app (F.obj Z) ≫ S₁.map (inv (adjFG.unit.app Z))

@[reassoc]
lemma transportζ_naturality {Z Z' : P} (f : Z ⟶ Z') :
    F.map f ≫ transportζ adjFG ιΦ Z' = transportζ adjFG ιΦ Z ≫ S₁.map f := by
  have h₁ := ιΦ.inv.naturality (F.map f)
  have h₂ := adjFG.unit.naturality f
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₂
  simp only [transportζ, ← Category.assoc, h₁]
  simp only [Category.assoc, ← S₁.map_comp]
  congr 2
  rw [← cancel_epi (adjFG.unit.app Z), ← Category.assoc, ← h₂, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]

@[reassoc]
lemma transportζ_comp_ιΦ (Y : S) :
    transportζ adjFG ιΦ (G.obj Y) ≫ ιΦ.hom.app Y = adjFG.counit.app Y := by
  have h₁ : inv (adjFG.unit.app (G.obj Y)) = G.map (adjFG.counit.app Y) := by
    rw [IsIso.inv_eq_of_hom_inv_id (adjFG.right_triangle_components Y)]
  have h₂ := ιΦ.hom.naturality (adjFG.counit.app Y)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj] at h₂
  rw [transportζ, h₁, Category.assoc, h₂]
  exact Iso.inv_hom_id_app_assoc ιΦ (F.obj (G.obj Y)) _

/-- `ζ` read through the exceptional adjunction `S₁ ⊣ B₁`. -/
lemma transportζ_homEquiv {B₁ : S ⥤ P} (adjSB : S₁ ⊣ B₁) {Z : P} {K : S} (g : S₁.obj Z ⟶ K) :
    F.map (adjSB.homEquiv _ _ g) ≫ transportζ adjFG ιΦ (B₁.obj K) ≫ adjSB.counit.app K =
      transportζ adjFG ιΦ Z ≫ g := by
  rw [Adjunction.homEquiv_unit, F.map_comp, Category.assoc, transportζ_naturality_assoc,
    transportζ_naturality_assoc]
  simp

lemma transportζ_eq (Y : S) :
    transportζ adjFG ιΦ (G.obj Y) = adjFG.counit.app Y ≫ ιΦ.inv.app Y := by
  rw [← transportζ_comp_ιΦ adjFG ιΦ Y]
  simp

variable [MonoidalCategory S] [MonoidalCategory P] [BraidedCategory S] [BraidedCategory P]
  [F.Monoidal] {H : P ⥤ S} (adjGH : G ⊣ H) {B₁ : S ⥤ P} (adjSB : S₁ ⊣ B₁)
  (ιΨ : B₁ ⋙ H ≅ 𝟭 S)

/-- **Transport of the class of a correspondence along the inverse image.** See the module
docstring: the projection morphism `pf` is that of `F ⊣ G` (`hpf`), `F` is braided at `(M, G 𝟙)`
(`hbraid`), and `ιΨ` is the conjugate of `ιΦ` (`hconj`). -/
theorem transport_class
    (hconj : ∀ K, ιΦ.inv.app (H.obj (B₁.obj K)) ≫ S₁.map (adjGH.counit.app (B₁.obj K)) ≫
      adjSB.counit.app K = ιΨ.hom.app K)
    (pf : ∀ (T : S) (M : P), G.obj T ⊗ M ⟶ G.obj (T ⊗ F.obj M))
    (hpf : ∀ T M, F.map (pf T M) ≫ adjFG.counit.app (T ⊗ F.obj M) =
      δ F (G.obj T) M ≫ adjFG.counit.app T ▷ F.obj M)
    {M : P} (hbraid : μ F M (G.obj (𝟙_ S)) ≫ F.map (β_ M (G.obj (𝟙_ S))).hom =
      (β_ (F.obj M) (F.obj (G.obj (𝟙_ S)))).hom ≫ μ F (G.obj (𝟙_ S)) M)
    {K : S} (x : F.obj M ⟶ H.obj (B₁.obj K)) :
    μ F M (G.obj (𝟙_ S)) ≫ F.map (((β_ M (G.obj (𝟙_ S))).hom ≫ pf (𝟙_ S) M ≫
        G.map (β_ (𝟙_ S) (F.obj M)).hom) ≫ G.map (ρ_ (F.obj M)).hom ≫
        (adjGH.homEquiv _ _).symm x) ≫ transportζ adjFG ιΦ (B₁.obj K) ≫ adjSB.counit.app K =
      F.obj M ◁ adjFG.counit.app (𝟙_ S) ≫ (ρ_ _).hom ≫ x ≫ ιΨ.hom.app K := by
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  rw [transportζ_naturality_assoc, transportζ_eq, Category.assoc, ← hconj]
  have h₁ := adjFG.counit.naturality x
  have h₂ := adjFG.counit.naturality (ρ_ (F.obj M)).hom
  have h₃ := adjFG.counit.naturality (β_ (𝟙_ S) (F.obj M)).hom
  simp only [Functor.comp_map, Functor.id_map] at h₁ h₂ h₃
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% (hpf (𝟙_ S) M),
    reassoc_of% hbraid, Functor.Monoidal.μ_δ_assoc,
    ← BraidedCategory.braiding_naturality_right_assoc, braiding_tensorUnit_right,
    braiding_tensorUnit_left]
  simp

/-- **Transport of the exceptional Künneth map along the inverse image.** Let the adjoint of
`exK` under `S₁ ⊣ B₁` be the symmetry, the inverse of a projection morphism
`pf : S₁ W ⊗ K ⟶ S₁ (W ⊗ A₁ K)` and a morphism `X = X₁ ≫ X₂ ≫ X₃ : S₁ W ⟶ 𝟙` tensored with
`K`. If `F` is braided at `(A₁ K, W)` (`hbraid`), `ζ` is compatible with `pf` (`hproj`) and
`ζ_W ≫ X = eW ≫ φ` (`hX`), then the transport of `exK` is `(eB ⊗ eW) ≫ K ◁ φ ≫ ρ`. -/
theorem transport_kunneth {A₁ : S ⥤ P} {K ω Y₁ Y₂ : S} {W : P}
    (pf : S₁.obj W ⊗ K ⟶ S₁.obj (W ⊗ A₁.obj K)) [IsIso pf]
    (X₁ : S₁.obj W ⟶ Y₁) (X₂ : Y₁ ⟶ Y₂) (X₃ : Y₂ ⟶ 𝟙_ S) (eB : F.obj (A₁.obj K) ⟶ K)
    (eW : F.obj W ⟶ ω) (φ : ω ⟶ 𝟙_ S)
    (hbraid : μ F (A₁.obj K) W ≫ F.map (β_ (A₁.obj K) W).hom =
      (β_ (F.obj (A₁.obj K)) (F.obj W)).hom ≫ μ F W (A₁.obj K))
    (hproj : μ F W (A₁.obj K) ≫ transportζ adjFG ιΦ (W ⊗ A₁.obj K) =
      (transportζ adjFG ιΦ W ⊗ₘ eB) ≫ pf)
    (hX : transportζ adjFG ιΦ W ≫ X₁ ≫ X₂ ≫ X₃ = eW ≫ φ) :
    μ F (A₁.obj K) W ≫ F.map ((adjSB.homEquiv _ _) (S₁.map (β_ (A₁.obj K) W).hom ≫ inv pf ≫
        X₁ ▷ K ≫ X₂ ▷ K ≫ X₃ ▷ K ≫ (λ_ K).hom)) ≫ transportζ adjFG ιΦ (B₁.obj K) ≫
        adjSB.counit.app K =
      (eB ⊗ₘ eW) ≫ K ◁ φ ≫ (ρ_ K).hom := by
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, transportζ_homEquiv,
    ← transportζ_naturality_assoc, reassoc_of% hbraid, reassoc_of% hproj,
    IsIso.hom_inv_id_assoc, tensorHom_comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [hX, ← BraidedCategory.braiding_naturality_assoc]
  simp [tensorHom_def]

section Projection

variable {L I : S ⥤ S} {A₁ : S ⥤ P} (c₁ : L ≅ G ⋙ S₁) (u : L ≅ 𝟭 S) (cI : I ≅ A₁ ⋙ F)
  (s : I ≅ 𝟭 S)

omit [BraidedCategory S] [BraidedCategory P] in
/-- **`ζ` is compatible with the projection morphisms**: if the projection morphism of the
composite `L ≅ G ⋙ S₁` is given by those of `G` and `S₁` (`hcomp`), that of `L ≅ 𝟭` is trivial
(`hid`), and that of `G` is the projection morphism of `F ⊣ G` (`hpf`), then
`μ ≫ ζ = (ζ ⊗ eB) ≫ pf₁` for `eB : F (A₁ M) ≅ I M ≅ M`. -/
theorem transportζ_projection (hu : ιΦ = c₁.symm ≪≫ u)
    (pfL : ∀ (T M : S), L.obj T ⊗ M ⟶ L.obj (T ⊗ I.obj M))
    (pf₁ : ∀ (W : P) (M : S), S₁.obj W ⊗ M ⟶ S₁.obj (W ⊗ A₁.obj M))
    (pfΔ : ∀ (T : S) (N : P), G.obj T ⊗ N ⟶ G.obj (T ⊗ F.obj N))
    [∀ T N, IsIso (pfΔ T N)]
    (hpf : ∀ T N, F.map (pfΔ T N) ≫ adjFG.counit.app (T ⊗ F.obj N) =
      δ F (G.obj T) N ≫ adjFG.counit.app T ▷ F.obj N)
    (hcomp : ∀ T M, pfL T M ≫ L.map (T ◁ cI.hom.app M) =
      c₁.hom.app T ▷ M ≫ pf₁ (G.obj T) M ≫ S₁.map (pfΔ T (A₁.obj M)) ≫
        c₁.inv.app (T ⊗ F.obj (A₁.obj M)))
    (hid : ∀ T M, pfL T M ≫ u.hom.app (T ⊗ I.obj M) ≫ T ◁ s.hom.app M = u.hom.app T ▷ M)
    (hnat : ∀ {W W' : P} (f : W ⟶ W') (M : S),
      S₁.map f ▷ M ≫ pf₁ W' M = pf₁ W M ≫ S₁.map (f ▷ A₁.obj M))
    (W : P) (M : S) :
    μ F W (A₁.obj M) ≫ transportζ adjFG ιΦ (W ⊗ A₁.obj M) =
      (transportζ adjFG ιΦ W ⊗ₘ (cI.inv.app M ≫ s.hom.app M)) ≫ pf₁ W M := by
  subst hu
  -- the case `W = G T`
  have key : ∀ T : S, μ F (G.obj T) (A₁.obj M) ≫ transportζ adjFG (c₁.symm ≪≫ u)
      (G.obj T ⊗ A₁.obj M) = (transportζ adjFG (c₁.symm ≪≫ u) (G.obj T) ⊗ₘ
        (cI.inv.app M ≫ s.hom.app M)) ≫ pf₁ (G.obj T) M := by
    intro T
    have h₁ : pf₁ (G.obj T) M ≫ S₁.map (pfΔ T (A₁.obj M)) =
        c₁.inv.app T ▷ M ≫ pfL T M ≫ L.map (T ◁ cI.hom.app M) ≫
          c₁.hom.app (T ⊗ F.obj (A₁.obj M)) := by
      rw [reassoc_of% (hcomp T M)]
      simp [← comp_whiskerRight_assoc]
    have h₂ : pfL T M = u.hom.app T ▷ M ≫ T ◁ s.inv.app M ≫ u.inv.app (T ⊗ I.obj M) := by
      rw [← hid T M]
      simp only [Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id_app,
        MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
    have h₃ := u.inv.naturality (T ◁ cI.hom.app M)
    simp only [Functor.id_map] at h₃
    rw [← cancel_mono (S₁.map (pfΔ T (A₁.obj M))), Category.assoc, ← transportζ_naturality,
      transportζ_eq, ← Category.assoc (F.map _), hpf]
    simp only [Category.assoc]
    rw [h₁, h₂, transportζ_eq]
    simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
      Functor.Monoidal.μ_δ_assoc]
    rw [← reassoc_of% h₃, tensorHom_def']
    simp only [comp_whiskerRight, Category.assoc, Functor.id_obj]
    rw [← comp_whiskerRight_assoc (c₁.hom.app T), Iso.hom_inv_id_app]
    simp only [id_whiskerRight, Category.id_comp]
    rw [← comp_whiskerRight_assoc (u.inv.app T), Iso.inv_hom_id_app]
    simp only [Functor.id_obj, id_whiskerRight, Category.id_comp]
    rw [← whisker_exchange_assoc]
    simp only [← whiskerLeft_comp_assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [← cancel_mono (S₁.map (adjFG.unit.app W ▷ A₁.obj M)), Category.assoc,
    ← transportζ_naturality, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [Functor.comp_obj]
  rw [key, Category.assoc, ← hnat]
  simp only [Functor.id_obj]
  rw [tensorHom_comp_whiskerRight_assoc, ← transportζ_naturality,
    ← whiskerRight_comp_tensorHom_assoc]

end Projection

section Conjugate

variable {S : Type*} [Category S] {L₂ R₂ L₁ R₁ L₀ R₀ : S ⥤ S} (a₂ : L₂ ⊣ R₂) (a₁ : L₁ ⊣ R₁)
  (a₀ : L₀ ⊣ R₀)

/-- The counit of an adjunction `L₂ ⊣ R₂` with `L₂ ≅ 𝟭`, through the conjugate identification
`R₂ ≅ 𝟭`: the identifications `L₂ ≅ L₁ ≅ L₀ ≅ 𝟭` and the conjugate `R₂ ≅ R₁ ≅ R₀ ≅ 𝟭`, the middle
step being compatible with the counits. -/
lemma conjugate_counit_aux (c : L₂ ≅ L₁) (eL : L₁ ≅ L₀) (eR : R₁ ≅ R₀) (ι₀ : L₀ ≅ 𝟭 S)
    (he : ∀ d, L₁.map (eR.hom.app d) ≫ eL.hom.app (R₀.obj d) ≫ a₀.counit.app d =
      a₁.counit.app d) (K : S) :
    ι₀.inv.app (R₂.obj K) ≫ eL.inv.app _ ≫ c.inv.app _ ≫ a₂.counit.app K =
      (conjugateIsoEquiv a₁ a₂ c).inv.app K ≫ eR.hom.app K ≫
        (conjugateIsoEquiv a₀ Adjunction.id ι₀.symm).hom.app K := by
  have h₁ := conjugateEquiv_counit a₂ a₁ c.inv K
  have h₂ := conjugateEquiv_counit a₀ Adjunction.id ι₀.inv K
  have h₃ := eL.inv.naturality ((conjugateIsoEquiv a₁ a₂ c).inv.app K ≫ eR.hom.app K)
  have h₄ := ι₀.inv.naturality ((conjugateIsoEquiv a₁ a₂ c).inv.app K ≫ eR.hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at h₂ h₄
  change _ ≫ Adjunction.id.counit.app K = _ at h₂
  simp only [Adjunction.id] at h₂
  rw [← h₁, ← he, ← L₁.map_comp_assoc]
  erw [← reassoc_of% h₃, Iso.inv_hom_id_app_assoc, ← reassoc_of% h₄]
  rw [← h₂, NatTrans.id_app, Category.comp_id]
  rfl

end Conjugate

end CategoryTheory.Verdier
