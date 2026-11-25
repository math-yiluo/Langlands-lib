/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.FinitePresentation

/-!
# Properness descends to a finite stage of a cofiltered limit

Let `{Dⱼ}` be a cofiltered system of quasi-compact quasi-separated schemes with affine transition
morphisms and limit `lim Dⱼ`, and let `p : Y ⟶ Dᵢ` be separated, quasi-compact and of finite
presentation. If the base change of `p` to `lim Dⱼ` is proper, then so is its base change to
some stage `Dⱼ` (Stacks, Tag 081F; EGA IV₃, 8.10.5 (xii)).

## Proof

By Nagata's compactification theorem `p` factors as an open immersion `Y ⟶ Ȳ` followed by a
proper morphism `Ȳ ⟶ Dᵢ`. Over the limit, the open immersion of the base change of `Y` into the
base change of `Ȳ` is proper, so its image `U` is clopen; the complement `W` is a quasi-compact
open. Both `W` and the relations `U ∩ W = ∅`, `U ∪ W = ⊤` descend to a finite stage
(Stacks, Tag 01Z4), where `Y ×_{Dᵢ} Dⱼ` becomes a clopen, hence closed, subscheme of the proper
`Dⱼ`-scheme `Ȳ ×_{Dᵢ} Dⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- The morphism `X ×_S T ⟶ Z ×_S T` induced by `ι : X ⟶ Z` (for `g : Z ⟶ S`, `h : T ⟶ S`) is
the base change of `ι` along the first projection `Z ×_S T ⟶ Z`. -/
lemma isPullback_pullbackMap_comp_fst {X Z S T : Scheme.{u}} (ι : X ⟶ Z) (g : Z ⟶ S)
    (h : T ⟶ S) :
    IsPullback (pullback.map (ι ≫ g) h g h ι (𝟙 T) (𝟙 S) (by simp) (by simp))
      (pullback.fst (ι ≫ g) h) (pullback.fst g h) ι :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (ι ≫ g) h).flip) (by simp)
    (IsPullback.of_hasPullback g h).flip

/-- The range of `X ×_S T ⟶ Z ×_S T` induced by `ι : X ⟶ Z` is the preimage of the range of `ι`
under the first projection. -/
lemma range_pullbackMap_comp {X Z S T : Scheme.{u}} (ι : X ⟶ Z) (g : Z ⟶ S) (h : T ⟶ S) :
    Set.range (pullback.map (ι ≫ g) h g h ι (𝟙 T) (𝟙 S) (by simp) (by simp)) =
      pullback.fst g h ⁻¹' Set.range ι := by
  rw [Scheme.Pullback.range_map]
  simp

/-- **Properness descends to a finite stage** (Stacks, Tag 081F). Let `{Dⱼ}` be a cofiltered
system of quasi-compact quasi-separated schemes with affine transition morphisms and limit cone
`c`, and let `p : Y ⟶ Dᵢ` be separated, quasi-compact and of finite presentation. If the base
change of `p` to `lim Dⱼ` is proper, then the base change of `p` to some stage `Dⱼ` is proper. -/
theorem Scheme.exists_isProper_pullback_snd_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c) {i : I} {Y : Scheme.{u}}
    (p : Y ⟶ D.obj i) [IsSeparated p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [IsProper (pullback.snd p (c.π.app i))] :
    ∃ (j : I) (f : j ⟶ i), IsProper (pullback.snd p (D.map f)) := by
  obtain ⟨⟨Z, g, ι, rfl, _, _⟩⟩ :=
    (nagataCompactification_of_locallyOfFinitePresentation p).nonempty_compactification
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (ι ≫ g)
  have hE := isLimitBaseChangeCone D c g hc
  have hm {T : Scheme.{u}} (h : T ⟶ D.obj i) :
      IsOpenImmersion (pullback.map (ι ≫ g) h g h ι (𝟙 T) (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_pullbackMap_comp_fst ι g h).flip
      inferInstance
  have hcomp {T : Scheme.{u}} (h : T ⟶ D.obj i) :
      pullback.snd (ι ≫ g) h =
        pullback.map (ι ≫ g) h g h ι (𝟙 T) (𝟙 _) (by simp) (by simp) ≫ pullback.snd g h := by
    simp
  -- the image of the base change of `Y` in the base change of `Z` over the limit is closed
  have hclosed : IsClosed (pullback.fst g (c.π.app i) ⁻¹' Set.range ι) := by
    have : IsProper (pullback.map (ι ≫ g) (c.π.app i) g (c.π.app i) ι (𝟙 _) (𝟙 _)
        (by simp) (by simp) ≫ pullback.snd g (c.π.app i)) := by
      rw [← hcomp]
      infer_instance
    have : IsProper (pullback.map (ι ≫ g) (c.π.app i) g (c.π.app i) ι (𝟙 _) (𝟙 _)
        (by simp) (by simp)) := IsProper.of_comp _ (pullback.snd g (c.π.app i))
    rw [← range_pullbackMap_comp]
    exact Scheme.Hom.isClosedMap _ |>.isClosed_range
  -- its complement descends to a quasi-compact open of a stage
  let W : (pullback g (c.π.app i)).Opens :=
    ⟨(pullback.fst g (c.π.app i) ⁻¹' Set.range ι)ᶜ, hclosed.isOpen_compl⟩
  have hW : IsCompact (SetLike.coe W) :=
    ((pullback.fst g (c.π.app i) ⁻¹ᵁ ι.opensRange).isOpen.isClosed_compl).isCompact
  obtain ⟨j₁, V, hV, hVW⟩ := exists_preimage_eq _ _ hE W hW
  have : IsAffineHom (pullback.fst g (D.map j₁.hom)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let U₁ : ((baseChangeDiagram D g).obj j₁).Opens :=
    pullback.fst g (D.map j₁.hom) ⁻¹ᵁ ι.opensRange
  have hU₁ : IsCompact (U₁ : Set ((baseChangeDiagram D g).obj j₁)) :=
    QuasiCompact.isCompact_preimage _ ι.opensRange.isOpen (isCompact_range ι.continuous)
  have hπU : (baseChangeCone D c g).π.app j₁ ⁻¹ᵁ U₁ =
      pullback.fst g (c.π.app i) ⁻¹ᵁ ι.opensRange := by
    rw [← Scheme.Hom.comp_preimage, baseChangeCone_π_app_fst]
  obtain ⟨k₁, f₁, h₁⟩ := exists_map_preimage_le_map_preimage _ _ hE (U := U₁ ⊓ V) (V := ⊥)
      (hU₁.inter_of_isOpen hV U₁.isOpen V.isOpen) (by
    rintro x ⟨hx₁, hx₂⟩
    have hx₁' : x ∈ (baseChangeCone D c g).π.app j₁ ⁻¹ᵁ U₁ := hx₁
    have hx₂' : x ∈ (baseChangeCone D c g).π.app j₁ ⁻¹ᵁ V := hx₂
    rw [hπU] at hx₁'
    rw [hVW] at hx₂'
    exact (hx₂' hx₁').elim)
  obtain ⟨k₂, f₂, h₂⟩ := exists_map_preimage_le_map_preimage _ _ hE (U := ⊤) (V := U₁ ⊔ V)
      isCompact_univ (by
    intro x _
    by_cases hx : x ∈ pullback.fst g (c.π.app i) ⁻¹ᵁ ι.opensRange
    · rw [← hπU] at hx
      exact Or.inl hx
    · have hx' : x ∈ W := hx
      rw [← hVW] at hx'
      exact Or.inr hx')
  obtain ⟨k, a, b, hab⟩ := IsCofiltered.cospan f₁ f₂
  have hφ₁ (x) : (baseChangeDiagram D g).map (a ≫ f₁) x =
      (baseChangeDiagram D g).map f₁ ((baseChangeDiagram D g).map a x) := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
  have hφ₂ (x) : (baseChangeDiagram D g).map (a ≫ f₁) x =
      (baseChangeDiagram D g).map f₂ ((baseChangeDiagram D g).map b x) := by
    rw [hab, Functor.map_comp, Scheme.Hom.comp_apply]
  have hφ : pullback.fst g (D.map k.hom) =
      (baseChangeDiagram D g).map (a ≫ f₁) ≫ pullback.fst g (D.map j₁.hom) :=
    (baseChangeDiagram_map_fst D g (a ≫ f₁)).symm
  have hkey : (pullback.fst g (D.map k.hom) ⁻¹' Set.range ι)ᶜ =
      (baseChangeDiagram D g).map (a ≫ f₁) ⁻¹' V := by
    ext x
    have hmem : x ∈ pullback.fst g (D.map k.hom) ⁻¹' Set.range ι ↔
        (baseChangeDiagram D g).map (a ≫ f₁) x ∈ U₁ := by
      rw [hφ]
      rfl
    rw [Set.mem_compl_iff, hmem, Set.mem_preimage]
    constructor
    · intro hx
      have := h₂ (x := (baseChangeDiagram D g).map b x) trivial
      rcases this with h | h
      · rw [← hφ₂] at h
        exact (hx h).elim
      · rw [← hφ₂] at h
        exact h
    · intro hx hU
      have := h₁ (x := (baseChangeDiagram D g).map a x) (by
        refine ⟨?_, ?_⟩
        · rw [← hφ₁]
          exact hU
        · rw [← hφ₁]
          exact hx)
      exact this.elim
  have hclosedk : IsClosed (Set.range (pullback.map (ι ≫ g) (D.map k.hom) g (D.map k.hom) ι
      (𝟙 _) (𝟙 _) (by simp) (by simp))) := by
    rw [range_pullbackMap_comp, ← isOpen_compl_iff, hkey]
    exact ((baseChangeDiagram D g).map (a ≫ f₁) ⁻¹ᵁ V).isOpen
  have := IsClosedImmersion.of_isPreimmersion _ hclosedk
  refine ⟨k.left, k.hom, ?_⟩
  rw [hcomp]
  infer_instance

end AlgebraicGeometry
