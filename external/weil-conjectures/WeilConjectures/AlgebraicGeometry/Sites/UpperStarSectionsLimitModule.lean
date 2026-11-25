/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsLimit
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsModule

/-!
# Sections of inverse images of étale sheaves of modules at a cofiltered limit

The results of `WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsLimit` for étale sheaves
of modules over a ring `Λ : Type (u + 1)`: for a cofiltered limit `X = lim Dⱼ` of quasi-compact
quasi-separated schemes over `R` with affine transition maps, an étale sheaf `G` of `Λ`-modules on
`R` and a quasi-compact quasi-separated étale `Dₖ`-scheme `Y` with base change `V = Y ×_{Dₖ} X`,
the sections of the inverse image of `G` over `V` are the filtered colimit of the sections over
the `Y ×_{Dₖ} Dⱼ` (`AlgebraicGeometry.Etale.ModuleSheaf.exists_restrictAlong_eq_of_isLimit`,
`AlgebraicGeometry.Etale.ModuleSheaf.exists_restrictAlong_eq_zero_of_isLimit`). This is the
form used for the continuity of étale cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale.ModuleSheaf

variable {Λ : Type (u + 1)} [CommRing Λ]

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c) {R : Scheme.{u}} (π : D ⟶ (Functor.const J).obj R) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

variable (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- `restrictAlong` only depends on the morphism of base schemes through its value. -/
lemma restrictAlong_congr_hom {T T' : Scheme.{u}} (t : T ⟶ R) {f₁ f₂ : T' ⟶ T} (t' : T' ⟶ R)
    (ht' : t' = f₁ ≫ t) (h : f₁ = f₂) {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left)
    (hm : m ≫ V.hom = V'.hom ≫ f₁) :
    restrictAlong t G f₁ t' ht' m hm = restrictAlong t G f₂ t' (h ▸ ht') m (h ▸ hm) := by
  subst h
  rfl

include hc hP in
/-- (Implementation) **Local vanishing at a stage.** If a section `s` over an étale `Dₖ`-scheme
`Y` vanishes on the base change `V` of `Y` to the limit, then every point of `V` is covered by
an étale `X`-scheme mapping compatibly to `V` and to an étale scheme `E` over a later stage,
mapping to `Y`, on which `s` vanishes. -/
lemma exists_local_restrictAlong_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : m ≫ Y.hom = V.hom ≫ c.π.app k)
    (s : ((π.app k)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op Y))
    (hs : restrictAlong (π.app k) G (c.π.app k) P (hP k) m hm s = 0) (x : V.left) :
    ∃ (k₁ : J) (f₁ : k₁ ⟶ k) (E : (D.obj k₁).Etale) (e : E.left ⟶ Y.left)
      (he : e ≫ Y.hom = E.hom ≫ D.map f₁)
      (_ : restrictAlong (π.app k) G (D.map f₁) (π.app k₁) (app_eq_map_comp_app π f₁) e he s = 0)
      (Z : c.pt.Etale) (u : Z.left ⟶ E.left) (_ : u ≫ E.hom = Z.hom ≫ c.π.app k₁) (v : Z ⟶ V),
      u ≫ e = v.left ≫ m ∧ x ∈ Set.range v.left := by
  obtain ⟨Ya, b, U, φ, hφ, g, ⟨ya, hya⟩, hsa⟩ := exists_pullSection_eq (π.app k) G s (m x)
  obtain ⟨xa, hxa₁, hxa₂⟩ := Scheme.Pullback.exists_preimage_pullback x ya hya.symm
  have hsnd : pullback.snd m b.left ≫ Ya.hom = (pullbackObj m b).hom ≫ c.π.app k := by
    rw [pullbackObj_hom, Category.assoc, ← hm, ← MorphismProperty.Over.w b,
      pullback.condition_assoc]
  have h0 : pullSection P G (V := pullbackObj m b) (pullback.snd m b.left ≫ φ)
      (by rw [Category.assoc, hφ, reassoc_of% hsnd, ← hP]) g = 0 := by
    calc _ = restrictAlong (π.app k) G (c.π.app k) P (hP k) _ hsnd
          (pullSection (π.app k) G φ hφ g) :=
          (restrictAlong_pullSection (π.app k) G (c.π.app k) P (hP k) _ hsnd φ hφ g).symm
      _ = restrictAlong (π.app k) G (c.π.app k) P (hP k) (pullback.snd m b.left ≫ b.left)
          (by rw [Category.assoc, MorphismProperty.Over.w b, hsnd]) s := by
        rw [← hsa, restrictAlong_map]
      _ = restrictAlong (π.app k) G (c.π.app k) P (hP k) ((pullbackObjFst m b).left ≫ m)
          (by rw [Category.assoc, hm, ← Category.assoc, MorphismProperty.Over.w]) s :=
        ConcreteCategory.congr_hom (restrictAlong_congr _ _ _ _ _ _ pullback.condition.symm) s
      _ = 0 := by rw [← map_restrictAlong _ _ _ _ _ (pullbackObjFst m b) m hm, hs, map_zero]
  obtain ⟨V'', a, U', b', φ', hφ', ⟨z, hz⟩, hfac, hg0⟩ :=
    exists_of_pullSection_eq_zero P G _ _ g h0 xa
  obtain ⟨k₁, f₁, E, hE, e, he, ψ, hψ, Z, u, hu, w, hue, huψ, ⟨z', hz'⟩⟩ :=
    exists_local_descent_of_isLimit hc π P hP Ya (pullback.snd m b.left) hsnd a φ' hφ' z
  have : CompactSpace ↥((𝟭 Scheme).obj E.left) := inferInstanceAs (CompactSpace E.left)
  obtain ⟨k₂, f₂, heq⟩ := exists_eq_descent_of_isLimit D c hc π E.hom U.hom (ψ ≫ b'.left)
    (e ≫ φ) (by rw [Category.assoc, MorphismProperty.Over.w b', hψ])
    (by rw [Category.assoc, hφ, reassoc_of% he, ← app_eq_map_comp_app])
    (by
      rw [← hu.isoPullback_inv_fst, Category.assoc, Category.assoc, reassoc_of% huψ, hfac,
        reassoc_of% hue])
  let E₂ : (D.obj k₂).Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.snd E.hom (D.map f₂)) inferInstance
  have he₂ : (pullback.fst E.hom (D.map f₂) ≫ e) ≫ Ya.hom = E₂.hom ≫ D.map (f₂ ≫ f₁) := by
    simp [E₂, he, pullback.condition_assoc]
  refine ⟨k₂, f₂ ≫ f₁, E₂, pullback.fst E.hom (D.map f₂) ≫ e ≫ b.left, ?_, ?_, Z,
    pullback.lift u (Z.hom ≫ c.π.app k₂) (by rw [hu.w, Category.assoc, c.w]),
    pullback.lift_snd _ _ _, w ≫ a ≫ pullbackObjFst m b, ?_, ?_⟩
  · simp [E₂, he, pullback.condition_assoc]
  · calc _ = restrictAlong (π.app k) G (D.map (f₂ ≫ f₁)) (π.app k₂) (app_eq_map_comp_app π _)
          ((pullback.fst E.hom (D.map f₂) ≫ e) ≫ b.left)
          (by rw [Category.assoc, MorphismProperty.Over.w b, he₂]) s :=
          ConcreteCategory.congr_hom
            (restrictAlong_congr _ _ _ _ _ _ (Category.assoc _ _ _).symm) s
      _ = _ :=
          (restrictAlong_map _ _ _ _ _ b _ he₂ s).symm
      _ = pullSection (π.app k₂) G (V := E₂) ((pullback.fst E.hom (D.map f₂) ≫ e) ≫ φ)
          (by rw [Category.assoc, hφ, ← Category.assoc, he₂, Category.assoc,
            ← app_eq_map_comp_app]) g := by
        rw [hsa, restrictAlong_pullSection]
      _ = pullSection (π.app k₂) G (V := E₂) ((pullback.fst E.hom (D.map f₂) ≫ ψ) ≫ b'.left)
          (by rw [Category.assoc, MorphismProperty.Over.w b', Category.assoc, hψ]
              simp [E₂, pullback.condition_assoc]) g :=
        pullSection_congr _ _ _ (by simpa using heq.symm) g
      _ = 0 := by
        rw [pullSection_comp (hφ := by
          rw [Category.assoc, hψ]
          simp [E₂, pullback.condition_assoc]), hg0, pullSection_zero]
  · simp [reassoc_of% hue, pullback.condition]
  · refine ⟨z', ?_⟩
    rw [← hxa₁, ← hz, ← hz']
    rfl

include hc hP in
/-- **Injectivity of the comparison of sections at a cofiltered limit.** Let `Y` be a
quasi-compact étale scheme over a stage `Dₖ`, with base change `m : V ⟶ Y` to the limit `X`, and
let `s` be a section of the inverse image of `G` over `Y` whose restriction to `V` vanishes. Then
the restriction of `s` along every morphism `V' ⟶ Y` over a late enough stage `Dₖ'' ⟶ Dₖ`
vanishes. -/
theorem exists_restrictAlong_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) [CompactSpace Y.left] {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : IsPullback m V.hom Y.hom (c.π.app k))
    (s : ((π.app k)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op Y))
    (hs : restrictAlong (π.app k) G (c.π.app k) P (hP k) m hm.w s = 0) :
    ∃ (k' : J) (f : k' ⟶ k), ∀ ⦃k'' : J⦄ (g' : k'' ⟶ k') (g : k'' ⟶ k), g' ≫ f = g →
      ∀ (V' : (D.obj k'').Etale) (m' : V'.left ⟶ Y.left) (hm' : m' ≫ Y.hom = V'.hom ≫ D.map g),
        restrictAlong (π.app k) G (D.map g) (π.app k'') (app_eq_map_comp_app π g) m' hm' s = 0 := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiCompact Y.hom := @quasiCompact_of_compactSpace _ _ Y.hom
    (inferInstanceAs (CompactSpace Y.left)) (inferInstanceAs (QuasiSeparatedSpace (D.obj k)))
  have : QuasiCompact V.hom := MorphismProperty.of_isPullback hm this
  have : CompactSpace V.left := @QuasiCompact.compactSpace_of_compactSpace _ _ V.hom _
    (inferInstanceAs (CompactSpace c.pt))
  choose k₁ f₁ E e he hvan Z u hu v hv hx using
    exists_local_restrictAlong_eq_zero_of_isLimit hc π P hP G Y m hm.w s hs
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (v x).left)
    (fun x ↦ (v x).left.isOpenMap.isOpen_range) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  obtain ⟨K, h, g₀, hg₀, H⟩ := exists_forall_mem_range_lift_of_isLimit hc Y m hm (ι := t)
    (fun i ↦ k₁ i) (fun i ↦ f₁ i) (fun i ↦ E i) (fun i ↦ e i) (fun i ↦ he i) (fun x ↦ by
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ Set.range (v i).left := by
        simpa using ht (Set.mem_univ x)
      exact ⟨⟨i, hi⟩, Z i, u i, hu i, v i, hv i, hxi⟩)
  refine ⟨K, h, fun k'' g' g hg V' m' hm' ↦ ?_⟩
  subst hg
  let τ (i : t) : (E i).left ⟶ pullback Y.hom (D.map (f₁ i)) :=
    pullback.lift (e i) (E i).hom (he i)
  have (i : t) : Etale (τ i) := by
    have : Etale (τ i ≫ pullback.snd Y.hom (D.map (f₁ i))) := by
      rw [pullback.lift_snd]
      infer_instance
    exact Etale.of_comp (τ i) (pullback.snd Y.hom (D.map (f₁ i)))
  let Λ' (i : t) : V'.left ⟶ pullback Y.hom (D.map (f₁ i)) :=
    pullback.lift m' (V'.hom ≫ D.map (g' ≫ g₀ i))
      (by rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc, hg₀])
  let W (i : t) : (D.obj k'').Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.fst (Λ' i) (τ i) ≫ V'.hom) inferInstance
  let a (i : t) : W i ⟶ V' := MorphismProperty.Over.homMk (pullback.fst (Λ' i) (τ i)) rfl
  refine eq_zero_of_forall_map_eq_zero _ a (fun y ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := H g' V' m' hm' y
    refine ⟨i, ?_⟩
    change y ∈ Set.range (pullback.fst (Λ' i) (τ i))
    rw [Scheme.Pullback.range_fst]
    exact hi
  · have hsnd : pullback.snd (Λ' i) (τ i) ≫ (E i).hom = (W i).hom ≫ D.map (g' ≫ g₀ i) := by
      have := pullback.condition (f := Λ' i) (g := τ i) =≫ pullback.snd _ _
      simpa [τ, Λ', W] using this.symm
    have hfst : (a i).left ≫ m' = pullback.snd (Λ' i) (τ i) ≫ e i := by
      have := pullback.condition (f := Λ' i) (g := τ i) =≫ pullback.fst _ _
      simpa [τ, Λ', a] using this
    have e₁ : D.map (g' ≫ h) = D.map (g' ≫ g₀ i) ≫ D.map (f₁ i) := by
      rw [← Functor.map_comp, Category.assoc, hg₀]
    rw [map_restrictAlong, restrictAlong_congr_hom G (π.app k) (π.app k'') _ e₁,
      restrictAlong_congr (h := hfst), ← restrictAlong_restrictAlong (π.app k) G (D.map (f₁ i))
        (π.app (k₁ i)) (app_eq_map_comp_app π _) (D.map (g' ≫ g₀ i)) (π.app k'')
        (app_eq_map_comp_app π _) (e i) (he i) _ hsnd s, hvan, map_zero]

include hc hP in
/-- (Implementation) **Local descent of a section.** Let `Y` be étale over a stage `Dₖ`, with a
morphism `m : V ⟶ Y` over `X ⟶ Dₖ` from an étale `X`-scheme, and let `t` be a section of the
inverse image of `G` over `V`. Around every point of `V` there is an étale `X`-scheme `Z` over
`V` such that for all late enough stages `D_K`, `Z` is the base change of an affine scheme `E`
étale over `D_K` and mapping to `Y`, and the restriction of `t` to `Z` comes from a section over
`E`. -/
lemma exists_local_section_descent_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : m ≫ Y.hom = V.hom ≫ c.π.app k)
    (t : ((P)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op V)) (x : V.left) :
    ∃ (k₁ : J) (f₁ : k₁ ⟶ k) (Z : c.pt.Etale) (v : Z ⟶ V), x ∈ Set.range v.left ∧
      ∀ ⦃K : J⦄ (h : K ⟶ k) (g : K ⟶ k₁), g ≫ f₁ = h →
        ∃ (E : (D.obj K).Etale) (_ : IsAffine E.left) (e : E.left ⟶ Y.left)
          (_ : e ≫ Y.hom = E.hom ≫ D.map h)
          (σ : ((π.app K)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op E))
          (u : Z.left ⟶ E.left) (hu : IsPullback u Z.hom E.hom (c.π.app K)),
          u ≫ e = v.left ≫ m ∧
            restrictAlong (π.app K) G (c.π.app K) P (hP K) u hu.w σ =
              ((P)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.map v.op t := by
  obtain ⟨V₁, a, U, φ, hφ, g₀, ⟨y, hy⟩, ht⟩ := exists_pullSection_eq P G t x
  obtain ⟨k₁, f₁, E, hE, e, he, ψ, hψ, Z, u, hu, w, hue, huψ, ⟨z, hz⟩⟩ :=
    exists_local_descent_of_isLimit hc π P hP Y m hm a φ hφ y
  refine ⟨k₁, f₁, Z, w ≫ a, ⟨z, by rw [etale_comp_left, Scheme.Hom.comp_apply, hz, hy]⟩,
    fun K h g hg ↦ ?_⟩
  have : IsAffineHom (pullback.fst E.hom (D.map g)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let E' : (D.obj K).Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.snd E.hom (D.map g)) inferInstance
  have hE'hom : E'.hom = pullback.snd E.hom (D.map g) := rfl
  have : IsAffine ((𝟭 Scheme).obj E.left) := hE
  have hE' : IsAffine E'.left := isAffine_of_isAffineHom (pullback.fst E.hom (D.map g))
  let u' : Z.left ⟶ E'.left :=
    pullback.lift u (Z.hom ≫ c.π.app K) (by rw [hu.w, Category.assoc, c.w])
  have hu' : IsPullback u' Z.hom E'.hom (c.π.app K) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback E.hom (D.map g))
    rw [pullback.lift_fst, c.w g]
    exact hu
  have hψ' : (pullback.fst E.hom (D.map g) ≫ ψ) ≫ U.hom = E'.hom ≫ π.app K := by
    rw [Category.assoc, hψ, pullback.condition_assoc, hE'hom, ← app_eq_map_comp_app]
  refine ⟨E', hE', pullback.fst E.hom (D.map g) ≫ e, ?_,
    pullSection (π.app K) G (pullback.fst E.hom (D.map g) ≫ ψ) hψ' g₀, u', hu', ?_, ?_⟩
  · rw [Category.assoc, he, pullback.condition_assoc, ← Functor.map_comp, hg, hE'hom]
  · simp [u', hue]
  · rw [restrictAlong_pullSection, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ht,
      map_pullSection]
    exact pullSection_congr _ _ _ (by simp [u', huψ]) _

include hc hP in
/-- **Surjectivity of the comparison of sections at a cofiltered limit.** Let `Y` be a
quasi-compact quasi-separated étale scheme over a stage `Dₖ`, with base change `m : V ⟶ Y` to the
limit `X`, and let `t` be a section of the inverse image of `G` over `V`. Then there is a stage
`h : D_K ⟶ Dₖ` such that for every étale scheme `V'` over a later stage `D_K'`, with a morphism
`m' : V' ⟶ Y` over `D_K' ⟶ Dₖ` and a factorisation `n : V ⟶ V'` of `m` over `X ⟶ D_K'`, the
section `t` is the restriction along `n` of a section over `V'`. -/
theorem exists_restrictAlong_eq_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] {V : c.pt.Etale}
    (m : V.left ⟶ Y.left) (hm : IsPullback m V.hom Y.hom (c.π.app k))
    (t : ((P)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op V)) :
    ∃ (K : J) (h : K ⟶ k), ∀ ⦃K' : J⦄ (h' : K' ⟶ K) (V' : (D.obj K').Etale)
      (m' : V'.left ⟶ Y.left) (_ : m' ≫ Y.hom = V'.hom ≫ D.map (h' ≫ h))
      (n : V.left ⟶ V'.left) (hn : n ≫ V'.hom = V.hom ≫ c.π.app K'), n ≫ m' = m →
        ∃ s : ((π.app K')^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op V'),
          restrictAlong (π.app K') G (c.π.app K') P (hP K') n hn s = t := by
  classical
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiCompact Y.hom := @quasiCompact_of_compactSpace _ _ Y.hom
    (inferInstanceAs (CompactSpace Y.left)) (inferInstanceAs (QuasiSeparatedSpace (D.obj k)))
  have : QuasiCompact V.hom := MorphismProperty.of_isPullback hm this
  have : CompactSpace V.left := @QuasiCompact.compactSpace_of_compactSpace _ _ V.hom _
    (inferInstanceAs (CompactSpace c.pt))
  -- local descent data around every point of `V`, finitely many of which cover `V`
  choose k₁ f₁ Z v hx H₁ using
    exists_local_section_descent_of_isLimit hc π P hP G Y m hm.w t
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (v x).left)
    (fun x ↦ (v x).left.isOpenMap.isOpen_range) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  have hTcov (x : V.left) : ∃ i : T, x ∈ Set.range (v i).left := by
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ T, x ∈ Set.range (v i).left := by
      simpa using hT (Set.mem_univ x)
    exact ⟨⟨i, hi⟩, hxi⟩
  -- the finitely many local data descend to a common stage `K₀`
  obtain ⟨K₀, h₀, g₀, hg₀⟩ := IsCofiltered.exists_comp_eq_of_finite (ι := T)
    (fun i ↦ k₁ i) (fun i ↦ f₁ i)
  choose E hE e he σ u hu hue hσ using fun i : T ↦ H₁ i h₀ (g₀ i) (hg₀ i)
  -- from a stage `K₁` on, the `Eᵢ` cover
  obtain ⟨K₁, h₁, g₁, hg₁, Hcov⟩ := exists_forall_mem_range_lift_of_isLimit hc Y m hm (ι := T)
    (fun _ ↦ K₀) (fun _ ↦ h₀) E e he (fun x ↦ by
      obtain ⟨i, hxi⟩ := hTcov x
      exact ⟨i, Z i, u i, (hu i).w, v i, hue i, hxi⟩)
  -- the overlaps `Eᵢ ×_{Y ×_{Dₖ} D_{K₀}} Eⱼ`
  have : IsAffineHom (pullback.fst Y.hom (D.map h₀)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparatedSpace ↥(pullback Y.hom (D.map h₀)) :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst Y.hom (D.map h₀))
      (inferInstanceAs (QuasiSeparatedSpace Y.left)) inferInstance
  let τ (i : T) : (E i).left ⟶ pullback Y.hom (D.map h₀) := pullback.lift (e i) (E i).hom (he i)
  have hτf (i : T) : τ i ≫ pullback.fst _ _ = e i := pullback.lift_fst _ _ _
  have hτs (i : T) : τ i ≫ pullback.snd _ _ = (E i).hom := pullback.lift_snd _ _ _
  have (i : T) : Etale (τ i) := by
    have : Etale (τ i ≫ pullback.snd Y.hom (D.map h₀)) := by
      rw [hτs]
      infer_instance
    exact Etale.of_comp (τ i) (pullback.snd Y.hom (D.map h₀))
  let O (i j : T) : (D.obj K₀).Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.fst (τ i) (τ j) ≫ (E i).hom) inferInstance
  have hOhom (i j : T) : (O i j).hom = pullback.fst (τ i) (τ j) ≫ (E i).hom := rfl
  have hOc (i j : T) : CompactSpace (O i j).left := by
    have : QuasiCompact (τ j) := quasiCompact_of_compactSpace (τ j)
    exact inferInstanceAs (CompactSpace ↥(pullback (τ i) (τ j)))
  have hOs (i j : T) : pullback.snd (τ i) (τ j) ≫ (E j).hom = (O i j).hom := by
    rw [hOhom, ← hτs i, ← hτs j, pullback.condition_assoc]
  let oF (i j : T) : O i j ⟶ E i := MorphismProperty.Over.homMk (pullback.fst _ _) rfl
  let oS (i j : T) : O i j ⟶ E j := MorphismProperty.Over.homMk (pullback.snd _ _) (hOs i j)
  have hoe (i j : T) : (oF i j).left ≫ e i = (oS i j).left ≫ e j := by
    change pullback.fst _ _ ≫ e i = pullback.snd _ _ ≫ e j
    rw [← hτf i, ← hτf j, pullback.condition_assoc]
  let F₀ := (π.app K₀)^*[(ModuleCat.{u + 1} Λ)].obj G
  let d (i j : T) : F₀.obj.obj (op (O i j)) :=
    F₀.obj.map (oF i j).op (σ i) - F₀.obj.map (oS i j).op (σ j)
  -- the differences `d i j` vanish at the limit
  let OX (i j : T) : c.pt.Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.snd (O i j).hom (c.π.app K₀)) inferInstance
  have hd (i j : T) : restrictAlong (π.app K₀) G (c.π.app K₀) P (hP K₀)
      (V := O i j) (V' := OX i j) (pullback.fst (O i j).hom (c.π.app K₀)) pullback.condition
        (d i j) = 0 := by
    have hOX : (OX i j).hom = pullback.snd (O i j).hom (c.π.app K₀) := rfl
    -- the maps from the overlap at the limit to `Zᵢ` and `Zⱼ`
    have key (l : T) (o : O i j ⟶ E l) : ∃ ℓ : OX i j ⟶ Z l, ℓ.left ≫ u l =
        pullback.fst (O i j).hom (c.π.app K₀) ≫ o.left := by
      refine ⟨MorphismProperty.Over.homMk ((hu l).lift
        (pullback.fst (O i j).hom (c.π.app K₀) ≫ o.left) (OX i j).hom ?_) ?_, ?_⟩
      · rw [Category.assoc, MorphismProperty.Over.w o, pullback.condition, hOX]
      · exact (hu l).lift_snd _ _ _
      · exact (hu l).lift_fst _ _ _
    obtain ⟨ℓi, hℓi⟩ := key i (oF i j)
    obtain ⟨ℓj, hℓj⟩ := key j (oS i j)
    have hℓ : ℓi ≫ v i = ℓj ≫ v j := by
      apply MorphismProperty.Over.Hom.ext
      apply hm.hom_ext
      · simp only [etale_comp_left, Category.assoc, ← hue, reassoc_of% hℓi, reassoc_of% hℓj,
          hoe]
      · simp only [etale_comp_left, Category.assoc, MorphismProperty.Over.w]
    have e₁ (l : T) (o : O i j ⟶ E l) (ℓ : OX i j ⟶ Z l)
        (hℓ : ℓ.left ≫ u l = pullback.fst (O i j).hom (c.π.app K₀) ≫ o.left) :
        restrictAlong (π.app K₀) G (c.π.app K₀) P (hP K₀) (V := O i j) (V' := OX i j)
          (pullback.fst _ _) pullback.condition (F₀.obj.map o.op (σ l)) =
          ((P)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.map (ℓ ≫ v l).op t := by
      rw [restrictAlong_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hσ,
        map_restrictAlong]
      exact ConcreteCategory.congr_hom (restrictAlong_congr _ _ _ _ _ _ hℓ.symm) _
    simp only [d, map_sub]
    rw [e₁ i (oF i j) ℓi hℓi, e₁ j (oS i j) ℓj hℓj, hℓ, sub_self]
  choose k₂ f₂ H₂ using fun i j ↦
    exists_restrictAlong_eq_zero_of_isLimit hc π P hP G (O i j) (V := OX i j)
      (pullback.fst (O i j).hom (c.π.app K₀))
      (IsPullback.of_hasPullback (O i j).hom (c.π.app K₀)) (d i j) (hd i j)
  -- a stage `K` after all of these
  obtain ⟨K₃, hK₃, a₃, b₃, ha₃, hb₃⟩ := IsCofiltered.exists_comp_eq_of_finite_of_finite g₁
    (fun p : T × T ↦ k₂ p.1 p.2) (fun p ↦ f₂ p.1 p.2)
  let q := IsCofiltered.eqHom (a₃ ≫ h₁) (hK₃ ≫ h₀)
  have hq : q ≫ a₃ ≫ h₁ = q ≫ hK₃ ≫ h₀ := IsCofiltered.eq_condition _ _
  refine ⟨_, q ≫ hK₃ ≫ h₀, fun K' h' V' m' hm' n hn hnm ↦ ?_⟩
  let ℓ : K' ⟶ K₀ := h' ≫ q ≫ hK₃
  have hm'₀ : m' ≫ Y.hom = (V'.hom ≫ D.map ℓ) ≫ D.map h₀ := by
    rw [hm', Category.assoc, ← Functor.map_comp]
    simp [ℓ]
  let Λₗ : V'.left ⟶ pullback Y.hom (D.map h₀) := pullback.lift m' (V'.hom ≫ D.map ℓ) hm'₀
  let W (i : T) : (D.obj K').Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.fst Λₗ (τ i) ≫ V'.hom) inferInstance
  let aW (i : T) : W i ⟶ V' := MorphismProperty.Over.homMk (pullback.fst Λₗ (τ i)) rfl
  have hsnd (i : T) : pullback.snd Λₗ (τ i) ≫ (E i).hom = (W i).hom ≫ D.map ℓ := by
    have := pullback.condition (f := Λₗ) (g := τ i) =≫ pullback.snd _ _
    simpa [τ, Λₗ, W] using this.symm
  let s (i : T) : ((π.app K')^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op (W i)) :=
    restrictAlong (π.app K₀) G (D.map ℓ) (π.app K') (app_eq_map_comp_app π ℓ)
      (pullback.snd Λₗ (τ i)) (hsnd i) (σ i)
  -- the `Wᵢ` cover `V'`
  have hcov (y : V'.left) : ∃ i, y ∈ Set.range (aW i).left := by
    obtain ⟨i, hi⟩ := Hcov (h' ≫ q ≫ a₃) V' m' (by
      rw [hm', Category.assoc, Category.assoc, hq]) y
    refine ⟨i, ?_⟩
    have hℓi : (h' ≫ q ≫ a₃) ≫ g₁ i = ℓ := by simp [ℓ, ha₃]
    have : pullback.lift m' (V'.hom ≫ D.map ((h' ≫ q ≫ a₃) ≫ g₁ i)) (by
        rw [hℓi]; exact hm'₀) = Λₗ := by
      apply pullback.hom_ext
      · simp [Λₗ]
      · simp only [pullback.lift_snd, Λₗ, hℓi]
    rw [this] at hi
    change y ∈ Set.range (pullback.fst Λₗ (τ i))
    rw [Scheme.Pullback.range_fst]
    exact hi
  -- the `sᵢ` agree on the overlaps
  have hcomp (i j : T) : ((π.app K')^*[(ModuleCat.{u + 1} Λ)].obj G).obj.map
      (overlapFst (aW i) (aW j)).op (s i) =
      ((π.app K')^*[(ModuleCat.{u + 1} Λ)].obj G).obj.map (overlapSnd (aW i) (aW j)).op (s j) := by
    let ω : (overlap (aW i) (aW j)).left ⟶ (O i j).left :=
      pullback.lift ((overlapFst (aW i) (aW j)).left ≫ pullback.snd Λₗ (τ i))
        ((overlapSnd (aW i) (aW j)).left ≫ pullback.snd Λₗ (τ j)) (by
          simp only [overlapFst_left, overlapSnd_left, Category.assoc,
            ← pullback.condition]
          exact pullback.condition_assoc _)
    have hω : ω ≫ (O i j).hom = (overlap (aW i) (aW j)).hom ≫ D.map ℓ := by
      change ω ≫ pullback.fst _ _ ≫ (E i).hom = (pullback.fst _ _ ≫ (W i).hom) ≫ _
      rw [pullback.lift_fst_assoc, overlapFst_left, Category.assoc, hsnd, Category.assoc]
    have hωF : (overlapFst (aW i) (aW j)).left ≫ pullback.snd Λₗ (τ i) = ω ≫ (oF i j).left :=
      (pullback.lift_fst _ _ _).symm
    have hωS : (overlapSnd (aW i) (aW j)).left ≫ pullback.snd Λₗ (τ j) = ω ≫ (oS i j).left :=
      (pullback.lift_snd _ _ _).symm
    have h0 := H₂ i j (h' ≫ q ≫ b₃ (i, j)) ℓ (by simp [ℓ, hb₃ (i, j)]) _ ω hω
    rw [← sub_eq_zero, map_restrictAlong, map_restrictAlong, restrictAlong_congr (h := hωF),
      restrictAlong_congr (h := hωS), ← restrictAlong_map _ _ _ _ _ (oF i j) ω hω,
      ← restrictAlong_map _ _ _ _ _ (oS i j) ω hω, ← map_sub]
    exact h0
  obtain ⟨σ', hσ'⟩ := exists_map_eq_of_compatible _ aW hcov s hcomp
  refine ⟨σ', eq_of_forall_exists_map_eq _ _ _ fun x ↦ ?_⟩
  obtain ⟨i, hxi⟩ := hTcov x
  refine ⟨Z i, v i, hxi, ?_⟩
  let ζ : (Z i).left ⟶ (W i).left := pullback.lift ((v i).left ≫ n) (u i) (by
    apply pullback.hom_ext
    · simp [Λₗ, hnm, hτf, hue]
    · simp only [Category.assoc, Λₗ, pullback.lift_snd, hτs, reassoc_of% hn, (hu i).w]
      rw [c.w ℓ, MorphismProperty.Over.w_assoc])
  have hζ : ζ ≫ (W i).hom = (Z i).hom ≫ c.π.app K' := by
    change ζ ≫ pullback.fst _ _ ≫ V'.hom = _
    rw [pullback.lift_fst_assoc, Category.assoc, hn, MorphismProperty.Over.w_assoc]
  have hζa : (v i).left ≫ n = ζ ≫ (aW i).left := (pullback.lift_fst _ _ _).symm
  have hζs : ζ ≫ pullback.snd Λₗ (τ i) = u i := pullback.lift_snd _ _ _
  rw [map_restrictAlong, restrictAlong_congr (h := hζa),
    ← restrictAlong_map (π.app K') G (c.π.app K') P (hP K') (aW i) ζ hζ, hσ',
    restrictAlong_restrictAlong, restrictAlong_congr_hom G (π.app K₀) P _ (c.w ℓ),
    restrictAlong_congr (h := hζs)]
  exact hσ i

end Etale.ModuleSheaf

end AlgebraicGeometry
