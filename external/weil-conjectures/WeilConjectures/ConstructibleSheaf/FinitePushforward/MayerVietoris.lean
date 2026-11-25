/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Generators
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Mayer–Vietoris for extensions by zero

For an étale `v : W ⟶ X`, maps `v_! Λ ⟶ G` are the sections of `G` over `W`
(`AlgebraicGeometry.Etale.sectionHom`). If `W = W₁ ∪ W₂` is a union of two opens, the sheaf
condition for `G` on this cover therefore exhibits `v_! Λ` as the cokernel of
`(v₁₂)_! Λ ⟶ (v₁)_! Λ ⊞ (v₂)_! Λ`, so `v_! Λ` is constructible as soon as the three pieces are
(`AlgebraicGeometry.Etale.isConstructibleSheaf_etaleLowerShriek_of_sup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The extension by zero `v_! Λ` of the constant sheaf `Λ` along an étale `v`. -/
noncomputable abbrev Etale.lowerShriekUnit {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v h).obj
    ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

lemma Etale.sectionHom_surjective (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) :
    Function.Surjective (Etale.sectionHom F v h) := by
  intro g
  let φ := ((constantSheafAdj W.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (MorphismProperty.Over.mkIdTerminal @Etale W)).homEquiv _ _)
      (((Etale.etaleLowerShriekLocalizationAdjunction v h).homEquiv _ _) g)
  refine ⟨φ.hom 1, ?_⟩
  have : ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (φ.hom 1)) = φ := by
    ext; simp
  rw [Etale.sectionHom]
  erw [this]
  simp [φ]

/-- The canonical section of `v_! Λ` over `v`, corresponding to the identity of `v_! Λ`. -/
noncomputable def Etale.unitSection {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) :
    (Etale.lowerShriekUnit (Λ := Λ) v h).obj.obj (op (Etale.self v h)) :=
  (Etale.sectionHom_surjective _ v h (𝟙 _)).choose

lemma Etale.sectionHom_unitSection {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) :
    Etale.sectionHom _ v h (Etale.unitSection (Λ := Λ) v h) = 𝟙 _ :=
  (Etale.sectionHom_surjective _ v h (𝟙 _)).choose_spec

/-- **Yoneda for `v_! Λ`.** Every map `v_! Λ ⟶ G` is the map attached to its value on the
canonical section. -/
lemma Etale.eq_sectionHom {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : Etale.lowerShriekUnit v h ⟶ G) :
    g = Etale.sectionHom G v h (g.hom.app _ (Etale.unitSection v h)) := by
  rw [← Etale.sectionHom_comp, Etale.sectionHom_unitSection, Category.id_comp]

lemma Etale.sectionHom_app_unitSection {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (σ : G.obj.obj (op (Etale.self v h))) :
    (Etale.sectionHom G v h σ).hom.app _ (Etale.unitSection v h) = σ := by
  apply Etale.sectionHom_injective G v h
  rw [← Etale.eq_sectionHom]


section Open

variable {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v)

/-- The inclusion of the étale `X`-scheme `V' ⟶ W ⟶ X` of an open `V'` of `W` into `W`. -/
noncomputable def Etale.selfOpenHom (V' : W.Opens) :
    Etale.self (V'.ι ≫ v) inferInstance ⟶ Etale.self v h :=
  MorphismProperty.Over.homMk V'.ι
    ((congrArg (V'.ι ≫ ·) (Category.id_comp v)).trans (Category.id_comp _).symm) trivial

/-- The map `(v ∘ ι)_! Λ ⟶ v_! Λ` induced by an open `ι : V' ⟶ W`. -/
noncomputable def Etale.lowerShriekUnitOpenHom (V' : W.Opens) :
    Etale.lowerShriekUnit (Λ := Λ) (V'.ι ≫ v) inferInstance ⟶ Etale.lowerShriekUnit v h :=
  Etale.sectionHom _ (V'.ι ≫ v) inferInstance
    ((Etale.lowerShriekUnit v h).obj.map (Etale.selfOpenHom v h V').op (Etale.unitSection v h))

lemma Etale.lowerShriekUnitOpenHom_comp (V' : W.Opens)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : Etale.lowerShriekUnit v h ⟶ G) :
    Etale.lowerShriekUnitOpenHom v h V' ≫ g = Etale.sectionHom G (V'.ι ≫ v) inferInstance
      (G.obj.map (Etale.selfOpenHom v h V').op (g.hom.app _ (Etale.unitSection v h))) := by
  rw [Etale.lowerShriekUnitOpenHom, Etale.sectionHom_comp, NatTrans.naturality_apply]

end Open


section Glue

variable {W : Scheme.{u}} (v : W ⟶ X) (h : Etale v) (V₁ V₂ : W.Opens)

/-- The inclusion of the étale `X`-scheme of an open `V'` into that of a larger open `V''`. -/
noncomputable def Etale.selfOpenHomOfLE {V' V'' : W.Opens} (hle : V' ≤ V'') :
    Etale.self (V'.ι ≫ v) inferInstance ⟶ Etale.self (V''.ι ≫ v) inferInstance :=
  MorphismProperty.Over.homMk (W.homOfLE hle)
    ((congrArg (W.homOfLE hle ≫ ·) (Category.id_comp _)).trans
      ((W.homOfLE_ι_assoc hle v).trans (Category.id_comp _).symm)) trivial

lemma Etale.selfOpenHomOfLE_comp {V' V'' : W.Opens} (hle : V' ≤ V'') :
    Etale.selfOpenHomOfLE v h hle ≫ Etale.selfOpenHom v h V'' = Etale.selfOpenHom v h V' :=
  MorphismProperty.Over.Hom.ext (W.homOfLE_ι hle)

/-- **Sections over a union of two opens glue.** -/
lemma Etale.existsUnique_glue_sup (hV : V₁ ⊔ V₂ = ⊤)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (s₁ : G.obj.obj (op (Etale.self (V₁.ι ≫ v) inferInstance)))
    (s₂ : G.obj.obj (op (Etale.self (V₂.ι ≫ v) inferInstance)))
    (hs : G.obj.map (Etale.selfOpenHomOfLE v h (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      G.obj.map (Etale.selfOpenHomOfLE v h (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op s₂) :
    ∃! s : G.obj.obj (op (Etale.self v h)),
      G.obj.map (Etale.selfOpenHom v h V₁).op s = s₁ ∧
        G.obj.map (Etale.selfOpenHom v h V₂).op s = s₂ := by
  let V : Bool → W.Opens := fun b ↦ bif b then V₁ else V₂
  let Z : Bool → X.Etale := fun b ↦ Etale.self ((V b).ι ≫ v) inferInstance
  let f : ∀ b, Z b ⟶ Etale.self v h := fun b ↦ Etale.selfOpenHom v h (V b)
  have hcov : Sieve.ofArrows Z f ∈ X.smallEtaleTopology (Etale.self v h) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    have hy : y ∈ V₁ ⊔ V₂ := by rw [hV]; trivial
    rcases hy with hy | hy
    · exact Set.mem_iUnion.mpr ⟨true, ⟨⟨y, hy⟩, rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨false, ⟨⟨y, hy⟩, rfl⟩⟩
  have hG := (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology G.obj
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).1 G.property
  rw [isSheaf_iff_isSheaf_of_type] at hG
  have hsh := Presieve.IsSheaf.isSheafFor hG (Presieve.ofArrows Z f) hcov
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hmono (b : Bool) : Mono (f b) := ⟨fun g₁ g₂ hg ↦ MorphismProperty.Over.Hom.ext
    ((cancel_mono (V b).ι).1 (congrArg (fun g ↦ g.left) hg :))⟩
  -- a common refinement factors through the intersection
  have hfac {T : X.Etale} (g₁ : T ⟶ Z true) (g₂ : T ⟶ Z false)
      (hg : g₁ ≫ f true = g₂ ≫ f false) : ∃ k : T ⟶ Etale.self ((V₁ ⊓ V₂).ι ≫ v) inferInstance,
        k ≫ Etale.selfOpenHomOfLE v h inf_le_left = g₁ ∧
          k ≫ Etale.selfOpenHomOfLE v h inf_le_right = g₂ := by
    have hg' : g₁.left ≫ V₁.ι = g₂.left ≫ V₂.ι := congrArg (fun g ↦ g.left) hg
    have hr : Set.range (g₁.left ≫ V₁.ι).base ⊆ Set.range (V₁ ⊓ V₂).ι.base := by
      rintro _ ⟨t, rfl⟩
      have e : (show V₁ from g₁.left t).1 = (show V₂ from g₂.left t).1 := by
        exact congrArg (fun φ : T.left ⟶ W ↦ φ t) hg'
      exact ⟨⟨_, (show V₁ from g₁.left t).2, e ▸ (show V₂ from g₂.left t).2⟩, rfl⟩
    let l := IsOpenImmersion.lift (V₁ ⊓ V₂).ι (g₁.left ≫ V₁.ι) hr
    have hl : l ≫ (V₁ ⊓ V₂).ι = g₁.left ≫ V₁.ι := IsOpenImmersion.lift_fac _ _ _
    refine ⟨MorphismProperty.Over.homMk l ?_ trivial, ?_, ?_⟩
    · calc l ≫ (𝟙 _ ≫ (V₁ ⊓ V₂).ι ≫ v) = (l ≫ (V₁ ⊓ V₂).ι) ≫ v := by
            rw [Category.id_comp, Category.assoc]
        _ = g₁.left ≫ (𝟙 _ ≫ V₁.ι ≫ v) := by rw [hl, Category.id_comp, Category.assoc]
        _ = T.hom := MorphismProperty.Over.w g₁
    · refine MorphismProperty.Over.Hom.ext ((cancel_mono V₁.ι).1 ?_)
      change (l ≫ W.homOfLE inf_le_left) ≫ V₁.ι = _
      rw [Category.assoc, W.homOfLE_ι, hl]
    · refine MorphismProperty.Over.Hom.ext ((cancel_mono V₂.ι).1 ?_)
      change (l ≫ W.homOfLE inf_le_right) ≫ V₂.ι = _
      rw [Category.assoc, W.homOfLE_ι, hl, hg']
  obtain ⟨s, hs', hsu⟩ := hsh (fun b ↦ Bool.rec (motive := fun b ↦
      ((G.obj ⋙ CategoryTheory.forget _).obj (op (Z b)))) s₂ s₁ b) (by
    intro b b' T g₁ g₂ hg
    cases b <;> cases b'
    · obtain rfl : g₁ = g₂ := (cancel_mono (f false)).1 hg
      rfl
    · obtain ⟨k, hk₁, hk₂⟩ := hfac g₂ g₁ hg.symm
      change G.obj.map g₁.op s₂ = G.obj.map g₂.op s₁
      rw [← hk₁, ← hk₂]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [hs]
      rfl
    · obtain ⟨k, hk₁, hk₂⟩ := hfac g₁ g₂ hg
      change G.obj.map g₁.op s₁ = G.obj.map g₂.op s₂
      rw [← hk₁, ← hk₂]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [hs]
      rfl
    · obtain rfl : g₁ = g₂ := (cancel_mono (f true)).1 hg
      rfl)
  exact ⟨s, ⟨hs' true, hs' false⟩, fun s' ⟨h₁, h₂⟩ ↦ hsu s' fun b ↦ by cases b <;> assumption⟩


/-- The map `(v ∘ ι')_! Λ ⟶ (v ∘ ι'')_! Λ` induced by an inclusion of opens `V' ≤ V''`. -/
noncomputable def Etale.lowerShriekUnitHomOfLE {V' V'' : W.Opens} (hle : V' ≤ V'') :
    Etale.lowerShriekUnit (Λ := Λ) (V'.ι ≫ v) inferInstance ⟶
      Etale.lowerShriekUnit (V''.ι ≫ v) inferInstance :=
  Etale.sectionHom _ (V'.ι ≫ v) inferInstance
    ((Etale.lowerShriekUnit (V''.ι ≫ v) inferInstance).obj.map
      (Etale.selfOpenHomOfLE v h hle).op (Etale.unitSection (V''.ι ≫ v) inferInstance))

lemma Etale.lowerShriekUnitHomOfLE_comp {V' V'' : W.Opens} (hle : V' ≤ V'')
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : Etale.lowerShriekUnit (V''.ι ≫ v) inferInstance ⟶ G) :
    Etale.lowerShriekUnitHomOfLE v h hle ≫ g = Etale.sectionHom G (V'.ι ≫ v) inferInstance
      (G.obj.map (Etale.selfOpenHomOfLE v h hle).op
        (g.hom.app _ (Etale.unitSection (V''.ι ≫ v) inferInstance))) := by
  rw [Etale.lowerShriekUnitHomOfLE, Etale.sectionHom_comp, NatTrans.naturality_apply]

/-- **Mayer–Vietoris for extensions by zero.** If `W = V₁ ∪ V₂`, then `v_! Λ` is the cokernel
of `(v₁₂)_! Λ ⟶ (v₁)_! Λ ⊞ (v₂)_! Λ`. -/
theorem Etale.exists_isColimit_cokernelCofork_lowerShriekUnit (hV : V₁ ⊔ V₂ = ⊤) :
    let α := biprod.lift (Etale.lowerShriekUnitHomOfLE (Λ := Λ) v h inf_le_left)
      (-Etale.lowerShriekUnitHomOfLE (Λ := Λ) v h inf_le_right)
    let π := biprod.desc (Etale.lowerShriekUnitOpenHom (Λ := Λ) v h V₁)
      (Etale.lowerShriekUnitOpenHom (Λ := Λ) v h V₂)
    ∃ w : α ≫ π = 0, Nonempty (IsColimit (CokernelCofork.ofπ π w)) := by
  intro α π
  -- restrictions of sections
  have key {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : _ ⟶ G) (V' : W.Opens)
      (hle : V₁ ⊓ V₂ ≤ V') :
      Etale.lowerShriekUnitHomOfLE v h hle ≫ Etale.lowerShriekUnitOpenHom v h V' ≫ g =
        Etale.sectionHom G _ inferInstance (G.obj.map (Etale.selfOpenHom v h (V₁ ⊓ V₂)).op
          (g.hom.app _ (Etale.unitSection v h))) := by
    rw [Etale.lowerShriekUnitHomOfLE_comp, Etale.lowerShriekUnitOpenHom_comp,
      Etale.sectionHom_app_unitSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, Etale.selfOpenHomOfLE_comp]
  have hw : α ≫ π = 0 := by
    simp only [α, π, biprod.lift_desc, Preadditive.neg_comp]
    rw [← Category.comp_id (Etale.lowerShriekUnitOpenHom v h V₁),
      ← Category.comp_id (Etale.lowerShriekUnitOpenHom v h V₂), key, key, add_neg_cancel]
  -- the sections attached to a map out of `(v₁)_! Λ ⊞ (v₂)_! Λ` killing `α` are compatible
  have hcompat {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : _ ⟶ G)
      (hg : α ≫ g = 0) :
      G.obj.map (Etale.selfOpenHomOfLE v h (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op
          ((biprod.inl ≫ g).hom.app _ (Etale.unitSection _ inferInstance)) =
        G.obj.map (Etale.selfOpenHomOfLE v h (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op
          ((biprod.inr ≫ g).hom.app _ (Etale.unitSection _ inferInstance)) := by
    have h0 : Etale.lowerShriekUnitHomOfLE v h inf_le_left ≫ biprod.inl ≫ g =
        Etale.lowerShriekUnitHomOfLE v h inf_le_right ≫ biprod.inr ≫ g := by
      have e : α ≫ g = Etale.lowerShriekUnitHomOfLE v h inf_le_left ≫ biprod.inl ≫ g -
          Etale.lowerShriekUnitHomOfLE v h inf_le_right ≫ biprod.inr ≫ g := by
        simp only [α, biprod.lift_eq, Preadditive.add_comp, Preadditive.neg_comp,
          Category.assoc, sub_eq_add_neg]
      rw [e, sub_eq_zero] at hg
      exact hg
    rw [Etale.lowerShriekUnitHomOfLE_comp, Etale.lowerShriekUnitHomOfLE_comp] at h0
    exact Etale.sectionHom_injective G _ inferInstance h0
  let s {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : _ ⟶ G) (hg : α ≫ g = 0) :
      G.obj.obj (op (Etale.self v h)) :=
    (Etale.existsUnique_glue_sup v h V₁ V₂ hV G _ _ (hcompat g hg)).exists.choose
  have hs {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : _ ⟶ G) (hg : α ≫ g = 0) :=
    (Etale.existsUnique_glue_sup v h V₁ V₂ hV G _ _ (hcompat g hg)).exists.choose_spec
  refine ⟨hw, ⟨CokernelCofork.IsColimit.ofπ π hw (fun {G} g hg ↦ Etale.sectionHom G v h (s g hg))
    (fun {G} g hg ↦ ?_) (fun {G} g hg m hm ↦ ?_)⟩⟩
  · refine biprod.hom_ext' _ _ ?_ ?_
    · rw [← Category.assoc, biprod.inl_desc, Etale.lowerShriekUnitOpenHom_comp,
        Etale.sectionHom_app_unitSection, (hs g hg).1, ← Etale.eq_sectionHom]
    · rw [← Category.assoc, biprod.inr_desc, Etale.lowerShriekUnitOpenHom_comp,
        Etale.sectionHom_app_unitSection, (hs g hg).2, ← Etale.eq_sectionHom]
  · rw [Etale.eq_sectionHom v h m]
    congr 1
    refine (Etale.existsUnique_glue_sup v h V₁ V₂ hV G _ _ (hcompat g hg)).unique ⟨?_, ?_⟩
      (hs g hg)
    · apply Etale.sectionHom_injective G _ inferInstance
      rw [← Etale.lowerShriekUnitOpenHom_comp, ← biprod.inl_desc_assoc
        (Etale.lowerShriekUnitOpenHom v h V₁) (Etale.lowerShriekUnitOpenHom v h V₂)]
      change biprod.inl ≫ π ≫ m = _
      rw [hm, ← Etale.eq_sectionHom]
    · apply Etale.sectionHom_injective G _ inferInstance
      rw [← Etale.lowerShriekUnitOpenHom_comp, ← biprod.inr_desc_assoc
        (Etale.lowerShriekUnitOpenHom v h V₁) (Etale.lowerShriekUnitOpenHom v h V₂)]
      change biprod.inr ≫ π ≫ m = _
      rw [hm, ← Etale.eq_sectionHom]

/-- **Extensions by zero along a union of two opens.** If `W = V₁ ∪ V₂` and the extensions by
zero of `Λ` along `V₁`, `V₂` and `V₁ ∩ V₂` are constructible, so is `v_! Λ`. -/
theorem Etale.isConstructibleSheaf_lowerShriekUnit_of_sup (hV : V₁ ⊔ V₂ = ⊤)
    (h₁ : IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) (V₁.ι ≫ v) inferInstance))
    (h₂ : IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) (V₂.ι ≫ v) inferInstance))
    (h₁₂ : IsConstructibleSheaf
      (Etale.lowerShriekUnit (Λ := Λ) ((V₁ ⊓ V₂).ι ≫ v) inferInstance)) :
    IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) v h) := by
  obtain ⟨w, ⟨hc⟩⟩ := Etale.exists_isColimit_cokernelCofork_lowerShriekUnit (Λ := Λ) v h V₁ V₂ hV
  have := IsConstructibleSheaf.biprod (F := Etale.lowerShriekUnit (Λ := Λ) (V₁.ι ≫ v)
    inferInstance) (G := Etale.lowerShriekUnit (Λ := Λ) (V₂.ι ≫ v) inferInstance)
  have := IsConstructibleSheaf.cokernel (biprod.lift
    (Etale.lowerShriekUnitHomOfLE (Λ := Λ) v h (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
    (-Etale.lowerShriekUnitHomOfLE (Λ := Λ) v h (inf_le_right : V₁ ⊓ V₂ ≤ V₂)))
  exact IsConstructibleSheaf.of_iso (F := cokernel (biprod.lift
    (Etale.lowerShriekUnitHomOfLE (Λ := Λ) v h (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
    (-Etale.lowerShriekUnitHomOfLE (Λ := Λ) v h (inf_le_right : V₁ ⊓ V₂ ≤ V₂))))
    ((cokernelIsCokernel _).coconePointUniqueUpToIso hc)

end Glue

end AlgebraicGeometry
