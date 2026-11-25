/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections

/-!
# Sections of inverse images of étale sheaves at a cofiltered limit

Let `X = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes over a scheme
`R` with affine transition maps, and let `G` be an abelian étale sheaf on `R`. For a
quasi-compact quasi-separated étale `Dₖ`-scheme `Y` with base change `V = Y ×_{Dₖ} X`, we show
that the sections of the inverse image of `G` over `V` are the filtered colimit of the sections
of the inverse images of `G` over the base changes `Y ×_{Dₖ} Dⱼ`:

- `AlgebraicGeometry.Etale.exists_restrictAlong_eq_zero_of_isLimit` (in
  `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity`): a section over `Y` which
  vanishes on `V` vanishes on `Y ×_{Dₖ} Dⱼ` for `j` large;
- `AlgebraicGeometry.Etale.exists_restrictAlong_eq_of_isLimit`: every section over `V` comes
  from a section over `Y ×_{Dₖ} Dⱼ` for `j` large.

## Implementation details

The second statement is proved by representing sections étale locally by sections of `G`
(`AlgebraicGeometry.Etale.exists_pullSection_eq`), descending the finitely many local data to a
stage (`AlgebraicGeometry.exists_etale_refinement_of_isLimit`,
`AlgebraicGeometry.exists_hom_descent_of_isLimit`, `AlgebraicGeometry.exists_eq_descent_of_isLimit`)
and descending the covering property (`AlgebraicGeometry.exists_forall_mem_range_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.IsCofiltered

/-- In a cofiltered category, finitely many morphisms `fᵢ : kᵢ ⟶ k` with common target are
dominated by a single morphism `h : K ⟶ k`: there are `gᵢ : K ⟶ kᵢ` with `gᵢ ≫ fᵢ = h`. -/
lemma exists_comp_eq_of_finite {C : Type*} [Category* C] [IsCofiltered C] {ι : Type*} [Finite ι]
    {k : C} (k₁ : ι → C) (f₁ : ∀ i, k₁ i ⟶ k) :
    ∃ (K : C) (h : K ⟶ k) (g : ∀ i, K ⟶ k₁ i), ∀ i, g i ≫ f₁ i = h := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists
    (Finset.univ.image (fun i ↦ Over.mk (f₁ i)))
  have hg (i : ι) : Nonempty (S ⟶ Over.mk (f₁ i)) := hS (Finset.mem_image_of_mem _ (by simp))
  exact ⟨S.left, S.hom, fun i ↦ (hg i).some.left, fun i ↦ Over.w (hg i).some⟩

/-- In a cofiltered category, finitely many parallel morphisms `gᵢ : K₁ ⟶ k` and finitely many
morphisms `fⱼ : kⱼ ⟶ k` are dominated by a single morphism `h : K ⟶ k`: there are `a : K ⟶ K₁`
with `a ≫ gᵢ = h` for all `i` and `bⱼ : K ⟶ kⱼ` with `bⱼ ≫ fⱼ = h`. -/
lemma exists_comp_eq_of_finite_of_finite {C : Type*} [Category* C] [IsCofiltered C]
    {ι κ : Type*} [Finite ι] [Finite κ] {k K₁ : C} (g : ι → (K₁ ⟶ k)) (k₁ : κ → C)
    (f₁ : ∀ j, k₁ j ⟶ k) :
    ∃ (K : C) (h : K ⟶ k) (a : K ⟶ K₁) (b : ∀ j, K ⟶ k₁ j),
      (∀ i, a ≫ g i = h) ∧ ∀ j, b j ≫ f₁ j = h := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let O : Finset C := insert k (insert K₁ (Finset.univ.image k₁))
  have hk : k ∈ O := Finset.mem_insert_self _ _
  have hK₁ : K₁ ∈ O := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hk₁ (j : κ) : k₁ j ∈ O := Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  let H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image (fun i ↦ ⟨K₁, k, hK₁, hk, g i⟩) ∪
      Finset.univ.image (fun j ↦ ⟨k₁ j, k, hk₁ j, hk, f₁ j⟩)
  obtain ⟨S, T, hT⟩ := IsCofiltered.inf_exists O H
  exact ⟨S, T hk, T hK₁, fun j ↦ T (hk₁ j),
    fun i ↦ hT hK₁ hk (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))),
    fun j ↦ hT (hk₁ j) hk
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))⟩

end CategoryTheory.IsCofiltered

namespace AlgebraicGeometry

namespace Etale

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c) {R : Scheme.{u}} (π : D ⟶ (Functor.const J).obj R) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

include hc hP in
/-- **Local descent of a morphism to an étale `R`-scheme.** Let `Y` be étale over a stage `Dₖ`,
`m : V ⟶ Y` a morphism over `X ⟶ Dₖ` from an étale `X`-scheme, `a : V'' ⟶ V` étale and
`φ : V'' ⟶ U` a morphism over `R` to an étale `R`-scheme. Around every point of `V''` there is an
affine scheme `E` étale over a later stage `Dₖ₁`, with a morphism `e : E ⟶ Y` and a morphism
`ψ : E ⟶ U` over `R`, such that `E ×_{Dₖ₁} X` maps to `V''` compatibly with `e` and `ψ`. -/
lemma exists_local_descent_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : m ≫ Y.hom = V.hom ≫ c.π.app k) {V'' : c.pt.Etale} (a : V'' ⟶ V) {U : R.Etale}
    (φ : V''.left ⟶ U.left) (hφ : φ ≫ U.hom = V''.hom ≫ P) (z : V''.left) :
    ∃ (k₁ : J) (f₁ : k₁ ⟶ k) (E : (D.obj k₁).Etale) (_ : IsAffine E.left) (e : E.left ⟶ Y.left)
      (_ : e ≫ Y.hom = E.hom ≫ D.map f₁) (ψ : E.left ⟶ U.left)
      (_ : ψ ≫ U.hom = E.hom ≫ π.app k₁) (Z : c.pt.Etale) (u : Z.left ⟶ E.left)
      (_ : IsPullback u Z.hom E.hom (c.π.app k₁)) (w : Z ⟶ V''),
      u ≫ e = w.left ≫ a.left ≫ m ∧ u ≫ ψ = w.left ≫ φ ∧ z ∈ Set.range w.left := by
  let β : V''.left ⟶ pullback Y.hom (c.π.app k) := pullback.lift (a.left ≫ m) V''.hom (by
    rw [Category.assoc, hm, MorphismProperty.Over.w_assoc])
  have : Etale (β ≫ pullback.snd _ _) := by
    rw [pullback.lift_snd]
    infer_instance
  have : Etale β := Etale.of_comp β (pullback.snd _ _)
  obtain ⟨k', f, E, hE, q, hq, e, he, E', π₁, π₂, hπ, γ, -, hγ, hz⟩ :=
    exists_etale_refinement_of_isLimit D c hc Y.hom β z
  have hγ₂ : γ ≫ V''.hom = π₂ := by
    have := congrArg (· ≫ pullback.snd Y.hom (c.π.app k)) hγ
    simpa [β] using this
  have hγ₁ : γ ≫ a.left ≫ m = π₁ ≫ e := by
    have := congrArg (· ≫ pullback.fst Y.hom (c.π.app k)) hγ
    simpa [β] using this
  obtain ⟨k'', f', ψ, hψ, hψφ⟩ := exists_hom_descent_of_isLimit D c hc π q U.hom
    (hπ.isoPullback.inv ≫ γ ≫ φ) (by
      rw [Category.assoc, Category.assoc, hφ, reassoc_of% hγ₂, IsPullback.isoPullback_inv_snd_assoc,
        hP])
  have : IsAffineHom (pullback.fst q (D.map f')) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine (pullback q (D.map f')) := isAffine_of_isAffineHom (pullback.fst q (D.map f'))
  have : Etale π₂ := MorphismProperty.of_isPullback hπ hq
  let u : E' ⟶ pullback q (D.map f') :=
    pullback.lift π₁ (π₂ ≫ c.π.app k'') (by rw [hπ.w, Category.assoc, c.w f'])
  have hu : IsPullback u π₂ (pullback.snd q (D.map f')) (c.π.app k'') := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (D.map f'))
    rw [pullback.lift_fst, c.w f']
    exact hπ
  have hu' : u = hπ.isoPullback.hom ≫ pullback.map q (c.π.app k') q (D.map f') (𝟙 _)
      (c.π.app k'') (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [u]
  refine ⟨k'', f' ≫ f, MorphismProperty.Over.mk ⊤ (pullback.snd q (D.map f')) inferInstance,
    ‹IsAffine (pullback q (D.map f'))›, pullback.fst q (D.map f') ≫ e, ?_, ψ, hψ,
    MorphismProperty.Over.mk ⊤ π₂ inferInstance, u, hu, MorphismProperty.Over.homMk γ hγ₂,
    ?_, ?_, hz⟩
  · simp [he, pullback.condition_assoc]
  · simp [u, hγ₁]
  · simp [hu', hψφ]

include hc in
/-- **Local data covering at the limit cover at a stage.** Let `Y` be quasi-compact and étale
over a stage `Dₖ`, with base change `m : V ⟶ Y` to the limit, and let `eᵢ : Eᵢ ⟶ Y` be finitely
many morphisms over `Dₖᵢ ⟶ Dₖ` from étale `Dₖᵢ`-schemes, such that the points of `V` are covered
by étale `X`-schemes mapping compatibly to `V` and the `Eᵢ`. Then there is a stage `K` over all
the `kᵢ` such that for every `m' : V' ⟶ Y` over a later stage `Dₖ' ⟶ D_K ⟶ Dₖ`, every point of
`V'` lies in the image of some `Eᵢ`, in the sense that its image in `Y ×_{Dₖ} Dₖᵢ` lies in the
image of `Eᵢ`. -/
lemma exists_forall_mem_range_lift_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)]
    {k : J} (Y : (D.obj k).Etale) [CompactSpace Y.left] {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : IsPullback m V.hom Y.hom (c.π.app k)) {ι : Type*} [Finite ι] (k₁ : ι → J)
    (f₁ : ∀ i, k₁ i ⟶ k) (E : ∀ i, (D.obj (k₁ i)).Etale) (e : ∀ i, (E i).left ⟶ Y.left)
    (he : ∀ i, e i ≫ Y.hom = (E i).hom ≫ D.map (f₁ i))
    (hcov : ∀ x : V.left, ∃ (i : ι) (Z : c.pt.Etale) (u : Z.left ⟶ (E i).left)
      (_ : u ≫ (E i).hom = Z.hom ≫ c.π.app (k₁ i)) (v : Z ⟶ V),
        u ≫ e i = v.left ≫ m ∧ x ∈ Set.range v.left) :
    ∃ (K : J) (h : K ⟶ k) (g : ∀ i, K ⟶ k₁ i) (hg : ∀ i, g i ≫ f₁ i = h),
      ∀ ⦃K' : J⦄ (h' : K' ⟶ K) (V' : (D.obj K').Etale) (m' : V'.left ⟶ Y.left)
        (hm' : m' ≫ Y.hom = V'.hom ≫ D.map (h' ≫ h)) (y : V'.left), ∃ i : ι,
        pullback.lift m' (V'.hom ≫ D.map (h' ≫ g i))
          (by rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc, hg])
          y ∈ Set.range (pullback.lift (e i) (E i).hom (he i)) := by
  obtain ⟨K, h, g, hg⟩ := IsCofiltered.exists_comp_eq_of_finite k₁ f₁
  -- the base changes of the `Eᵢ` to the stage `K`, étale over `Y ×_{Dₖ} D_K`
  let eK (i : ι) : pullback (E i).hom (D.map (g i)) ⟶ pullback Y.hom (D.map h) :=
    pullback.map _ _ _ _ (e i) (𝟙 _) (D.map (f₁ i)) (he i).symm (by simp [← hg i])
  have (i : ι) : Etale (eK i) := by
    have : Etale (eK i ≫ pullback.snd Y.hom (D.map h)) := by
      rw [pullback.lift_snd, Category.comp_id]
      infer_instance
    exact Etale.of_comp (eK i) (pullback.snd Y.hom (D.map h))
  have : CompactSpace ↥(pullback Y.hom (D.map h)) := baseChange_compactSpace (Y := Y.left) h Y.hom
  obtain ⟨K₁, f, H⟩ := exists_forall_mem_range_of_isLimit D c hc
    (pullback.snd Y.hom (D.map h)) eK (fun x ↦ by
      let L : pullback (pullback.snd Y.hom (D.map h)) (c.π.app K) ⟶ V.left :=
        hm.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
          rw [Category.assoc, pullback.condition, pullback.condition_assoc, c.w])
      obtain ⟨i, Z, u, hu, v, hv, z, hz⟩ := hcov (L x)
      let M : V.left ⟶ pullback Y.hom (D.map h) :=
        pullback.lift m (V.hom ≫ c.π.app K) (by rw [hm.w, Category.assoc, c.w])
      have hLM : L ≫ M = pullback.fst _ _ := by
        apply pullback.hom_ext
        · simp [L, M]
        · simp [L, M, pullback.condition]
      let uK : Z.left ⟶ pullback (E i).hom (D.map (g i)) :=
        pullback.lift u (Z.hom ≫ c.π.app K) (by rw [hu, Category.assoc, c.w])
      have huv : uK ≫ eK i = v.left ≫ M := by
        apply pullback.hom_ext
        · simp [uK, eK, M, hv]
        · simp [uK, eK, M]
      refine ⟨i, uK z, ?_⟩
      rw [← Scheme.Hom.comp_apply, huv, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, hLM])
  refine ⟨K₁, f ≫ h, fun i ↦ f ≫ g i, fun i ↦ by rw [Category.assoc, hg], ?_⟩
  intro K' h' V' m' hm' y
  let Λ : V'.left ⟶ pullback Y.hom (D.map h) :=
    pullback.lift m' (V'.hom ≫ D.map (h' ≫ f)) (by
      rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc])
  obtain ⟨i, ε, hε⟩ := H K' h' (pullback.lift Λ V'.hom (by simp [Λ]) y)
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst] at hε
  let ρ : pullback Y.hom (D.map h) ⟶ pullback Y.hom (D.map (f₁ i)) :=
    pullback.map _ _ _ _ (𝟙 _) (D.map (g i)) (𝟙 _) (by simp) (by simp [← hg i])
  have key₁ : eK i ≫ ρ = pullback.fst _ _ ≫ pullback.lift (e i) (E i).hom (he i) := by
    apply pullback.hom_ext
    · simp [eK, ρ]
    · simp [eK, ρ, pullback.condition]
  have key₂ : Λ ≫ ρ = pullback.lift m' (V'.hom ≫ D.map (h' ≫ f ≫ g i)) (by
      rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc, Category.assoc, hg]) := by
    apply pullback.hom_ext
    · simp [Λ, ρ]
    · simp [Λ, ρ]
  refine ⟨i, pullback.fst (E i).hom (D.map (g i)) ε, ?_⟩
  calc _ = ρ (eK i ε) := by
        rw [← Scheme.Hom.comp_apply (eK i) ρ, key₁, Scheme.Hom.comp_apply]
        rfl
    _ = ρ (Λ y) := by rw [hε]
    _ = _ := by rw [← Scheme.Hom.comp_apply Λ ρ, key₂]

omit [IsCofiltered J] in
/-- The structure morphisms of the stages to `R` are compatible with the transition maps. -/
lemma app_eq_map_comp_app {k k' : J} (g : k' ⟶ k) : π.app k' = D.map g ≫ π.app k := by
  simp

variable (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- `restrictAlong` only depends on the morphism of base schemes through its value. -/
lemma restrictAlong_congr_hom {T T' : Scheme.{u}} (t : T ⟶ R) {f₁ f₂ : T' ⟶ T} (t' : T' ⟶ R)
    (ht' : t' = f₁ ≫ t) (h : f₁ = f₂) {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left)
    (hm : m ≫ V.hom = V'.hom ≫ f₁) :
    restrictAlong t G f₁ t' ht' m hm = restrictAlong t G f₂ t' (h ▸ ht') m (h ▸ hm) := by
  subst h
  rfl

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
    (t : ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) (x : V.left) :
    ∃ (k₁ : J) (f₁ : k₁ ⟶ k) (Z : c.pt.Etale) (v : Z ⟶ V), x ∈ Set.range v.left ∧
      ∀ ⦃K : J⦄ (h : K ⟶ k) (g : K ⟶ k₁), g ≫ f₁ = h →
        ∃ (E : (D.obj K).Etale) (_ : IsAffine E.left) (e : E.left ⟶ Y.left)
          (_ : e ≫ Y.hom = E.hom ≫ D.map h)
          (σ : ((π.app K)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op E))
          (u : Z.left ⟶ E.left) (hu : IsPullback u Z.hom E.hom (c.π.app K)),
          u ≫ e = v.left ≫ m ∧
            restrictAlong (π.app K) G (c.π.app K) P (hP K) u hu.w σ =
              ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.map v.op t := by
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
    (t : ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    ∃ (K : J) (h : K ⟶ k), ∀ ⦃K' : J⦄ (h' : K' ⟶ K) (V' : (D.obj K').Etale)
      (m' : V'.left ⟶ Y.left) (_ : m' ≫ Y.hom = V'.hom ≫ D.map (h' ≫ h))
      (n : V.left ⟶ V'.left) (hn : n ≫ V'.hom = V.hom ≫ c.π.app K'), n ≫ m' = m →
        ∃ s : ((π.app K')^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V'),
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
  let F₀ := (π.app K₀)^*[AddCommGrpCat.{u + 1}].obj G
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
          ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.map (ℓ ≫ v l).op t := by
      rw [restrictAlong_map, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hσ,
        map_restrictAlong]
      exact ConcreteCategory.congr_hom (restrictAlong_congr _ _ _ _ _ _ hℓ.symm) _
    simp only [d, map_sub]
    rw [e₁ i (oF i j) ℓi hℓi, e₁ j (oS i j) ℓj hℓj, hℓ, sub_self]
  choose k₂ f₂ H₂ using fun i j ↦
    have := hOc i j
    exists_restrictAlong_eq_zero_of_isLimit π P hP G hc (O i j) (d i j) (hd i j)
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
  let Λ : V'.left ⟶ pullback Y.hom (D.map h₀) := pullback.lift m' (V'.hom ≫ D.map ℓ) hm'₀
  let W (i : T) : (D.obj K').Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.fst Λ (τ i) ≫ V'.hom) inferInstance
  let aW (i : T) : W i ⟶ V' := MorphismProperty.Over.homMk (pullback.fst Λ (τ i)) rfl
  have hsnd (i : T) : pullback.snd Λ (τ i) ≫ (E i).hom = (W i).hom ≫ D.map ℓ := by
    have := pullback.condition (f := Λ) (g := τ i) =≫ pullback.snd _ _
    simpa [τ, Λ, W] using this.symm
  let s (i : T) : ((π.app K')^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (W i)) :=
    restrictAlong (π.app K₀) G (D.map ℓ) (π.app K') (app_eq_map_comp_app π ℓ)
      (pullback.snd Λ (τ i)) (hsnd i) (σ i)
  -- the `Wᵢ` cover `V'`
  have hcov (y : V'.left) : ∃ i, y ∈ Set.range (aW i).left := by
    obtain ⟨i, hi⟩ := Hcov (h' ≫ q ≫ a₃) V' m' (by
      rw [hm', Category.assoc, Category.assoc, hq]) y
    refine ⟨i, ?_⟩
    have hℓi : (h' ≫ q ≫ a₃) ≫ g₁ i = ℓ := by simp [ℓ, ha₃]
    have : pullback.lift m' (V'.hom ≫ D.map ((h' ≫ q ≫ a₃) ≫ g₁ i)) (by
        rw [hℓi]; exact hm'₀) = Λ := by
      apply pullback.hom_ext
      · simp [Λ]
      · simp only [pullback.lift_snd, Λ, hℓi]
    rw [this] at hi
    change y ∈ Set.range (pullback.fst Λ (τ i))
    rw [Scheme.Pullback.range_fst]
    exact hi
  -- the `sᵢ` agree on the overlaps
  have hcomp (i j : T) : ((π.app K')^*[AddCommGrpCat.{u + 1}].obj G).obj.map
      (overlapFst (aW i) (aW j)).op (s i) =
      ((π.app K')^*[AddCommGrpCat.{u + 1}].obj G).obj.map (overlapSnd (aW i) (aW j)).op (s j) := by
    let ω : (overlap (aW i) (aW j)).left ⟶ (O i j).left :=
      pullback.lift ((overlapFst (aW i) (aW j)).left ≫ pullback.snd Λ (τ i))
        ((overlapSnd (aW i) (aW j)).left ≫ pullback.snd Λ (τ j)) (by
          simp only [overlapFst_left, overlapSnd_left, Category.assoc,
            ← pullback.condition]
          exact pullback.condition_assoc _)
    have hω : ω ≫ (O i j).hom = (overlap (aW i) (aW j)).hom ≫ D.map ℓ := by
      change ω ≫ pullback.fst _ _ ≫ (E i).hom = (pullback.fst _ _ ≫ (W i).hom) ≫ _
      rw [pullback.lift_fst_assoc, overlapFst_left, Category.assoc, hsnd, Category.assoc]
    have hωF : (overlapFst (aW i) (aW j)).left ≫ pullback.snd Λ (τ i) = ω ≫ (oF i j).left :=
      (pullback.lift_fst _ _ _).symm
    have hωS : (overlapSnd (aW i) (aW j)).left ≫ pullback.snd Λ (τ j) = ω ≫ (oS i j).left :=
      (pullback.lift_snd _ _ _).symm
    have hℓ : (h' ≫ q ≫ b₃ (i, j)) ≫ f₂ i j = ℓ := by simp [ℓ, hb₃ (i, j)]
    have h0 := H₂ i j _ (h' ≫ q ≫ b₃ (i, j)) _ ω (by rw [hℓ]; exact hω)
    rw [restrictAlong_congr_hom G (π.app K₀) (π.app K') _ (congrArg D.map hℓ)] at h0
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
    · simp [Λ, hnm, hτf, hue]
    · simp only [Category.assoc, Λ, pullback.lift_snd, hτs, reassoc_of% hn, (hu i).w]
      rw [c.w ℓ, MorphismProperty.Over.w_assoc])
  have hζ : ζ ≫ (W i).hom = (Z i).hom ≫ c.π.app K' := by
    change ζ ≫ pullback.fst _ _ ≫ V'.hom = _
    rw [pullback.lift_fst_assoc, Category.assoc, hn, MorphismProperty.Over.w_assoc]
  have hζa : (v i).left ≫ n = ζ ≫ (aW i).left := (pullback.lift_fst _ _ _).symm
  have hζs : ζ ≫ pullback.snd Λ (τ i) = u i := pullback.lift_snd _ _ _
  rw [map_restrictAlong, restrictAlong_congr (h := hζa),
    ← restrictAlong_map (π.app K') G (c.π.app K') P (hP K') (aW i) ζ hζ, hσ',
    restrictAlong_restrictAlong, restrictAlong_congr_hom G (π.app K₀) P _ (c.w ℓ),
    restrictAlong_congr (h := hζs)]
  exact hσ i

end Etale

end AlgebraicGeometry
