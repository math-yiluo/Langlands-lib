/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus

/-!
# Continuity of sections of étale sheaves at inverse limits

For a cofiltered system `(Dⱼ)` of quasi-compact quasi-separated schemes over `R` with affine
transition maps and limit `X`, the comparison maps `AlgebraicGeometry.Etale.unitComparison`
exhibit the sections of the pullback of an abelian étale sheaf `G` on `R` over `W ×_R X` as the
colimit of the sections over the `W ×_R Dⱼ`, for `W` quasi-compact and quasi-separated étale
over a quasi-separated `R` (`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`).

## Main statements

- `AlgebraicGeometry.Etale.exists_unitComparison_app_eq_zero_of_isLimit`: a section over
  `W ×_R Dⱼ` which vanishes on `W ×_R X` vanishes on some `W ×_R Dⱼ'`.
- `AlgebraicGeometry.Etale.unitComparison_app_surjective_of_isLimit`: every section over
  `W ×_R X` comes from some `W ×_R Dⱼ`.
- `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`: both together.

## Implementation details

*Injectivity.* A section `s` over a quasi-compact étale `Dⱼ`-scheme `V` whose restriction to
`V ×_{Dⱼ} X` vanishes, vanishes étale locally near the image of `V ×_{Dⱼ} X`; this is an open
subset of `V` (the vanishing locus of `s`). Since the `V ×_{Dⱼ} Dⱼ'` are quasi-compact with
limit `V ×_{Dⱼ} X`, the open already contains the image of some `V ×_{Dⱼ} Dⱼ'`
(`AlgebraicGeometry.exists_map_eq_top`), and `s` vanishes there
(`AlgebraicGeometry.Etale.exists_restrictAlong_eq_zero_of_isLimit`).

*Surjectivity.* A section `t` over `W ×_R X` is, on finitely many affine étale pieces `Vₐ`
covering `W ×_R X`, the pullback `φₐ^* gₐ` of sections of `G`. Each `Vₐ` descends to an affine
étale scheme over some stage
(`AlgebraicGeometry.Scheme.exists_isPullback_of_etale_of_isAffineOpen`), together with `φₐ` and
the map to `W` (`AlgebraicGeometry.Scheme.exists_isPullbackLift_comp_eq`). The pulled back sections
at a common stage agree on the overlaps after passing to a later stage, by injectivity, the
descended pieces cover `W ×_R Dⱼ` at a later stage, and they glue to the required section.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

section RestrictAlong

variable {R T T' : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  (f : T' ⟶ T) (t' : T' ⟶ R) (ht' : t' = f ≫ t)

/-- The restriction of a section `s` of `t^* G` along `m` vanishes as soon as the image of `m`
lies in the vanishing locus of `s`. -/
lemma restrictAlong_eq_zero_of_range_subset {V : T.Etale} {V' : T'.Etale}
    (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f)
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V))
    (h : Set.range m ⊆ vanishingLocus ((t)^*[AddCommGrpCat.{u + 1}].obj G) s) :
    restrictAlong t G f t' ht' m hm s = 0 := by
  have hx (x : V'.left) := h ⟨x, rfl⟩
  choose V₁ a ha hs using hx
  choose w hw using ha
  refine eq_zero_of_forall_map_eq_zero _ (fun x ↦ pullbackObjFst m (a x)) (fun x ↦ ?_) _
    (fun x ↦ ?_)
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x (w x) (hw x).symm
    exact ⟨x, z, hz⟩
  · have wa : (a x).left ≫ V.hom = (V₁ x).hom := MorphismProperty.Over.w (a x)
    have hsnd : pullback.snd m (a x).left ≫ (V₁ x).hom = (pullbackObj m (a x)).hom ≫ f := by
      rw [pullbackObj_hom, Category.assoc, ← hm, ← wa, ← pullback.condition_assoc]
    rw [map_restrictAlong, restrictAlong_congr (h := show (pullbackObjFst m (a x)).left ≫ m =
      pullback.snd m (a x).left ≫ (a x).left from pullback.condition),
      ← restrictAlong_map _ _ _ _ _ (a x) _ hsnd, hs x, map_zero]

end RestrictAlong

section Injectivity

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}} {R : Scheme.{u}}
  (π : D ⟶ (Functor.const J).obj R) {c : Cone D} (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **Injectivity of continuity of sections, local form.** Let `s` be a section of the
pullback of `G` to a stage `Dⱼ` over a quasi-compact étale `Dⱼ`-scheme `V`, whose restriction
to `V ×_{Dⱼ} lim Dᵢ` vanishes. Then `s` restricts to zero along every morphism over
`Dₖ ⟶ Dⱼ'`, for some `j' ⟶ j` and all `k ⟶ j'`. -/
lemma exists_restrictAlong_eq_zero_of_isLimit [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    (hc : IsLimit c) {j : J} (V : (D.obj j).Etale) [CompactSpace V.left]
    (s : ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V))
    (hs : restrictAlong (π.app j) G (c.π.app j) P (hP j)
      (V' := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j)).obj V)
      (pullback.fst V.hom (c.π.app j)) pullback.condition s = 0) :
    ∃ (j' : J) (f : j' ⟶ j), ∀ (k : J) (g : k ⟶ j') (V'' : (D.obj k).Etale)
      (m : V''.left ⟶ V.left) (hm : m ≫ V.hom = V''.hom ≫ D.map (g ≫ f)),
      restrictAlong (π.app j) G (D.map (g ≫ f)) (π.app k) (by simp) m hm s = 0 := by
  have hO := range_subset_vanishingLocus_of_restrictAlong_eq_zero (π.app j) G (c.π.app j) P
    (hP j) _ pullback.condition s hs
  let O : V.left.Opens := ⟨vanishingLocus _ s, isOpen_vanishingLocus s⟩
  let i : Over j := Over.mk (𝟙 j)
  let U := pullback.fst V.hom (D.map i.hom) ⁻¹ᵁ O
  have : CompactSpace ((𝟭 Scheme).obj V.left) := ‹CompactSpace V.left›
  obtain ⟨j₁, fji, hj₁⟩ := exists_map_eq_top (baseChangeDiagram D V.hom)
    (baseChangeCone D c V.hom) (isLimitBaseChangeCone D c V.hom hc) (i := i) U (by
      ext z
      simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top,
        Set.mem_univ, iff_true, U]
      have h := hO ⟨z, rfl⟩
      rw [← baseChangeCone_π_app_fst D c V.hom i, Scheme.Hom.comp_apply] at h
      exact h)
  refine ⟨j₁.left, j₁.hom, fun k g V'' m hm ↦ restrictAlong_eq_zero_of_range_subset _ _ _ _ _ _
    _ _ ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.hom)
    (g := D.map (g ≫ j₁.hom)) (m x) (V''.hom x) (by simpa using congr($hm x))
  have h₁ : pullback.fst V.hom (D.map (g ≫ j₁.hom)) ⁻¹ᵁ O = ⊤ := by
    have e : pullback.fst V.hom (D.map (g ≫ j₁.hom)) =
        pullback.map V.hom (D.map (g ≫ j₁.hom)) V.hom (D.map j₁.hom) (𝟙 _) (D.map g) (𝟙 _)
          (by simp) (by simp) ≫ (baseChangeDiagram D V.hom).map fji ≫
          pullback.fst V.hom (D.map i.hom) := by simp
    rw [e, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    change _ ⁻¹ᵁ ((baseChangeDiagram D V.hom).map fji ⁻¹ᵁ U) = ⊤
    rw [hj₁]
    simp
  have : q ∈ pullback.fst V.hom (D.map (g ≫ j₁.hom)) ⁻¹ᵁ O := by rw [h₁]; trivial
  rw [← hq]
  exact this

end Injectivity

section Model

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u}) {R : Scheme.{u}}
  (π : D ⟶ (Functor.const J).obj R) (c : Cone D) [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]

/-- (Implementation) A model at the stage `Dᵢ` of an étale `lim Dⱼ`-scheme `V` together with
morphisms `φ : V ⟶ U` and `ω : V ⟶ W` over `R`: an affine étale `Dᵢ`-scheme `Y` with
`V = Y ×_{Dᵢ} lim Dⱼ`, through which `φ` and `ω` factor over `R`. -/
def HasStageModel (V : c.pt.Etale) {U W : Scheme.{u}} (qU : U ⟶ R) (qW : W ⟶ R)
    (φ : V.left ⟶ U) (ω : V.left ⟶ W) (i : J) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (h : V.left ⟶ Y) (ψ : Y ⟶ U) (ω' : Y ⟶ W),
    Etale p ∧ IsAffine Y ∧ IsPullback h V.hom p (c.π.app i) ∧ ψ ≫ qU = p ≫ π.app i ∧
      ω' ≫ qW = p ≫ π.app i ∧ h ≫ ψ = φ ∧ h ≫ ω' = ω

variable {D π c}

omit [IsCofiltered J] in
lemma HasStageModel.mono {V : c.pt.Etale} {U W : Scheme.{u}} {qU : U ⟶ R} {qW : W ⟶ R}
    {φ : V.left ⟶ U} {ω : V.left ⟶ W} {i k : J} (H : HasStageModel D π c V qU qW φ ω i)
    (f : k ⟶ i) : HasStageModel D π c V qU qW φ ω k := by
  obtain ⟨Y, p, h, ψ, ω', hp, hY, H, hψ, hω', hhψ, hhω⟩ := H
  have : IsAffineHom (pullback.fst p (D.map f)) := MorphismProperty.pullback_fst _ _ inferInstance
  have hnat : D.map f ≫ π.app i = π.app k := by simp
  refine ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f H, pullback.fst _ _ ≫ ψ,
    pullback.fst _ _ ≫ ω', inferInstance, isAffine_of_isAffineHom (pullback.fst p (D.map f)),
    isPullback_isPullbackLift f H, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hψ, pullback.condition_assoc, hnat]
  · rw [Category.assoc, hω', pullback.condition_assoc, hnat]
  · rw [isPullbackLift_fst_assoc, hhψ]
  · rw [isPullbackLift_fst_assoc, hhω]

variable [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

/-- (Implementation) An affine étale `lim Dⱼ`-scheme over an affine open of `lim Dⱼ`, together
with morphisms over `R` to schemes locally of finite presentation over `R`, has a model at some
stage. -/
lemma exists_hasStageModel (hc : IsLimit c) (P : c.pt ⟶ R) (hP : ∀ j, P = c.π.app j ≫ π.app j)
    (V : c.pt.Etale) [IsAffine V.left] {N : c.pt.Opens} (hN : IsAffineOpen N)
    (hVN : Set.range V.hom ⊆ (N : Set c.pt)) {U W : Scheme.{u}} (qU : U ⟶ R) (qW : W ⟶ R)
    [LocallyOfFinitePresentation qU] [LocallyOfFinitePresentation qW]
    (φ : V.left ⟶ U) (hφ : φ ≫ qU = V.hom ≫ P) (ω : V.left ⟶ W) (hω : ω ≫ qW = V.hom ≫ P) :
    ∃ i, HasStageModel D π c V qU qW φ ω i := by
  have : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  obtain ⟨i, Y, hY, p, hp, h, H⟩ :=
    Scheme.exists_isPullback_of_etale_of_isAffineOpen D c hc V.hom hN hVN
  obtain ⟨k₁, f₁, ψ, hψ, hhψ⟩ := Scheme.exists_isPullbackLift_comp_eq hc π H qU φ
    (by rw [hφ, hP i])
  have H₁ := isPullback_isPullbackLift f₁ H
  obtain ⟨k₂, f₂, ω', hω', hhω'⟩ := Scheme.exists_isPullbackLift_comp_eq hc π H₁ qW ω
    (by rw [hω, hP k₁])
  have hnat : D.map f₂ ≫ π.app k₁ = π.app k₂ := by simp
  have : IsAffineHom (pullback.fst (pullback.snd p (D.map f₁)) (D.map f₂)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffineHom (pullback.fst p (D.map f₁)) := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine (pullback p (D.map f₁)) := isAffine_of_isAffineHom (pullback.fst p (D.map f₁))
  refine ⟨k₂, pullback (pullback.snd p (D.map f₁)) (D.map f₂), pullback.snd _ _,
    isPullbackLift D c f₂ H₁, pullback.fst _ _ ≫ ψ, ω', inferInstance,
    isAffine_of_isAffineHom (pullback.fst (pullback.snd p (D.map f₁)) (D.map f₂)),
    isPullback_isPullbackLift f₂ H₁, ?_, hω', ?_, hhω'⟩
  · rw [Category.assoc, hψ, pullback.condition_assoc, hnat]
  · rw [isPullbackLift_fst_assoc, hhψ]

end Model

section Local

variable {R T : Scheme.{u}} (P : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  (W : R.Etale)

/-- (Implementation) Every section of `P^* G` over `W ×_R T` is, near every point, the pullback
of a section of `G` along a morphism from an affine étale `T`-scheme lying over an affine open
of `T`. -/
lemma exists_local_pullSection
    (t : ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ P).obj W)))
    (x : ((MorphismProperty.Over.pullback @Etale ⊤ P).obj W).left) :
    ∃ (V : T.Etale) (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ P).obj W) (U : R.Etale)
      (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ P) (g : G.obj.obj (op U)),
      x ∈ Set.range a.left ∧
      ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op t = pullSection P G φ hφ g ∧
      IsAffine V.left ∧ ∃ N : T.Opens, IsAffineOpen N ∧ Set.range V.hom ⊆ (N : Set T) := by
  obtain ⟨V', a', U, φ, hφ, g, ⟨y, hy⟩, ht⟩ := exists_pullSection_eq P G t x
  obtain ⟨_, ⟨N, hN, rfl⟩, hyN, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (V'.hom y)) isOpen_univ
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV₀, hV₀N⟩ := V'.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ V'.hom ⁻¹ᵁ N from hyN) (V'.hom ⁻¹ᵁ N).isOpen
  refine ⟨Scheme.Etale.ofOpens V' V₀, Scheme.Etale.ofOpensι V' V₀ ≫ a', U,
    Scheme.Opens.ι V₀ ≫ φ,
    by rw [Category.assoc, hφ]; rfl, g, ⟨⟨y, hyV₀⟩, ?_⟩, ?_, hV₀, N, hN, ?_⟩
  · rw [← hy]
    rfl
  · rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ht, map_pullSection]
    rfl
  · rintro _ ⟨z, rfl⟩
    exact hV₀N z.2

end Local

section Piece

variable {J : Type u} [SmallCategory J] {D : J ⥤ Scheme.{u}} {R : Scheme.{u}}
  (π : D ⟶ (Functor.const J).obj R) {c : Cone D} (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  {W : R.Etale}

/-- (Implementation) Restricting the section `ψ^* g` of a model `Y` at the stage `Dₖ` of a
piece `V` of `W ×_R lim Dⱼ`, on which `t = φ^* g`, along `m : Z ⟶ Y` over `lim Dⱼ ⟶ Dₖ`, gives
the restriction of `t` along the induced morphism `Z ⟶ V ⟶ W ×_R lim Dⱼ`. -/
lemma restrictAlong_pullSection_eq_map {k : J} {V : c.pt.Etale}
    (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ P).obj W) {U : R.Etale}
    {φ : V.left ⟶ U.left} (hφ : φ ≫ U.hom = V.hom ≫ P) {g : G.obj.obj (op U)}
    (t : ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ P).obj W)))
    (ht : ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op t = pullSection P G φ hφ g)
    {Y : (D.obj k).Etale} {e : V.left ⟶ Y.left} (H : IsPullback e V.hom Y.hom (c.π.app k))
    {ψ : Y.left ⟶ U.left} (hψ : ψ ≫ U.hom = Y.hom ≫ π.app k) (hhψ : e ≫ ψ = φ)
    {Z : c.pt.Etale} (m : Z.left ⟶ Y.left) (hm : m ≫ Y.hom = Z.hom ≫ c.π.app k) :
    restrictAlong (π.app k) G (c.π.app k) P (hP k) m hm (pullSection (π.app k) G ψ hψ g) =
      ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.map
        ((MorphismProperty.Over.homMk (H.lift m Z.hom hm) (by simp) : Z ⟶ V) ≫ a).op t := by
  rw [restrictAlong_pullSection, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ht,
    map_pullSection]
  apply pullSection_congr
  simp [← hhψ]

end Piece

variable {R : Scheme.{u}} {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
  (π : D ⟶ (Functor.const J).obj R) (c : Cone D) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

/-- **Continuity of sections at an inverse limit, surjectivity**: every section of the pullback
of `G` over `W ×_R lim Dⱼ` comes from a section over some `W ×_R Dⱼ`. This is the first half of
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`. -/
theorem unitComparison_app_surjective_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (t : ((P)_*[AddCommGrpCat.{u + 1}].obj ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)) :
    ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t := by
  classical
  have : QuasiCompact W.hom := @quasiCompact_of_compactSpace W.left R W.hom ‹_› ‹_›
  have : QuasiSeparated W.hom := @QuasiSeparated.of_quasiSeparatedSpace W.left R W.hom ‹_›
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let WX := (MorphismProperty.Over.pullback @Etale ⊤ P).obj W
  have : CompactSpace WX.left := inferInstanceAs (CompactSpace ↥(pullback W.hom P))
  let t' : ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op WX) := t
  -- local representations of `t` on finitely many affine pieces
  choose V a U φ hφ g hx ht hV N hN hVN using fun x ↦ exists_local_pullSection P G W t' x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (a x).left)
    (fun x ↦ (a x).left.isOpenMap.isOpen_range) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  have hcov : ∀ z : WX.left, ∃ x : s, z ∈ Set.range (a x).left := fun z ↦ by
    have := hs (Set.mem_univ z)
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxs, hz⟩ := this
    exact ⟨⟨x, hxs⟩, hz⟩
  -- models of the pieces at a common stage `k`
  have hmodel (x : WX.left) : ∃ i, HasStageModel D π c (V x) (U x).hom W.hom (φ x)
      ((a x).left ≫ pullback.fst W.hom P) i := by
    have := hV x
    exact exists_hasStageModel hc P hP (V x) (hN x) (hVN x) (U x).hom W.hom (φ x) (hφ x) _
      (by rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ P) (MorphismProperty.Over.w (a x)))
  choose i hi using hmodel
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (s.image i)
  choose Y p e ψ ω hp hY H hψ hω hhψ hhω using fun x : s ↦
    (hi x).mono (hk (Finset.mem_image_of_mem i x.2)).some
  -- the pieces at the stage `k`
  let F := (π.app k)^*[AddCommGrpCat.{u + 1}].obj G
  let Wk := (MorphismProperty.Over.pullback @Etale ⊤ (π.app k)).obj W
  have : QuasiSeparatedSpace Wk.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd W.hom (π.app k))
  let Ya (x : s) : (D.obj k).Etale := have := hp x; Scheme.Etale.mk (p x)
  let ba (x : s) : Ya x ⟶ Wk :=
    MorphismProperty.Over.homMk (pullback.lift (ω x) (p x) (hω x)) (pullback.lift_snd _ _ _)
  let σ (x : s) : F.obj.obj (op (Ya x)) := pullSection (π.app k) G (ψ x) (hψ x) (g x)
  -- the pieces cover `W ×_R Dₖ'` at a later stage `k₁`
  let E := baseChangeOverDiagram D π W.hom
  let Ec := baseChangeOverCone D π c P hP W.hom
  have hEc := isLimitBaseChangeOverCone D π c P hP W.hom hc
  let Uk : (E.obj k).Opens := ⟨⋃ x : s, Set.range (ba x).left,
    isOpen_iUnion fun x ↦ (ba x).left.isOpenMap.isOpen_range⟩
  have hba (x : s) : e x ≫ (ba x).left = (a x).left ≫ Ec.π.app k := by
    apply pullback.hom_ext
    · simp [ba, Ec, hhω]
    · simpa [ba, Ec, (H x).w] using
        congrArg (· ≫ c.π.app k) (MorphismProperty.Over.w (a x)).symm
  have hUk : Ec.π.app k ⁻¹ᵁ Uk = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top,
      Set.mem_univ, iff_true]
    obtain ⟨x, v, rfl⟩ := hcov z
    have := congr($(hba x) v)
    simp only [Scheme.Hom.comp_apply] at this
    exact Set.mem_iUnion.2 ⟨x, e x v, this⟩
  obtain ⟨k₁, f₁, hk₁⟩ := exists_map_eq_top E Ec hEc Uk hUk
  -- the differences on the overlaps vanish at a later stage
  let δ (x y : s) : F.obj.obj (op (overlap (ba x) (ba y))) :=
    F.obj.map (overlapFst (ba x) (ba y)).op (σ x) - F.obj.map (overlapSnd (ba x) (ba y)).op (σ y)
  have hδ (x y : s) : ∃ (k' : J) (f : k' ⟶ k), ∀ (k'' : J) (g' : k'' ⟶ k')
      (V'' : (D.obj k'').Etale) (m : V''.left ⟶ (overlap (ba x) (ba y)).left)
      (hm : m ≫ (overlap (ba x) (ba y)).hom = V''.hom ≫ D.map (g' ≫ f)),
      restrictAlong (π.app k) G (D.map (g' ≫ f)) (π.app k'') (by simp) m hm (δ x y) = 0 := by
    have : IsAffine (Ya x).left := hY x
    have : IsAffine (Ya y).left := hY y
    have : QuasiCompact (ba y).left := quasiCompact_of_compactSpace _
    have : CompactSpace (overlap (ba x) (ba y)).left :=
      inferInstanceAs (CompactSpace ↥(pullback (ba x).left (ba y).left))
    refine exists_restrictAlong_eq_zero_of_isLimit π P hP G hc _ (δ x y) ?_
    rw [map_sub, restrictAlong_map, restrictAlong_map,
      restrictAlong_pullSection_eq_map π P hP G (a x) (hφ x) t' (ht x) (Y := Ya x) (H x) (hψ x)
        (hhψ x),
      restrictAlong_pullSection_eq_map π P hP G (a y) (hφ y) t' (ht y) (Y := Ya y) (H y) (hψ y)
        (hhψ y), sub_eq_zero]
    congr 4
    have hωxy : pullback.fst (ba x).left (ba y).left ≫ ω x =
        pullback.snd (ba x).left (ba y).left ≫ ω y := by
      have := congrArg (· ≫ pullback.fst W.hom (π.app k))
        (pullback.condition (f := (ba x).left) (g := (ba y).left))
      simpa [ba] using this
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
      rw [← hhω x, ← hhω y]
      simp only [MorphismProperty.Over.homMk_hom, Over.homMk_left, IsPullback.lift_fst_assoc,
        overlapFst_left, overlapSnd_left, Category.assoc, hωxy]
    · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
      have wx : (a x).left ≫ pullback.snd W.hom P = (V x).hom := MorphismProperty.Over.w (a x)
      have wy : (a y).left ≫ pullback.snd W.hom P = (V y).hom := MorphismProperty.Over.w (a y)
      rw [wx, wy]
      simp only [MorphismProperty.Over.homMk_hom, Over.homMk_left, IsPullback.lift_snd]
  -- a common later stage `ks`
  choose kxy fxy hxy using hδ
  obtain ⟨k₂, f₂, g₂, hg₂⟩ := IsCofiltered.wideCospan (fun xy : s × s ↦ fxy xy.1 xy.2)
  obtain ⟨ks, a₁, a₂, ha⟩ := IsCofiltered.cospan f₁ f₂
  let fs : ks ⟶ k := a₁ ≫ f₁
  have hfs (x y : s) : (a₂ ≫ g₂ (x, y)) ≫ fxy x y = fs := by
    rw [Category.assoc, hg₂, ← ha]
  -- the pieces at the stage `ks`
  let Wks := (MorphismProperty.Over.pullback @Etale ⊤ (π.app ks)).obj W
  let Fs := (π.app ks)^*[AddCommGrpCat.{u + 1}].obj G
  let Za (x : s) : (D.obj ks).Etale :=
    Scheme.Etale.mk (pullback.snd (ba x).left (E.map fs) ≫ pullback.snd W.hom (π.app ks))
  let ea (x : s) : Za x ⟶ Wks :=
    MorphismProperty.Over.homMk (pullback.snd (ba x).left (E.map fs)) rfl
  have hμ (x : s) : pullback.fst (ba x).left (E.map fs) ≫ (Ya x).hom =
      (Za x).hom ≫ D.map fs := by
    rw [← MorphismProperty.Over.w (ba x), pullback.condition_assoc]
    simp [E, Za, Wk]
  let τ (x : s) : Fs.obj.obj (op (Za x)) := restrictAlong (π.app k) G (D.map fs) (π.app ks)
    (by simp) (pullback.fst (ba x).left (E.map fs)) (hμ x) (σ x)
  have hcovs (w : Wks.left) : ∃ x : s, w ∈ Set.range (ea x).left := by
    have h₁ : E.map fs ⁻¹ᵁ Uk = ⊤ := by
      rw [show E.map fs = E.map a₁ ≫ E.map f₁ from E.map_comp a₁ f₁, Scheme.Hom.comp_preimage,
        hk₁]
      simp
    have h₂ : w ∈ E.map fs ⁻¹ᵁ Uk := by rw [h₁]; trivial
    obtain ⟨x, y, hy⟩ := Set.mem_iUnion.1 h₂
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y w hy
    exact ⟨x, z, hz⟩
  -- the restricted sections agree on the overlaps
  have hcompat (x y : s) : Fs.obj.map (overlapFst (ea x) (ea y)).op (τ x) =
      Fs.obj.map (overlapSnd (ea x) (ea y)).op (τ y) := by
    let m : (overlap (ea x) (ea y)).left ⟶ (overlap (ba x) (ba y)).left :=
      pullback.map (ea x).left (ea y).left (ba x).left (ba y).left
        (pullback.fst (ba x).left (E.map fs)) (pullback.fst (ba y).left (E.map fs)) (E.map fs)
        pullback.condition.symm pullback.condition.symm
    have hm : m ≫ (overlap (ba x) (ba y)).hom =
        (overlap (ea x) (ea y)).hom ≫ D.map ((a₂ ≫ g₂ (x, y)) ≫ fxy x y) := by
      rw [hfs]
      simp only [m, overlap, MorphismProperty.Over.mk_hom, pullback.lift_fst_assoc,
        Category.assoc, hμ x]
    have h := hxy x y ks (a₂ ≫ g₂ (x, y)) (overlap (ea x) (ea y)) m hm
    rw [restrictAlong_congr' (π.app k) G (π.app ks) (f₂ := D.map fs) (by rw [hfs]) _ (by simp)
      rfl _ (by rw [← hfs]; exact hm)] at h
    rw [map_sub, sub_eq_zero, restrictAlong_map, restrictAlong_map] at h
    simp only [τ]
    rw [map_restrictAlong, map_restrictAlong,
      restrictAlong_congr' (π.app k) G (π.app ks) rfl _ _
        (show (overlapFst (ea x) (ea y)).left ≫ pullback.fst (ba x).left (E.map fs) =
          m ≫ (overlapFst (ba x) (ba y)).left by simp [m]) _ _,
      restrictAlong_congr' (π.app k) G (π.app ks) rfl _ _
        (show (overlapSnd (ea x) (ea y)).left ≫ pullback.fst (ba y).left (E.map fs) =
          m ≫ (overlapSnd (ba x) (ba y)).left by simp [m]) _ _]
    exact h
  -- glue and compare with `t`
  obtain ⟨sg, hsg⟩ := exists_map_eq_of_compatible Fs ea hcovs τ hcompat
  refine ⟨ks, sg, ?_⟩
  rw [unitComparison_hom_app_eq]
  refine eq_of_forall_exists_map_eq ((P)^*[AddCommGrpCat.{u + 1}].obj G) _ t' fun z ↦ ?_
  obtain ⟨x, v, rfl⟩ := hcov z
  refine ⟨V x, a x, ⟨v, rfl⟩, ?_⟩
  rw [ht x]
  refine (map_restrictAlong (π.app ks) G (c.π.app ks) P (hP ks) (V := Wks) (a x) _ _ sg).trans ?_
  have hν : e x ≫ (ba x).left =
      ((a x).left ≫ Ec.π.app ks) ≫ E.map fs := by
    rw [Category.assoc, Ec.w fs, hba x]
  let ν : (V x).left ⟶ (Za x).left := pullback.lift (e x) ((a x).left ≫ Ec.π.app ks) hν
  have e₁ : (a x).left ≫ Ec.π.app ks = ν ≫ (ea x).left := (pullback.lift_snd _ _ _).symm
  have hνZ : ν ≫ (Za x).hom = (V x).hom ≫ c.π.app ks := by
    simpa [ν, Za, Ec] using congrArg (· ≫ c.π.app ks) (MorphismProperty.Over.w (a x))
  change (restrictAlong (π.app ks) G (c.π.app ks) P (hP ks) (V := Wks) (V' := V x)
    ((a x).left ≫ Ec.π.app ks) _) sg = _
  rw [restrictAlong_congr (h := e₁), ← restrictAlong_map _ _ _ _ _ (ea x) ν hνZ, hsg x,
    restrictAlong_restrictAlong, restrictAlong_congr' (π.app k) G P (c.w fs) _ (hP k)
      (show ν ≫ pullback.fst (ba x).left (E.map fs) = e x from pullback.lift_fst _ _ _) _
      (H x).w, restrictAlong_pullSection]
  exact pullSection_congr _ _ _ (hhψ x) _

/-- **Continuity of sections at an inverse limit, injectivity**: a section of the pullback of
`G` over `W ×_R Dⱼ` which vanishes on `W ×_R lim Dⱼ` already vanishes on some `W ×_R Dⱼ'`,
`j' ⟶ j`. This is the second half of
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`. -/
theorem exists_unitComparison_app_eq_zero_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (j : J)
    (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W))
    (hs : (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0) :
    ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
      (by simp) G).hom.app (op W) s = 0 := by
  let V := (MorphismProperty.Over.pullback @Etale ⊤ (π.app j)).obj W
  have : QuasiCompact W.hom := @quasiCompact_of_compactSpace W.left R W.hom ‹_› ‹_›
  have : CompactSpace V.left := inferInstanceAs (CompactSpace ↥(pullback W.hom (π.app j)))
  rw [unitComparison_hom_app_eq] at hs
  let ι : pullback V.hom (c.π.app j) ⟶ pullback W.hom P :=
    pullback.lift (pullback.fst V.hom (c.π.app j) ≫ pullback.fst W.hom (π.app j))
      (pullback.snd V.hom (c.π.app j)) (by
        rw [Category.assoc, pullback.condition, hP j, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ π.app j) (pullback.condition (f := V.hom) (g := c.π.app j)))
  let b : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j)).obj V ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ P).obj W :=
    MorphismProperty.Over.homMk ι (pullback.lift_snd _ _ _)
  have hb : ι ≫ pullback.map W.hom P W.hom (π.app j) (𝟙 _) (c.π.app j) (𝟙 _) (by simp)
      (by simp [hP j]) = pullback.fst V.hom (c.π.app j) := by
    apply pullback.hom_ext
    · simp [ι]
    · simp only [Category.assoc, pullback.lift_snd, ι, pullback.lift_snd_assoc]
      exact (pullback.condition (f := V.hom) (g := c.π.app j)).symm
  obtain ⟨j', f, H⟩ := exists_restrictAlong_eq_zero_of_isLimit π P hP G hc V s (by
    have key := map_restrictAlong (π.app j) G (c.π.app j) P (hP j) (V := V) b
      (pullback.map W.hom P W.hom (π.app j) (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp [hP j]))
      (pullback.lift_snd _ _ _) s
    rw [restrictAlong_congr' (π.app j) G P rfl (hP j) (hP j) hb.symm _
      (by rw [hb]; exact pullback.condition)]
    refine key.symm.trans ?_
    exact (congrArg (fun x ↦ ((P)^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op x) hs).trans
      (map_zero _))
  refine ⟨j', f, ?_⟩
  rw [unitComparison_hom_app_eq]
  have := H j' (𝟙 _) ((MorphismProperty.Over.pullback @Etale ⊤ (π.app j')).obj W)
    (pullback.map W.hom (π.app j') W.hom (π.app j) (𝟙 _) (D.map f) (𝟙 _) (by simp) (by simp))
    (by simp [V])
  rw [restrictAlong_congr' (π.app j) G (π.app j') (f₂ := D.map f) (by simp) _ (by simp) rfl] at this
  exact this

/-- **Continuity of sections at an inverse limit.** Let `(Dⱼ)` be a cofiltered system of
quasi-compact quasi-separated schemes over `R` with affine transition maps, with limit `X`, let
`G` be an abelian étale sheaf on `R` and `W` a quasi-compact quasi-separated étale `R`-scheme,
where `R` is quasi-separated. Then the sections of the pullback of `G` over `W ×_R X` are the
filtered colimit of the sections of the pullbacks of `G` over the `W ×_R Dⱼ`, written as the
sections of `πⱼ_* πⱼ^* G` over `W`, with transition maps `AlgebraicGeometry.Etale.unitComparison`.
-/
theorem unitComparison_app_isColimit_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    (∀ t : ((P)_*[AddCommGrpCat.{u + 1}].obj
        ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W),
      ∃ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
        (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = t) ∧
    ∀ (j : J) (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)),
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s = 0 →
        ∃ (j' : J) (f : j' ⟶ j), (unitComparison (D.map f) (π.app j) (π.app j')
          (by simp) G).hom.app (op W) s = 0 :=
  ⟨fun t ↦ unitComparison_app_surjective_of_isLimit D π c P hP hc G W t,
    fun j s hs ↦ exists_unitComparison_app_eq_zero_of_isLimit D π c P hP hc G W j s hs⟩

end Etale

end AlgebraicGeometry
