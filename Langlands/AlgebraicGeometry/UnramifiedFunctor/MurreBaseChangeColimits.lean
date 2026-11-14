import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Base change of Murre's condition (F2)

Condition (F2) asks that `B ↦ F(Spec B)` preserve filtered colimits of `R`-algebras for
the affine opens `Spec R ⟶ S`. For a Zariski sheaf this extends to every morphism
`Spec R ⟶ S` (`good_of_zariskiSheaf`), which gives (F2) for every base change of `F`. -/

universe w u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace BaseChange

section Abstract

/-- In a filtered category, finitely many conditions on morphisms out of `α`, each stable
under postcomposition and each satisfied by some morphism, are satisfied by one morphism. -/
lemma exists_forall_of_finite {J : Type*} [Category J] [IsFilteredOrEmpty J] {κ : Type*}
    [Finite κ] (α : J) (Q : κ → ∀ γ : J, (α ⟶ γ) → Prop)
    (hQ : ∀ k γ (t : α ⟶ γ) γ' (s : γ ⟶ γ'), Q k γ t → Q k γ' (t ≫ s))
    (hex : ∀ k, ∃ (γ : J) (t : α ⟶ γ), Q k γ t) : ∃ (γ : J) (t : α ⟶ γ), ∀ k, Q k γ t := by
  classical
  have := Fintype.ofFinite κ
  suffices H : ∀ s : Finset κ, ∃ (γ : J) (t : α ⟶ γ), ∀ k ∈ s, Q k γ t by
    obtain ⟨γ, t, ht⟩ := H Finset.univ
    exact ⟨γ, t, fun k ↦ ht k (Finset.mem_univ k)⟩
  intro s
  refine Finset.induction_on s ⟨α, 𝟙 α, by simp⟩ ?_
  intro k s _ ih
  obtain ⟨γ₁, t₁, h₁⟩ := ih
  obtain ⟨γ₂, t₂, h₂⟩ := hex k
  refine ⟨IsFiltered.coeq (t₁ ≫ IsFiltered.leftToMax γ₁ γ₂) (t₂ ≫ IsFiltered.rightToMax γ₁ γ₂),
    t₁ ≫ IsFiltered.leftToMax γ₁ γ₂ ≫ IsFiltered.coeqHom _ _, ?_⟩
  intro k' hk'
  rcases Finset.mem_insert.1 hk' with rfl | hk'
  · have e : t₁ ≫ IsFiltered.leftToMax γ₁ γ₂ ≫
        IsFiltered.coeqHom (t₁ ≫ IsFiltered.leftToMax γ₁ γ₂) (t₂ ≫ IsFiltered.rightToMax γ₁ γ₂) =
        t₂ ≫ IsFiltered.rightToMax γ₁ γ₂ ≫
          IsFiltered.coeqHom (t₁ ≫ IsFiltered.leftToMax γ₁ γ₂)
            (t₂ ≫ IsFiltered.rightToMax γ₁ γ₂) := by
      simpa only [Category.assoc] using IsFiltered.coeq_condition
        (t₁ ≫ IsFiltered.leftToMax γ₁ γ₂) (t₂ ≫ IsFiltered.rightToMax γ₁ γ₂)
    rw [e]
    exact hQ _ _ _ _ _ h₂
  · exact hQ _ _ _ _ _ (h₁ k' hk')

/-- A functor to types which is, objectwise, the equalizer of a finite family of functors
preserving a filtered colimit (through the maps `res`, `a`, `b`) preserves that colimit. -/
def isColimit_mapCocone_of_equalizer {C : Type*} [Category C] {J : Type*} [Category J]
    [IsFiltered J] {ι : Type*} [Finite ι] {K : J ⥤ C} (c : Cocone K)
    (P : C ⥤ Type w) (Pi : ι → C ⥤ Type w) (Pij : ι → ι → C ⥤ Type w)
    (res : ∀ i, P ⟶ Pi i) (a : ∀ i j, Pi i ⟶ Pij i j) (b : ∀ i j, Pi j ⟶ Pij i j)
    (hab : ∀ X x i j, (a i j).app X ((res i).app X x) = (b i j).app X ((res j).app X x))
    (sep : ∀ X (x y : P.obj X), (∀ i, (res i).app X x = (res i).app X y) → x = y)
    (glue : ∀ X (s : ∀ i, (Pi i).obj X), (∀ i j, (a i j).app X (s i) = (b i j).app X (s j)) →
      ∃ x, ∀ i, (res i).app X x = s i)
    (hi : ∀ i, IsColimit ((Pi i).mapCocone c))
    (hij : ∀ i j, IsColimit ((Pij i j).mapCocone c)) :
    IsColimit (P.mapCocone c) := by
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨α₀⟩ := IsFiltered.nonempty (C := J)
    obtain ⟨γ, t, ht⟩ := exists_forall_of_finite α₀
      (fun i γ _ ↦ ∃ y : (Pi i).obj (K.obj γ), (Pi i).map (c.ι.app γ) y = (res i).app c.pt x)
      (fun i γ t γ' s ⟨y, hy⟩ ↦ ⟨(Pi i).map (K.map s) y, by
        rw [← Functor.map_comp_apply, c.w, hy]⟩)
      (fun i ↦ by
        obtain ⟨β, y, hy⟩ := Types.jointly_surjective_of_isColimit (hi i) ((res i).app c.pt x)
        refine ⟨IsFiltered.max α₀ β, IsFiltered.leftToMax _ _,
          (Pi i).map (K.map (IsFiltered.rightToMax _ _)) y, ?_⟩
        rw [← Functor.map_comp_apply, c.w]
        exact hy)
    choose y hy using ht
    obtain ⟨δ, s, hs⟩ := exists_forall_of_finite (κ := ι × ι) γ
      (fun p δ s ↦ (Pij p.1 p.2).map (K.map s) ((a p.1 p.2).app _ (y p.1)) =
        (Pij p.1 p.2).map (K.map s) ((b p.1 p.2).app _ (y p.2)))
      (fun p δ s δ' s' h ↦ by
        rw [K.map_comp, Functor.map_comp_apply, Functor.map_comp_apply, h])
      (fun p ↦ (Types.FilteredColimit.isColimit_eq_iff' (hij p.1 p.2) _ _).1 (by
        simp only [Functor.mapCocone_ι_app, Functor.comp_obj]
        rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hy, hy, hab]))
    obtain ⟨z, hz⟩ := glue (K.obj δ) (fun i ↦ (Pi i).map (K.map s) (y i)) (fun i j ↦ by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact hs (i, j))
    refine ⟨δ, z, sep _ _ _ fun i ↦ ?_⟩
    simp only [Functor.mapCocone_ι_app]
    rw [NatTrans.naturality_apply, hz, ← Functor.map_comp_apply, c.w, hy]
  · intro α x y hxy
    obtain ⟨δ, s, hs⟩ := exists_forall_of_finite α
      (fun i δ s ↦ (Pi i).map (K.map s) ((res i).app _ x) =
        (Pi i).map (K.map s) ((res i).app _ y))
      (fun i δ s δ' s' h ↦ by
        rw [K.map_comp, Functor.map_comp_apply, Functor.map_comp_apply, h])
      (fun i ↦ (Types.FilteredColimit.isColimit_eq_iff' (hi i) _ _).1 (by
        simp only [Functor.mapCocone_ι_app, Functor.comp_obj] at hxy ⊢
        rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hxy]))
    refine ⟨δ, s, sep _ _ _ fun i ↦ ?_⟩
    simp only [Functor.comp_map]
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact hs i

/-- Separation and gluing for a family of arrows `ρ i = e i ≫ π i` refining a family for
which `P` satisfies the sheaf condition, the compatibility being tested on objects `W i j`
through which every pair of arrows agreeing in `X` factors. -/
lemma sep_glue_of_isSheafFor {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type w) {X : C} {ι : Type*}
    {U V : ι → C} (π : ∀ i, U i ⟶ X) (hP : Presieve.IsSheafFor P (Presieve.ofArrows U π))
    (e : ∀ i, V i ≅ U i) (ρ : ∀ i, V i ⟶ X) (hρ : ∀ i, ρ i = (e i).hom ≫ π i)
    {W : ι → ι → C} (p : ∀ i j, W i j ⟶ V i) (q : ∀ i j, W i j ⟶ V j)
    (hlift : ∀ i j (Z : C) (gi : Z ⟶ V i) (gj : Z ⟶ V j), gi ≫ ρ i = gj ≫ ρ j →
      ∃ l : Z ⟶ W i j, l ≫ p i j = gi ∧ l ≫ q i j = gj) :
    (∀ x y : P.obj (op X), (∀ i, P.map (ρ i).op x = P.map (ρ i).op y) → x = y) ∧
    (∀ s : ∀ i, P.obj (op (V i)), (∀ i j, P.map (p i j).op (s i) = P.map (q i j).op (s j)) →
      ∃ x, ∀ i, P.map (ρ i).op x = s i) := by
  rw [Presieve.isSheafFor_arrows_iff] at hP
  have key : ∀ i (x : P.obj (op X)), P.map (π i).op x = P.map (e i).inv.op (P.map (ρ i).op x) :=
    fun i x ↦ by
      rw [hρ, ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id_assoc]
  constructor
  · intro x y hxy
    obtain ⟨t, -, ht⟩ := hP (fun i ↦ P.map (π i).op x) (fun i j Z gi gj h ↦ by
      simp only [← Functor.map_comp_apply, ← op_comp, h])
    refine (ht x fun _ ↦ rfl).trans (ht y fun i ↦ ?_).symm
    rw [key, key, hxy]
  · intro s hs
    obtain ⟨t, ht, -⟩ := hP (fun i ↦ P.map (e i).inv.op (s i)) (fun i j Z gi gj h ↦ by
      obtain ⟨l, hl₁, hl₂⟩ := hlift i j Z (gi ≫ (e i).inv) (gj ≫ (e j).inv) (by
        simpa [hρ] using h)
      dsimp only
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← hl₁, ← hl₂,
        op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hs])
    refine ⟨t, fun i ↦ ?_⟩
    rw [hρ, op_comp, Functor.map_comp_apply, ht, ← Functor.map_comp_apply, ← op_comp,
      Iso.hom_inv_id, op_id, Functor.map_id_apply]

end Abstract

section Good

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v)

/-- For `h : Spec R ⟶ S`, the functor `B ↦ (Spec B ⟶ Spec R ⟶ S)` on rings under `R`. -/
@[simps]
def specOver {R : CommRingCat.{u}} (h : Spec R ⟶ S) : Under R ⥤ (Over S)ᵒᵖ where
  obj B := op (Over.mk (Spec.map B.hom ≫ h))
  map {B B'} u := (Over.homMk (Spec.map u.right) (by
    dsimp
    rw [← Category.assoc, ← Spec.map_comp, Under.w u])).op
  map_id B := by
    apply Quiver.Hom.unop_inj
    ext1
    simp
  map_comp u u' := by
    apply Quiver.Hom.unop_inj
    ext1
    simp

/-- `h : Spec R ⟶ S` is good for `F` if `B ↦ F(Spec B)` preserves filtered colimits of rings
under `R`. -/
def Good {R : CommRingCat.{u}} (h : Spec R ⟶ S) : Prop :=
  PreservesFilteredColimitsOfSize.{u, u} (specOver h ⋙ F)

/-- The components of `specOverCompIso`. -/
def specOverCompIsoApp {R R' : CommRingCat.{u}} (φ : R ⟶ R') (h : Spec R ⟶ S) (B : Under R') :
    Over.mk (Spec.map (φ ≫ B.hom) ≫ h) ≅ Over.mk (Spec.map B.hom ≫ Spec.map φ ≫ h) :=
  Over.isoMk (Iso.refl _) (by
    show 𝟙 _ ≫ Spec.map B.hom ≫ Spec.map φ ≫ h = Spec.map (φ ≫ B.hom) ≫ h
    rw [Category.id_comp, Spec.map_comp, Category.assoc])

/-- Composing `h` with `Spec φ` corresponds to restricting along `Under.map φ`. -/
def specOverCompIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') (h : Spec R ⟶ S) :
    specOver (Spec.map φ ≫ h) ≅ Under.map φ ⋙ specOver h :=
  NatIso.ofComponents (fun B ↦ (specOverCompIsoApp φ h B).op) (by
    intro B B' u
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    show 𝟙 _ ≫ Spec.map u.right = Spec.map u.right ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id])

instance preservesColimitsOfShape_underMap {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (Under.map φ) := by
  have : IsConnected J := IsFiltered.isConnected J
  constructor
  intro K
  have : PreservesColimit K (Under.map φ ⋙ Under.forget R) :=
    inferInstanceAs (PreservesColimit K (Under.forget R'))
  exact preservesColimit_of_reflects_of_preserves (Under.map φ) (Under.forget R)

variable {F}

lemma good_comp {R R' : CommRingCat.{u}} (φ : R ⟶ R') {h : Spec R ⟶ S} (hh : Good F h) :
    Good F (Spec.map φ ≫ h) := by
  constructor
  intro J _ _
  have := hh.preserves_filtered_colimits J
  have : PreservesColimitsOfShape J ((Under.map φ ⋙ specOver h) ⋙ F) :=
    inferInstanceAs (PreservesColimitsOfShape J (Under.map φ ⋙ (specOver h ⋙ F)))
  exact preservesColimitsOfShape_of_natIso (Functor.isoWhiskerRight (specOverCompIso φ h).symm F)

/-- On algebras, `specOver` is `algebraFunctor`. -/
def algebraFunctorIso {R : Type u} [CommRing R] (h : Spec (CommRingCat.of R) ⟶ S) :
    (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ specOver h ≅ algebraFunctor h :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B u
    apply Quiver.Hom.unop_inj
    ext1
    simp
    rfl)

lemma good_of_isOpenImmersion (h2 : FilteredColimits F) {R : CommRingCat.{u}} (h : Spec R ⟶ S)
    [IsOpenImmersion h] : Good F h := by
  constructor
  intro J _ _
  have := (h2 R h inferInstance).preserves_filtered_colimits J
  let E := commAlgCatEquivUnder (CommRingCat.of R)
  have : PreservesColimitsOfShape J (E.inverse ⋙ (algebraFunctor h ⋙ F)) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight (algebraFunctorIso h).symm F) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Functor.associator _ _ _).symm F ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight E.counitIso _) F ≪≫
      Functor.isoWhiskerRight (Functor.leftUnitor _) F)

end Good

section Pushouts

variable {R A Ri Rj : CommRingCat.{u}} (a : R ⟶ A) (φi : R ⟶ Ri) (φj : R ⟶ Rj)

/-- The map `A ⊗_R R_i → A ⊗_R (R_i ⊗_R R_j)`. -/
def descL : pushout a φi ⟶ pushout a (φi ≫ pushout.inl φi φj) :=
  pushout.desc (pushout.inl _ _) (pushout.inl φi φj ≫ pushout.inr _ _)
    (by rw [pushout.condition (f := a), Category.assoc])

/-- The map `A ⊗_R R_j → A ⊗_R (R_i ⊗_R R_j)`. -/
def descR : pushout a φj ⟶ pushout a (φi ≫ pushout.inl φi φj) :=
  pushout.desc (pushout.inl _ _) (pushout.inr φi φj ≫ pushout.inr _ _)
    (by rw [pushout.condition (f := a), Category.assoc, pushout.condition_assoc (f := φi)])

@[reassoc]
lemma inl_descL : pushout.inl a φi ≫ descL a φi φj = pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inl_descR : pushout.inl a φj ≫ descR a φi φj = pushout.inl _ _ :=
  pushout.inl_desc _ _ _

lemma descL_w : (φi ≫ pushout.inr a φi) ≫ descL a φi φj =
    (φi ≫ pushout.inl φi φj) ≫ pushout.inr a _ := by
  rw [Category.assoc, descL, pushout.inr_desc, Category.assoc]

lemma descR_w : (φj ≫ pushout.inr a φj) ≫ descR a φi φj =
    (φi ≫ pushout.inl φi φj) ≫ pushout.inr a _ := by
  rw [Category.assoc, descR, pushout.inr_desc, Category.assoc, pushout.condition_assoc (f := φi)]

lemma specMap_inr_comp (φk : R ⟶ Rj) :
    Spec.map (pushout.inr a φk) ≫ Spec.map φk = Spec.map (pushout.inl a φk) ≫ Spec.map a := by
  rw [← Spec.map_comp, ← Spec.map_comp, pushout.condition (f := a)]

/-- Two points of `Spec (A ⊗_R R_i)` and `Spec (A ⊗_R R_j)` over the same point of `Spec A`
come from a point of `Spec (A ⊗_R R_i ⊗_R R_j)`. -/
lemma exists_lift_pushout {Z : Scheme.{u}} (gi : Z ⟶ Spec (pushout a φi))
    (gj : Z ⟶ Spec (pushout a φj))
    (hg : gi ≫ Spec.map (pushout.inl a φi) = gj ≫ Spec.map (pushout.inl a φj)) :
    ∃ l : Z ⟶ Spec (pushout a (φi ≫ pushout.inl φi φj)),
      l ≫ Spec.map (descL a φi φj) = gi ∧ l ≫ Spec.map (descR a φi φj) = gj := by
  have hQ := isPullback_SpecMap_pushout φi φj
  have hm : (gi ≫ Spec.map (pushout.inr a φi)) ≫ Spec.map φi =
      (gj ≫ Spec.map (pushout.inr a φj)) ≫ Spec.map φj := by
    rw [Category.assoc, Category.assoc, specMap_inr_comp, specMap_inr_comp, reassoc_of% hg]
  have h2 := isPullback_SpecMap_pushout a (φi ≫ pushout.inl φi φj)
  have hl : (gi ≫ Spec.map (pushout.inl a φi)) ≫ Spec.map a =
      hQ.lift _ _ hm ≫ Spec.map (φi ≫ pushout.inl φi φj) := by
    rw [Spec.map_comp φi (pushout.inl φi φj), IsPullback.lift_fst_assoc, Category.assoc,
      Category.assoc, specMap_inr_comp]
  have hPi := isPullback_SpecMap_pushout a φi
  have hPj := isPullback_SpecMap_pushout a φj
  refine ⟨h2.lift _ _ hl, hPi.hom_ext ?_ ?_, hPj.hom_ext ?_ ?_⟩
  · rw [Category.assoc, ← Spec.map_comp, inl_descL, IsPullback.lift_fst]
  · rw [Category.assoc, ← Spec.map_comp, descL, pushout.inr_desc,
      Spec.map_comp (pushout.inl φi φj) (pushout.inr a _), IsPullback.lift_snd_assoc,
      IsPullback.lift_fst]
  · rw [Category.assoc, ← Spec.map_comp, inl_descR, IsPullback.lift_fst, hg]
  · rw [Category.assoc, ← Spec.map_comp, descR, pushout.inr_desc,
      Spec.map_comp (pushout.inr φi φj) (pushout.inr a _), IsPullback.lift_snd_assoc,
      IsPullback.lift_snd]

end Pushouts

section Cover

variable {R A : CommRingCat.{u}}

/-- `B ↦ B ⊗_R A`, as a ring under `R` through `R → A → B ⊗_R A`. -/
abbrev pieceT (α : R ⟶ A) : Under R ⥤ Under R := Under.pushout α ⋙ Under.map α

/-- The maps `B → B ⊗_R A`. -/
def resNat (α : R ⟶ A) : 𝟭 (Under R) ⟶ pieceT α where
  app B := Under.homMk (pushout.inl B.hom α) (pushout.condition (f := B.hom) (g := α))
  naturality B B' u := by
    ext1
    exact (pushout.inl_desc _ _ _).symm

variable {Ri Rj : CommRingCat.{u}}

/-- The maps `B ⊗_R R_i → B ⊗_R R_i ⊗_R R_j`. -/
def natL (φi : R ⟶ Ri) (φj : R ⟶ Rj) : pieceT φi ⟶ pieceT (φi ≫ pushout.inl φi φj) where
  app B := Under.homMk (descL B.hom φi φj) (descL_w B.hom φi φj)
  naturality B B' u := by
    ext1
    show pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _) _ ≫ descL B'.hom φi φj =
      descL B.hom φi φj ≫ pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _) _
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, Category.assoc, inl_descL, inl_descL_assoc, pushout.inl_desc]
    · rw [pushout.inr_desc_assoc, descL, descL, pushout.inr_desc, pushout.inr_desc_assoc,
        Category.assoc, pushout.inr_desc]

/-- The maps `B ⊗_R R_j → B ⊗_R R_i ⊗_R R_j`. -/
def natR (φi : R ⟶ Ri) (φj : R ⟶ Rj) : pieceT φj ⟶ pieceT (φi ≫ pushout.inl φi φj) where
  app B := Under.homMk (descR B.hom φi φj) (descR_w B.hom φi φj)
  naturality B B' u := by
    ext1
    show pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _) _ ≫ descR B'.hom φi φj =
      descR B.hom φi φj ≫ pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _) _
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, Category.assoc, inl_descR, inl_descR_assoc, pushout.inl_desc]
    · rw [pushout.inr_desc_assoc, descR, descR, pushout.inr_desc, pushout.inr_desc_assoc,
        Category.assoc, pushout.inr_desc]

lemma resNat_natL (φi : R ⟶ Ri) (φj : R ⟶ Rj) :
    resNat φi ≫ natL φi φj = resNat φj ≫ natR φi φj := by
  apply NatTrans.ext
  funext B
  apply Under.UnderMorphism.ext
  show pushout.inl B.hom φi ≫ descL B.hom φi φj = pushout.inl B.hom φj ≫ descR B.hom φi φj
  rw [inl_descL, inl_descR]

end Cover

section Local

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {R : CommRingCat.{u}}

lemma preserves_piece {A : CommRingCat.{u}} (α : R ⟶ A) {h : Spec R ⟶ S}
    (hα : Good F (Spec.map α ≫ h)) (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (pieceT α ⋙ specOver h ⋙ F) := by
  have := hα.preserves_filtered_colimits J
  have : PreservesColimitsOfShape J (Under.map α ⋙ specOver h ⋙ F) :=
    preservesColimitsOfShape_of_natIso
      (Functor.isoWhiskerRight (specOverCompIso α h) F ≪≫ Functor.associator _ _ _)
  have := (Under.mapPushoutAdj α).leftAdjoint_preservesColimits.{u, u}
  exact inferInstanceAs
    (PreservesColimitsOfShape J (Under.pushout α ⋙ (Under.map α ⋙ specOver h ⋙ F)))

/-- Separation and gluing for `B ↦ F(Spec B)` along the covering of `Spec B` by the
`Spec (B ⊗_R R_i)`, for open immersions `Spec R_i ⟶ Spec R` covering `Spec R`. -/
lemma sep_glue (hZ : ZariskiSheaf F) (h : Spec R ⟶ S) {ι : Type u}
    {Ri : ι → CommRingCat.{u}} (φ : ∀ i, R ⟶ Ri i) [∀ i, IsOpenImmersion (Spec.map (φ i))]
    (hcov : ∀ x, ∃ i y, Spec.map (φ i) y = x) (B : Under R) :
    (∀ x y : (specOver h ⋙ F).obj B,
      (∀ i, (specOver h ⋙ F).map ((resNat (φ i)).app B) x =
        (specOver h ⋙ F).map ((resNat (φ i)).app B) y) → x = y) ∧
    (∀ s : ∀ i, (specOver h ⋙ F).obj ((pieceT (φ i)).obj B),
      (∀ i j, (specOver h ⋙ F).map ((natL (φ i) (φ j)).app B) (s i) =
        (specOver h ⋙ F).map ((natR (φ i) (φ j)).app B) (s j)) →
      ∃ x, ∀ i, (specOver h ⋙ F).map ((resNat (φ i)).app B) x = s i) := by
  have hopen : ∀ i, IsOpenImmersion (Spec.map (pushout.inl B.hom (φ i))) := fun i ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_SpecMap_pushout B.hom (φ i)).flip inferInstance
  let 𝒰 : (Spec B.right).OpenCover.{u} := Scheme.Cover.mkOfCovers ι
    (fun i ↦ Spec (pushout B.hom (φ i))) (fun i ↦ Spec.map (pushout.inl B.hom (φ i)))
    (fun x ↦ by
      obtain ⟨i, z, hz⟩ := hcov (Spec.map B.hom x)
      obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
        (isPullback_SpecMap_pushout B.hom (φ i)) x z hz.symm
      exact ⟨i, p, hp⟩) hopen
  have hP := hZ (Over.mk (Spec.map B.hom ≫ h)) 𝒰
  exact sep_glue_of_isSheafFor F _ hP
    (V := fun i ↦ unop ((specOver h).obj ((pieceT (φ i)).obj B)))
    (fun i ↦ Over.isoMk (Iso.refl _) (by
      show 𝟙 _ ≫ Spec.map (pushout.inl B.hom (φ i)) ≫ Spec.map B.hom ≫ h =
        Spec.map (φ i ≫ pushout.inr B.hom (φ i)) ≫ h
      rw [Category.id_comp, ← Category.assoc, ← Spec.map_comp,
        pushout.condition (f := B.hom) (g := φ i)]))
    (fun i ↦ ((specOver h).map ((resNat (φ i)).app B)).unop)
    (fun i ↦ by
      apply Over.OverMorphism.ext
      show Spec.map (pushout.inl B.hom (φ i)) = 𝟙 _ ≫ Spec.map (pushout.inl B.hom (φ i))
      rw [Category.id_comp])
    (W := fun i j ↦ unop ((specOver h).obj ((pieceT (φ i ≫ pushout.inl (φ i) (φ j))).obj B)))
    (fun i j ↦ ((specOver h).map ((natL (φ i) (φ j)).app B)).unop)
    (fun i j ↦ ((specOver h).map ((natR (φ i) (φ j)).app B)).unop)
    (fun i j Z gi gj hg ↦ by
      obtain ⟨l, hl1, hl2⟩ := exists_lift_pushout B.hom (φ i) (φ j) gi.left gj.left
        (congrArg CommaMorphism.left hg)
      refine ⟨Over.homMk l ?_, ?_, ?_⟩
      · show l ≫ Spec.map ((φ i ≫ pushout.inl (φ i) (φ j)) ≫ pushout.inr B.hom _) ≫ h = Z.hom
        rw [← descL_w B.hom (φ i) (φ j),
          Spec.map_comp (φ i ≫ pushout.inr B.hom (φ i)) (descL B.hom (φ i) (φ j)),
          Category.assoc, reassoc_of% hl1]
        exact Over.w gi
      · apply Over.OverMorphism.ext
        exact hl1
      · apply Over.OverMorphism.ext
        exact hl2)

/-- Goodness is local on `Spec R`: if finitely many open immersions `Spec R_i ⟶ Spec R`
cover `Spec R` and every composite `Spec R_i ⟶ Spec R ⟶ S` is good, so is `h`. -/
lemma good_of_cover (hZ : ZariskiSheaf F) (h : Spec R ⟶ S) {ι : Type u} [Finite ι]
    {Ri : ι → CommRingCat.{u}} (φ : ∀ i, R ⟶ Ri i) [∀ i, IsOpenImmersion (Spec.map (φ i))]
    (hcov : ∀ x, ∃ i y, Spec.map (φ i) y = x) (hgood : ∀ i, Good F (Spec.map (φ i) ≫ h)) :
    Good F h := by
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  have hi : ∀ i, PreservesColimitsOfShape J (pieceT (φ i) ⋙ specOver h ⋙ F) :=
    fun i ↦ preserves_piece (φ i) (hgood i) J
  have hij : ∀ i j, PreservesColimitsOfShape J
      (pieceT (φ i ≫ pushout.inl (φ i) (φ j)) ⋙ specOver h ⋙ F) := fun i j ↦ by
    refine preserves_piece _ ?_ J
    rw [Spec.map_comp, Category.assoc]
    exact good_comp _ (hgood i)
  refine ⟨isColimit_mapCocone_of_equalizer c (specOver h ⋙ F)
    (fun i ↦ pieceT (φ i) ⋙ specOver h ⋙ F)
    (fun i j ↦ pieceT (φ i ≫ pushout.inl (φ i) (φ j)) ⋙ specOver h ⋙ F)
    (fun i ↦ Functor.whiskerRight (resNat (φ i)) (specOver h ⋙ F))
    (fun i j ↦ Functor.whiskerRight (natL (φ i) (φ j)) (specOver h ⋙ F))
    (fun i j ↦ Functor.whiskerRight (natR (φ i) (φ j)) (specOver h ⋙ F))
    ?_ (fun B ↦ (sep_glue hZ h φ hcov B).1) (fun B ↦ (sep_glue hZ h φ hcov B).2)
    (fun i ↦ isColimitOfPreserves _ hc) (fun i j ↦ isColimitOfPreserves _ hc)⟩
  intro B x i j
  show ((specOver h ⋙ F).map ((resNat (φ i)).app B) ≫
      (specOver h ⋙ F).map ((natL (φ i) (φ j)).app B)) x =
    ((specOver h ⋙ F).map ((resNat (φ j)).app B) ≫
      (specOver h ⋙ F).map ((natR (φ i) (φ j)).app B)) x
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
    resNat_natL]

/-- With (F1a) and (F2), every morphism `Spec R ⟶ S` is good. -/
lemma good_all (hZ : ZariskiSheaf F) (h2 : FilteredColimits F) (h : Spec R ⟶ S) :
    Good F h := by
  have H : ∀ x : Spec R, ∃ (R' : CommRingCat.{u}) (g : Spec R' ⟶ Spec R),
      IsOpenImmersion g ∧ x ∈ Set.range g ∧ Good F (g ≫ h) := by
    intro x
    obtain ⟨R₁, f₁, hf₁, hx₁, -⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := h x) (U := ⊤) trivial
    obtain ⟨R', g, hg, hx, hgU⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (X := Spec R) (x := x) (U := h ⁻¹ᵁ f₁.opensRange) hx₁
    refine ⟨R', g, hg, hx, ?_⟩
    have hsub : Set.range (g ≫ h) ⊆ Set.range f₁ := by
      rintro _ ⟨y, rfl⟩
      exact hgU ⟨y, rfl⟩
    rw [← IsOpenImmersion.lift_fac f₁ (g ≫ h) hsub,
      ← Spec.map_preimage (IsOpenImmersion.lift f₁ (g ≫ h) hsub)]
    exact good_comp _ (good_of_isOpenImmersion h2 f₁)
  choose R' g hg hx hgood using H
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (g x))
    (fun x ↦ IsOpenImmersion.isOpen_range (g x)) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hx y⟩)
  have : ∀ i : t, IsOpenImmersion (Spec.map (Spec.preimage (g i))) := fun i ↦ by
    rw [Spec.map_preimage]
    exact hg i
  refine good_of_cover hZ h (ι := t) (fun i ↦ Spec.preimage (g i)) ?_ ?_
  · intro y
    obtain ⟨x, hxt, z, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨x, hxt⟩, z, by rw [Spec.map_preimage]; exact hz⟩
  · intro i
    rw [Spec.map_preimage]
    exact hgood i

end Local

section BaseChangeF2

variable {S S' : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- The components of `algebraFunctorCompIso`. -/
def algebraOverCompIso {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S')
    (g : S' ⟶ S) (B : Type u) [CommRing B] [Algebra A B] :
    algebraOver (f ≫ g) B ≅ (Over.map g).obj (algebraOver f B) :=
  Over.isoMk (Iso.refl _) (by
    show 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f ≫ g
    rw [Category.id_comp, Category.assoc])

/-- Base change of `algebraFunctor f` along `g` is `algebraFunctor (f ≫ g)`. -/
def algebraFunctorCompIso {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S')
    (g : S' ⟶ S) : algebraFunctor f ⋙ (Over.map g).op ≅ algebraFunctor (f ≫ g) :=
  NatIso.ofComponents (fun B ↦ (algebraOverCompIso f g B).op) (by
    intro B C φ
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    show 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (φ.hom : B →+* C)) =
      Spec.map (CommRingCat.ofHom (φ.hom : B →+* C)) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id])

/-- (F2) for the base change of `F`, given (F1a) and (F2) for `F`. -/
theorem filteredColimits (hZ : ZariskiSheaf F) (h2 : FilteredColimits F) (g : S' ⟶ S) :
    FilteredColimits (baseChange g F) := by
  intro A _ f _
  have hg := good_all hZ h2 (f ≫ g)
  constructor
  intro J _ _
  have := hg.preserves_filtered_colimits J
  let E := commAlgCatEquivUnder (CommRingCat.of A)
  have : PreservesColimitsOfShape J (E.functor ⋙ (specOver (f ≫ g) ⋙ F)) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (algebraFunctorIso (f ≫ g)) F ≪≫
      Functor.isoWhiskerRight (algebraFunctorCompIso f g).symm F ≪≫ Functor.associator _ _ _)

end BaseChangeF2

end BaseChange

end Langlands.AlgebraicGeometry.UnramifiedFunctor
