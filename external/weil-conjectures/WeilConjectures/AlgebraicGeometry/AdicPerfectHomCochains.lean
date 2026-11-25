/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModels
import WeilConjectures.AlgebraicGeometry.AdicPerfectModuleHom

/-! # Evaluation of ordinary quotient Hom cochains

Source: Stacks Project, Tags 093T, 09C6 and 0A8H.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w uE hE uC hC
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion CochainComplex CochainComplex.HomComplex
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change
  adicPerfectLocalComplex adicPerfectQuotientComplex adicPerfectQuotientStep
  completed adicPerfectLocalFunctor

private abbrev linearHom {A : Type w} [CommRing A] (M N : ModuleCat.{w} A) :=
  ModuleCat.of A (M →ₗ[A] N)

private abbrev homMap {A : Type w} [CommRing A]
    {M M' N N' : ModuleCat.{w} A} (a : M' ⟶ M) (b : N ⟶ N') :
    linearHom M N ⟶ linearHom M' N' :=
  ModuleCat.ofHom ((LinearMap.llcomp A M' N N' b.hom).comp (LinearMap.lcomp A N a.hom))

private def cochainProj {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) (q i j : ℤ) (h : i + q = j) :
    (moduleHomComplex P Q).X q ⟶ linearHom (P.X i) (Q.X j) :=
  ModuleCat.ofHom
    { toFun := fun z ↦ (z.v i j h).hom
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private def cochainSingle {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) (q i : ℤ) :
    linearHom (P.X i) (Q.X (i + q)) ⟶ (moduleHomComplex P Q).X q :=
  ModuleCat.ofHom
    { toFun := fun f ↦ Cochain.single (ModuleCat.ofHom f) q
      map_add' := by
        intro f g
        apply Cochain.ext
        intro p r h
        by_cases hp : p = i
        · subst p
          obtain rfl : r = i + q := h.symm
          simp
        · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]
      map_smul' := by
        intro r f
        apply Cochain.ext
        intro p s h
        by_cases hp : p = i
        · subst p
          obtain rfl : s = i + q := h.symm
          simp
          rfl
        · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp] }

private theorem cochainSingle_proj {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) (q i : ℤ) :
    cochainSingle P Q q i ≫ cochainProj P Q q i (i + q) rfl = 𝟙 _ := by
  ext f x
  change ((Cochain.single (ModuleCat.ofHom f) q).v i (i + q) rfl).hom x = f x
  rw [Cochain.single_v]
  rfl

private theorem cochainSingle_proj_ne {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) (q i p j : ℤ) (h : p + q = j)
    (hp : p ≠ i) :
    cochainSingle P Q q i ≫ cochainProj P Q q p j h = 0 := by
  ext f x
  change ((Cochain.single (ModuleCat.ofHom f) q).v p j h).hom x = 0
  rw [Cochain.single_v_eq_zero _ _ _ _ _ hp]
  rfl

private theorem cochain_sum_id {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i)) (q : ℤ) :
    ∑ i ∈ s, cochainProj P Q q i (i + q) rfl ≫ cochainSingle P Q q i = 𝟙 _ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro i j hij
  subst j
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
  let ev : Cochain P Q q →+ (P.X i ⟶ Q.X (i + q)) :=
    { toFun := fun x ↦ x.v i (i + q) rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ k ∈ s, Cochain.single (z.v k (k + q) rfl) q) = _
  rw [map_sum]
  by_cases hi : i ∈ s
  · rw [Finset.sum_eq_single i]
    · exact Cochain.single_v (z.v i (i + q) rfl) q rfl
    · intro k hk hki
      exact Cochain.single_v_eq_zero (z.v k (k + q) rfl) q i (i + q) rfl (Ne.symm hki)
    · exact fun h ↦ (h hi).elim
  · rw [Finset.sum_eq_zero]
    · exact ((hs i hi).eq_of_src 0 (z.v i (i + q) rfl))
    · intro k hk
      exact Cochain.single_v_eq_zero (z.v k (k + q) rfl) q i (i + q) rfl
        (fun h ↦ hi (h.symm ▸ hk))

private theorem group_sum_apply {B C : AddCommGrpCat} {ι : Type*}
    (s : Finset ι) (f : ι → (B ⟶ C)) (x : B) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem group_zsmul_apply {B C : AddCommGrpCat} (f : B ⟶ C) (r : ℤ) (x : B) :
    (r • f) x = r • f x := rfl

private theorem cochainProj_ext {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero (P.X i))
    (H : ModuleCat.{w} A ⥤ AddCommGrpCat.{hE}) [H.Additive] (q : ℤ)
    {x y : H.obj ((moduleHomComplex P Q).X q)}
    (h : ∀ i, H.map (cochainProj P Q q i (i + q) rfl) x =
      H.map (cochainProj P Q q i (i + q) rfl) y) : x = y := by
  have hh := congrArg (fun f ↦ H.map f) (cochain_sum_id P Q s hs q)
  rw [H.map_sum, H.map_id] at hh
  have hx := ConcreteCategory.congr_hom hh x
  have hy := ConcreteCategory.congr_hom hh y
  change (∑ i ∈ s, H.map
    (cochainProj P Q q i (i + q) rfl ≫ cochainSingle P Q q i)) x = x at hx
  change (∑ i ∈ s, H.map
    (cochainProj P Q q i (i + q) rfl ≫ cochainSingle P Q q i)) y = y at hy
  rw [← hx, ← hy]
  simp only [H.map_comp, group_sum_apply, AddCommGrpCat.comp_apply, h]

private theorem cochain_delta_proj {A : Type w} [CommRing A]
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) (q r i j : ℤ) (h : i + r = j) :
    (moduleHomComplex P Q).d q r ≫ cochainProj P Q r i j h =
      cochainProj P Q q i (i + q) rfl ≫ homMap (𝟙 _) (Q.d (i + q) j) +
        (r.negOnePow : ℤˣ) •
          (cochainProj P Q q (i + r - q) j (by omega) ≫
            homMap (P.d i (i + r - q)) (𝟙 _)) := by
  ext z x
  rfl

private def cochainRealizationMap {A : Type w} [CommRing A]
    {E : Type uE} [Category.{hE} E] [Preadditive E]
    (F : ModuleCat.{w} A ⥤ E) [F.Additive]
    (H : ModuleCat.{w} A ⥤ AddCommGrpCat.{hE}) [H.Additive]
    (t : ∀ M N : ModuleCat.{w} A, H.obj (linearHom M N) →+ (F.obj M ⟶ F.obj N))
    (ht : ∀ (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
      (x : H.obj (linearHom M N)),
      t M' N' (H.map (homMap a b) x) = F.map a ≫ t M N x ≫ F.map b)
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).obj (moduleHomComplex P Q) ⟶
      HomComplex ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) where
  f q := AddCommGrpCat.ofHom
    { toFun := fun x ↦ Cochain.mk (fun i j h ↦
        t (P.X i) (Q.X j) (H.map (cochainProj P Q q i j h) x))
      map_zero' := by apply Cochain.ext; intros; simp
      map_add' := by intros; apply Cochain.ext; intros; simp }
  comm' q r _ := by
    ext x
    apply Cochain.ext
    intro i j hij
    change (δ q r (Cochain.mk
      (F := ((F.mapHomologicalComplex (.up ℤ)).obj P))
      (G := ((F.mapHomologicalComplex (.up ℤ)).obj Q)) (fun i j h ↦
      t (P.X i) (Q.X j) (H.map (cochainProj P Q q i j h) x)))).v i j hij =
      t (P.X i) (Q.X j)
        (H.map (cochainProj P Q r i j hij) (H.map ((moduleHomComplex P Q).d q r) x))
    rw [← AddCommGrpCat.comp_apply, ← H.map_comp, cochain_delta_proj]
    simp only [H.map_add, Units.smul_def, H.map_zsmul, AddCommGrpCat.hom_add_apply,
      group_zsmul_apply, map_add, map_zsmul, H.map_comp,
      AddCommGrpCat.comp_apply, ht, F.map_id, Category.id_comp, Category.comp_id]
    rfl

private theorem cochainRealizationMap_v {A : Type w} [CommRing A]
    {E : Type uE} [Category.{hE} E] [Preadditive E]
    (F : ModuleCat.{w} A ⥤ E) [F.Additive]
    (H : ModuleCat.{w} A ⥤ AddCommGrpCat.{hE}) [H.Additive]
    (t : ∀ M N : ModuleCat.{w} A, H.obj (linearHom M N) →+ (F.obj M ⟶ F.obj N))
    (ht : ∀ (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
      (x : H.obj (linearHom M N)),
      t M' N' (H.map (homMap a b) x) = F.map a ≫ t M N x ≫ F.map b)
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ)
    (q i j : ℤ) (h : i + q = j)
    (x : ((H.mapHomologicalComplex (.up ℤ)).obj (moduleHomComplex P Q)).X q) :
    (((cochainRealizationMap F H t ht P Q).f q) x).v i j h =
      t (P.X i) (Q.X j) (H.map (cochainProj P Q q i j h) x) := by
  rfl

private theorem cochainRealizationMap_bijective {A : Type w} [CommRing A]
    {E : Type uE} [Category.{hE} E] [Preadditive E]
    (F : ModuleCat.{w} A ⥤ E) [F.Additive]
    (H : ModuleCat.{w} A ⥤ AddCommGrpCat.{hE}) [H.Additive]
    (t : ∀ M N : ModuleCat.{w} A, H.obj (linearHom M N) →+ (F.obj M ⟶ F.obj N))
    (ht : ∀ (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
      (x : H.obj (linearHom M N)),
      t M' N' (H.map (homMap a b) x) = F.map a ≫ t M N x ≫ F.map b)
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero (P.X i))
    (hb : ∀ i j, Function.Bijective (t (P.X i) (Q.X j))) (q : ℤ) :
    Function.Bijective ((cochainRealizationMap F H t ht P Q).f q) := by
  classical
  constructor
  · intro x y hxy
    apply cochainProj_ext P Q s hs H q
    intro i
    apply (hb i (i + q)).1
    exact Cochain.congr_v hxy i (i + q) rfl
  · intro z
    let x (i : ℤ) : H.obj (linearHom (P.X i) (Q.X (i + q))) :=
      (Equiv.ofBijective _ (hb i (i + q))).symm (z.v i (i + q) rfl)
    refine ⟨∑ i ∈ s, H.map (cochainSingle P Q q i) (x i), ?_⟩
    apply Cochain.ext
    intro i j hij
    subst j
    change t (P.X i) (Q.X (i + q))
      (H.map (cochainProj P Q q i (i + q) rfl)
        (∑ k ∈ s, H.map (cochainSingle P Q q k) (x k))) = _
    rw [map_sum]
    by_cases hi : i ∈ s
    · rw [Finset.sum_eq_single i]
      · rw [← AddCommGrpCat.comp_apply, ← H.map_comp,
          cochainSingle_proj, H.map_id]
        simpa only [x, AddCommGrpCat.id_apply] using
          (Equiv.ofBijective_apply_symm_apply (t (P.X i) (Q.X (i + q)))
            (hb i (i + q)) (z.v i (i + q) rfl))
      · intro k hk hki
        rw [← AddCommGrpCat.comp_apply, ← H.map_comp,
          cochainSingle_proj_ne P Q q k i (i + q) rfl (Ne.symm hki), H.map_zero]
        rfl
      · exact fun h ↦ (h hi).elim
    · rw [Finset.sum_eq_zero]
      · rw [map_zero]
        exact (F.map_isZero (hs i hi)).eq_of_src _ _
      · intro k hk
        rw [← AddCommGrpCat.comp_apply, ← H.map_comp,
          cochainSingle_proj_ne P Q q k i (i + q) rfl (fun h ↦ hi (h.symm ▸ hk)), H.map_zero]
        rfl

attribute [local irreducible] cochainRealizationMap

private theorem scalar_cochain_v
    {C E : Type*} [Category C] [Preadditive C] [Category E] [Preadditive E]
    (Φ : C ⥤ E) [Φ.Additive] {P Q : CochainComplex C ℤ}
    {P' Q' : CochainComplex E ℤ}
    (a : (Φ.mapHomologicalComplex (.up ℤ)).obj P ≅ P')
    (b : (Φ.mapHomologicalComplex (.up ℤ)).obj Q ≅ Q')
    (q : ℤ) (z : Cochain P Q q) (i j : ℤ) (h : i + q = j) :
    ((((Cochain.ofHom a.inv).comp (z.map Φ) (zero_add q)).comp
      (Cochain.ofHom b.hom) (add_zero q)).v i j h) =
        a.inv.f i ≫ Φ.map (z.v i j h) ≫ b.hom.f j := by
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.map_v, Category.assoc]

private theorem balance_inv_f
    {B C D E : Type*} [Category B] [Preadditive B]
    [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    (L : B ⥤ C) [L.Additive] (G : C ⥤ D) [G.Additive]
    (H : D ⥤ E) [H.Additive] (K : C ⥤ E) [K.Additive]
    (δ : G ⋙ H ≅ K) (R : CochainComplex B ℤ) (i : ℤ) :
    ((Functor.mapHomologicalComplexCompIso δ (.up ℤ)).app
        ((L.mapHomologicalComplex (.up ℤ)).obj R)).inv.f i =
      (((Functor.associator L G H) ≪≫ Functor.isoWhiskerLeft L δ).app (R.X i)).inv := by
  simp only [Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.app_inv, Iso.trans_inv, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.comp_id]
  rfl

private theorem balance_hom_f
    {B C D E : Type*} [Category B] [Preadditive B]
    [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    (L : B ⥤ C) [L.Additive] (G : C ⥤ D) [G.Additive]
    (H : D ⥤ E) [H.Additive] (K : C ⥤ E) [K.Additive]
    (δ : G ⋙ H ≅ K) (R : CochainComplex B ℤ) (i : ℤ) :
    ((Functor.mapHomologicalComplexCompIso δ (.up ℤ)).app
        ((L.mapHomologicalComplex (.up ℤ)).obj R)).hom.f i =
      (((Functor.associator L G H) ≪≫ Functor.isoWhiskerLeft L δ).app (R.X i)).hom := by
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f,
    Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
  rfl

private theorem cochainComparison
    {A : Type w} [CommRing A]
    (E : ℕ → Type uE) [∀ n, Category.{hE} (E n)] [∀ n, Preadditive (E n)]
    (F : ∀ n, ModuleCat.{w} A ⥤ E n) [∀ n, (F n).Additive]
    (H : ℕ → ModuleCat.{w} A ⥤ AddCommGrpCat.{hE}) [∀ n, (H n).Additive]
    (Φ : ∀ n, E (n + 1) ⥤ E n) [∀ n, (Φ n).Additive]
    (α : ∀ n, F (n + 1) ⋙ Φ n ≅ F n)
    (σ : ∀ n, H (n + 1) ⟶ H n)
    (t : ∀ n (M N : ModuleCat.{w} A),
      (H n).obj (linearHom M N) →+ ((F n).obj M ⟶ (F n).obj N))
    (ht : ∀ n (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
      (x : (H n).obj (linearHom M N)),
      t n M' N' ((H n).map (homMap a b) x) =
        (F n).map a ≫ t n M N x ≫ (F n).map b)
    (htstep : ∀ n (M N : ModuleCat.{w} A)
      (x : (H (n + 1)).obj (linearHom M N)),
      t n M N ((σ n).app (linearHom M N) x) =
        ((α n).app M).inv ≫ (Φ n).map (t (n + 1) M N x) ≫ ((α n).app N).hom)
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero (P.X i))
    (hb : ∀ n i j, Function.Bijective (t n (P.X i) (Q.X j)))
    (βP : ∀ n,
      ((Φ n).mapHomologicalComplex (.up ℤ)).obj
          (((F (n + 1)).mapHomologicalComplex (.up ℤ)).obj P) ≅
        ((F n).mapHomologicalComplex (.up ℤ)).obj P)
    (βQ : ∀ n,
      ((Φ n).mapHomologicalComplex (.up ℤ)).obj
          (((F (n + 1)).mapHomologicalComplex (.up ℤ)).obj Q) ≅
        ((F n).mapHomologicalComplex (.up ℤ)).obj Q)
    (hβP : ∀ n i, (βP n).inv.f i = ((α n).app (P.X i)).inv)
    (hβQ : ∀ n i, (βQ n).hom.f i = ((α n).app (Q.X i)).hom) :
    let C := fun n ↦ HomComplex (((F n).mapHomologicalComplex (.up ℤ)).obj P)
      (((F n).mapHomologicalComplex (.up ℤ)).obj Q)
    let D := fun n ↦ ((H n).mapHomologicalComplex (.up ℤ)).obj (moduleHomComplex P Q)
    ∃ e : ∀ n, C n ≅ D n, ∀ n q (z : (C (n + 1)).X q),
      (e n).hom.f q
        (((Cochain.ofHom (βP n).inv).comp (z.map (Φ n)) (zero_add q)).comp
          (Cochain.ofHom (βQ n).hom) (add_zero q)) =
        (σ n).app ((moduleHomComplex P Q).X q) ((e (n + 1)).hom.f q z) := by
  classical
  let C := fun n ↦ HomComplex (((F n).mapHomologicalComplex (.up ℤ)).obj P)
    (((F n).mapHomologicalComplex (.up ℤ)).obj Q)
  let D := fun n ↦ ((H n).mapHomologicalComplex (.up ℤ)).obj (moduleHomComplex P Q)
  let f (n : ℕ) : D n ⟶ C n := cochainRealizationMap (F n) (H n) (t n) (ht n) P Q
  have hf (n : ℕ) (q : ℤ) : Function.Bijective ((f n).f q) :=
    cochainRealizationMap_bijective (F n) (H n) (t n) (ht n) P Q s hs (hb n) q
  have hfi (n : ℕ) : IsIso (f n) := by
    have (q : ℤ) : IsIso ((f n).f q) := (ConcreteCategory.isIso_iff_bijective _).mpr (hf n q)
    exact HomologicalComplex.Hom.isIso_of_components (f n)
  let e (n : ℕ) : C n ≅ D n := (asIso (f n)).symm
  refine ⟨e, ?_⟩
  intro n q z
  have square (x : (D (n + 1)).X q) :
      (f n).f q ((σ n).app ((moduleHomComplex P Q).X q) x) =
        ((Cochain.ofHom (βP n).inv).comp
          (((f (n + 1)).f q x).map (Φ n)) (zero_add q)).comp
            (Cochain.ofHom (βQ n).hom) (add_zero q) := by
    apply Cochain.ext
    intro i j hij
    rw [scalar_cochain_v]
    dsimp only [f]
    erw [cochainRealizationMap_v, cochainRealizationMap_v]
    have hx := (ConcreteCategory.congr_hom
      ((σ n).naturality (cochainProj P Q q i j hij)) x).symm
    change (H n).map (cochainProj P Q q i j hij)
        ((σ n).app ((moduleHomComplex P Q).X q) x) =
      (σ n).app (linearHom (P.X i) (Q.X j))
        ((H (n + 1)).map (cochainProj P Q q i j hij) x) at hx
    erw [hx, htstep, hβP, hβQ]
  have hfe (m : ℕ) (y : (C m).X q) : (f m).f q ((e m).hom.f q y) = y := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun g ↦ g.f q) (e m).hom_inv_id) y
  apply (hf n q).1
  rw [hfe, square, hfe]

private def scalarBalance (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    change (adicResidueLocalProjection.{u, v} X J U (n + 1)) ⋙
        change (adicPerfectQuotientScalarStep.{u, v} X J U n) ≅
      change (adicResidueLocalProjection.{u, v} X J U n) :=
  adicFiniteChangeComp (adicResidueLocalProjection.{u, v} X J U (n + 1))
    (adicPerfectQuotientScalarStep.{u, v} X J U n) ≪≫
      eqToIso (congrArg change (adicPerfectQuotientScalarStep_comp.{u, v} X J U n))

private theorem moduleStep_balance (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicPerfectQuotientModuleStep.{u, v} X J U n =
      Functor.associator (adicPerfectLocalFunctor.{u, v} X J U)
        (change (adicResidueLocalProjection.{u, v} X J U (n + 1)))
        (change (adicPerfectQuotientScalarStep.{u, v} X J U n)) ≪≫
      Functor.isoWhiskerLeft (adicPerfectLocalFunctor.{u, v} X J U)
        (scalarBalance.{u, v} X J U n) := by
  unfold adicPerfectQuotientModuleStep scalarBalance
  rfl

attribute [local irreducible] scalarBalance

private structure OrdinaryDiagram
    (E : ℕ → Type uE) [∀ n, Category.{hE} (E n)] [∀ n, Preadditive (E n)]
    (Φ : ∀ n, E (n + 1) ⥤ E n) [∀ n, (Φ n).Additive] where
  obj : ∀ n, CochainComplex (E n) ℤ
  step : ∀ n, ((Φ n).mapHomologicalComplex (.up ℤ)).obj (obj (n + 1)) ≅ obj n

private abbrev HasComparison
    {E : ℕ → Type uE} [∀ n, Category.{hE} (E n)] [∀ n, Preadditive (E n)]
    {Φ : ∀ n, E (n + 1) ⥤ E n} [∀ n, (Φ n).Additive]
    (DP DQ : OrdinaryDiagram E Φ) (D : ℕ → CochainComplex AddCommGrpCat.{hE} ℤ)
    (d : ∀ n q, (D (n + 1)).X q → (D n).X q) : Prop :=
  ∃ e : ∀ n, HomComplex (DP.obj n) (DQ.obj n) ≅ D n,
    ∀ n q (z : Cochain (DP.obj (n + 1)) (DQ.obj (n + 1)) q),
      (e n).hom.f q
        (((Cochain.ofHom (DP.step n).inv).comp (z.map (Φ n)) (zero_add q)).comp
          (Cochain.ofHom (DQ.step n).hom) (add_zero q)) =
        d n q ((e (n + 1)).hom.f q z)

private def baseDiagram
    {E : ℕ → Type uE} [∀ n, Category.{hE} (E n)] [∀ n, Preadditive (E n)]
    {C : Type uC} [Category.{hC} C] [Preadditive C]
    (G : ∀ n, C ⥤ E n) [∀ n, (G n).Additive]
    (Φ : ∀ n, E (n + 1) ⥤ E n) [∀ n, (Φ n).Additive]
    (δ : ∀ n, G (n + 1) ⋙ Φ n ≅ G n) (R : CochainComplex C ℤ) :
    OrdinaryDiagram E Φ where
  obj n := ((G n).mapHomologicalComplex (.up ℤ)).obj R
  step n := (Functor.mapHomologicalComplexCompIso (δ n) (.up ℤ)).app R

private theorem balancedComparison
    {A : Type w} [CommRing A]
    {C : Type uC} [Category.{hC} C] [Preadditive C]
    (L : ModuleCat.{w} A ⥤ C) [L.Additive]
    (E : ℕ → Type uE) [∀ n, Category.{hE} (E n)] [∀ n, Preadditive (E n)]
    (G : ∀ n, C ⥤ E n) [∀ n, (G n).Additive]
    (H : ℕ → ModuleCat.{w} A ⥤ AddCommGrpCat.{hE}) [∀ n, (H n).Additive]
    (Φ : ∀ n, E (n + 1) ⥤ E n) [∀ n, (Φ n).Additive]
    (δ : ∀ n, G (n + 1) ⋙ Φ n ≅ G n)
    (α : ∀ n, (L ⋙ G (n + 1)) ⋙ Φ n ≅ L ⋙ G n)
    (hα : ∀ n, α n = Functor.associator L (G (n + 1)) (Φ n) ≪≫
      Functor.isoWhiskerLeft L (δ n))
    (σ : ∀ n, H (n + 1) ⟶ H n)
    (t : ∀ n (M N : ModuleCat.{w} A),
      (H n).obj (linearHom M N) →+ ((L ⋙ G n).obj M ⟶ (L ⋙ G n).obj N))
    (ht : ∀ n (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
      (x : (H n).obj (linearHom M N)),
      t n M' N' ((H n).map (homMap a b) x) =
        (L ⋙ G n).map a ≫ t n M N x ≫ (L ⋙ G n).map b)
    (htstep : ∀ n (M N : ModuleCat.{w} A)
      (x : (H (n + 1)).obj (linearHom M N)),
      t n M N ((σ n).app (linearHom M N) x) =
        ((α n).app M).inv ≫ (Φ n).map (t (n + 1) M N x) ≫ ((α n).app N).hom)
    (P Q : CochainComplex (ModuleCat.{w} A) ℤ)
    (s : Finset ℤ) (hs : ∀ i ∉ s, IsZero (P.X i))
    (hb : ∀ n i j, Function.Bijective (t n (P.X i) (Q.X j))) :
    HasComparison
      (baseDiagram G Φ δ ((L.mapHomologicalComplex (.up ℤ)).obj P))
      (baseDiagram G Φ δ ((L.mapHomologicalComplex (.up ℤ)).obj Q))
      (fun n ↦ ((H n).mapHomologicalComplex (.up ℤ)).obj (moduleHomComplex P Q))
      (fun n _ x ↦ (σ n).app _ x) := by
  let β (R : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) :=
    (baseDiagram G Φ δ ((L.mapHomologicalComplex (.up ℤ)).obj R)).step n
  have hβinv (R : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) (i : ℤ) :
      (β R n).inv.f i = ((α n).app (R.X i)).inv := by
    rw [hα]
    exact balance_inv_f L (G (n + 1)) (Φ n) (G n) (δ n) R i
  have hβhom (R : CochainComplex (ModuleCat.{w} A) ℤ) (n : ℕ) (i : ℤ) :
      (β R n).hom.f i = ((α n).app (R.X i)).hom := by
    rw [hα]
    exact balance_hom_f L (G (n + 1)) (Φ n) (G n) (δ n) R i
  exact cochainComparison E (fun n ↦ L ⋙ G n) H Φ α σ t ht htstep
    P Q s hs hb (β P) (β Q) (hβinv P) (hβhom Q)

private abbrev actualDiagram (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    OrdinaryDiagram
      (fun n ↦ Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U))
      (fun n ↦ change (adicPerfectQuotientScalarStep.{u, v} X J U n)) where
  obj n := adicPerfectQuotientComplex.{u, v} X J U P n
  step n := adicPerfectQuotientStep.{u, v} X J U P n

private def reductionDiagram (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U)) :
    OrdinaryDiagram
      (fun n ↦ Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U))
      (fun n ↦ change (adicPerfectQuotientScalarStep.{u, v} X J U n)) :=
  baseDiagram
    (fun n ↦ change (adicResidueLocalProjection.{u, v} X J U n))
    (fun n ↦ change (adicPerfectQuotientScalarStep.{u, v} X J U n))
    (scalarBalance.{u, v} X J U) P

private abbrev realizedDiagram (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :=
  reductionDiagram X J U
    (((adicPerfectLocalFunctor.{u, v} X J U).mapHomologicalComplex (.up ℤ)).obj P)

private theorem localComplex_realization (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    adicPerfectLocalComplex.{u, v} X J U P =
      ((adicPerfectLocalFunctor.{u, v} X J U).mapHomologicalComplex (.up ℤ)).obj P := by
  unfold adicPerfectLocalComplex adicPerfectLocalFunctor
  rfl

private theorem actualDiagram_realized (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    actualDiagram X J U P = realizedDiagram X J U P := by
  have h : actualDiagram X J U P =
      reductionDiagram X J U (adicPerfectLocalComplex.{u, v} X J U P) := by
    unfold actualDiagram reductionDiagram baseDiagram adicPerfectQuotientComplex
      adicPerfectQuotientStep scalarBalance
    rfl
  exact h.trans (congrArg (reductionDiagram X J U) (localComplex_realization X J U P))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Evaluation identifies the entire graded quotient Hom complex, before taking
cycles, boundaries or homotopy classes. The equation is in every cochain degree.
No weak contractibility or exactness of section evaluation is assumed.

Source: Stacks Project, Modules on Sites, Tag 093T; proetale.tex, Tag 09C6,
the displayed quotient Hom calculation; More on Algebra, Tag 0A8H.
(auxiliary; not a blueprint node).

Proof: compose the scalar-balancing isomorphism for completed-to-finite change
with the constant-sheaf scalar-extension comparison, and restrict to the slice.
This identifies each ordinary quotient term with the constant realization of
its algebraic quotient. For a finite free source, evaluate a sheaf-linear map
on the finite basis. This gives the constant sheaf of algebraic Hom after
quotienting; finite-projective splittings give the same comparison for retracts.
The source terms outside [a,b] vanish. Thus in every degree the Hom product is
a finite product, and both quotient and additive constant realization commute
with it. The termwise comparisons assemble to the asserted graded isomorphisms.
Their naturality for precomposition and postcomposition identifies both summands
of the signed differential d_Q f - (-1)^q f d_P, giving complex isomorphisms.
For the successor equation, scalar balancing multiplies the adjacent scalars.
On a locally constant linear map and a pure tensor in its source, both sides
are its value followed by the quotient map. Such local tensors generate; sheaf
separatedness gives equality on all sections. It passes to finite-projective
retracts and the finite product. This verifies the displayed equation in every
degree, without passage to cohomology. Empty intervals, zero rings, the unit
ideal and empty slices give zero complexes and their unique isomorphisms. -/
theorem adicPerfectHomCochains (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (P Q : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) :
    let G := AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U)) ⋙
        forget₂ (ModuleCat A) AddCommGrpCat
    let K := CochainComplex.moduleHomComplex P Q
    let C := fun n : ℕ ↦ CochainComplex.HomComplex
      (adicPerfectQuotientComplex.{u, v} X J U P n)
      (adicPerfectQuotientComplex.{u, v} X J U Q n)
    let D := fun n : ℕ ↦ (G.mapHomologicalComplex (.up ℤ)).obj
      (((AdicCohomology.quotient J (n + 1)).mapHomologicalComplex (.up ℤ)).obj K)
    ∃ e : ∀ n : ℕ, C n ≅ D n,
      ∀ (n : ℕ) (q : ℤ)
        (z : Cochain (adicPerfectQuotientComplex.{u, v} X J U P (n + 1))
          (adicPerfectQuotientComplex.{u, v} X J U Q (n + 1)) q),
        (e n).hom.f q
          (((Cochain.ofHom (adicPerfectQuotientStep.{u, v} X J U P n).inv).comp
            (z.map (change (adicPerfectQuotientScalarStep.{u, v} X J U n)))
              (zero_add q)).comp
                (Cochain.ofHom (adicPerfectQuotientStep.{u, v} X J U Q n).hom)
                  (add_zero q)) =
          G.map ((AdicCohomology.transition J
            (Nat.add_le_add_right (Nat.le_succ n) 1)).app (K.X q))
              ((e (n + 1)).hom.f q z) := by
  classical
  let T := coefficientProEtaleModelTopology.{u, v} X
  let G := AdicCohomology.sections (T.over U) (Over.mk (𝟙 U)) ⋙
    forget₂ (ModuleCat A) AddCommGrpCat
  let H := fun n : ℕ ↦ AdicCohomology.quotient J (n + 1) ⋙ G
  let Φ := fun n : ℕ ↦ change (adicPerfectQuotientScalarStep.{u, v} X J U n)
  let α := fun n : ℕ ↦ adicPerfectQuotientModuleStep.{u, v} X J U n
  let σ (n : ℕ) : H (n + 1) ⟶ H n :=
    Functor.whiskerRight
      (AdicCohomology.transition J (Nat.add_le_add_right (Nat.le_succ n) 1)) G
  let δ (n : ℕ) := scalarBalance.{u, v} X J U n
  let s := Finset.Icc a b
  have hs (i : ℤ) (hi : i ∉ s) : IsZero (P.X i) := by
    have hi' : ¬ (a ≤ i ∧ i ≤ b) := by simpa only [s, Finset.mem_Icc] using hi
    by_cases hia : i < a
    · exact (P.isStrictlyGE_iff a).mp _ha i hia
    · exact (P.isStrictlyLE_iff b).mp _hb i (by omega)
  obtain ⟨t, htbij, htnat, htstep⟩ := adicPerfectModuleHom.{u, v} X J U
  have hstep : ∀ n (M N : ModuleCat.{max v (u + 1)} A)
      (x : (H (n + 1)).obj (linearHom M N)),
      t n M N ((σ n).app (linearHom M N) x) =
        ((α n).app M).inv ≫ (Φ n).map (t (n + 1) M N x) ≫ ((α n).app N).hom :=
    htstep
  have h := balancedComparison (C := Mod ((completed T A J).over U))
    (adicPerfectLocalFunctor.{u, v} X J U)
    (fun n ↦ Mod ((finite T A J n).over U))
    (fun n ↦ change (adicResidueLocalProjection.{u, v} X J U n)) H Φ δ α
    (moduleStep_balance.{u, v} X J U) σ t htnat hstep
    P Q s hs (fun n i j ↦ htbij n (P.X i) (Q.X j) (_hP i).1 (_hP i).2)
  let D (n : ℕ) := (G.mapHomologicalComplex (.up ℤ)).obj
    (((AdicCohomology.quotient J (n + 1)).mapHomologicalComplex (.up ℤ)).obj
      (moduleHomComplex P Q))
  let d (n : ℕ) (q : ℤ) : (D (n + 1)).X q → (D n).X q :=
    G.map ((AdicCohomology.transition J
      (Nat.add_le_add_right (Nat.le_succ n) 1)).app ((moduleHomComplex P Q).X q))
  change HasComparison (actualDiagram X J U P) (actualDiagram X J U Q) D d
  rw [actualDiagram_realized X J U P, actualDiagram_realized X J U Q]
  exact h

end AlgebraicGeometry.Scheme
