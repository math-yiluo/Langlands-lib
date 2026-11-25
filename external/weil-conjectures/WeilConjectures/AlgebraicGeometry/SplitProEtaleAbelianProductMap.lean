/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits

/-! # The canonical product map over a split finite cover -/

@[expose] public section

open CategoryTheory
private theorem sheetTranspose
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} (adjF : F ⊣ R)
    {K : D ⥤ E} {T : E ⥤ D} (adjK : K ⊣ T)
    {H : C ⥤ E} {S : E ⥤ C} (adjH : H ⊣ S)
    (a : H ⟶ F ⋙ K) (N : D) :
    adjH.homEquiv _ _ (a.app (R.obj N) ≫ K.map (adjF.counit.app N)) =
      R.map (adjK.unit.app N) ≫
        (conjugateEquiv (adjF.comp adjK) adjH a).app (K.obj N) := by
  let b := conjugateEquiv (adjF.comp adjK) adjH a
  have hu := unit_conjugateEquiv (adjF.comp adjK) adjH a (R.obj N)
  simp only [Adjunction.comp_unit_app] at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← hu, Category.assoc, ← b.naturality]
  simp only [Functor.comp_map]
  have hn := adjK.unit.naturality (adjF.counit.app N)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Category.assoc]
  rw [← Category.assoc (R.map _) (R.map _) (b.app _),
    ← R.map_comp, ← hn]
  rw [R.map_comp]
  simpa only [Category.assoc, Category.id_comp, Functor.id_obj, b] using
    congrArg (fun z ↦ z ≫ R.map (adjK.unit.app N) ≫ b.app (K.obj N))
      (adjF.right_triangle_components N)

private theorem sheetNormalized
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} (adjF : F ⊣ R)
    {K K' : D ⥤ E} {T : E ⥤ D} (adjK : K ⊣ T) (adjK' : K' ⊣ T)
    {H H' : C ⥤ E} {S : E ⥤ C} (adjH : H ⊣ S) (adjH' : H' ⊣ S)
    (a : H ⟶ F ⋙ K) (b : T ⋙ R ⟶ S)
    (hab : conjugateEquiv (adjF.comp adjK) adjH a = b)
    (N : D) (q' : H'.obj (R.obj N) ⟶ K'.obj N)
    (hq' : adjH'.homEquiv _ _ q' = R.map (adjK'.unit.app N) ≫ b.app (K'.obj N)) :
    (a.app (R.obj N) ≫ K.map (adjF.counit.app N)) ≫
        (adjK.leftAdjointUniq adjK').hom.app N =
      (adjH.leftAdjointUniq adjH').hom.app (R.obj N) ≫ q' := by
  apply (adjH.homEquiv _ _).injective
  rw [adjH.homEquiv_naturality_right, sheetTranspose, hab]
  rw [Category.assoc, ← b.naturality]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← R.map_comp, Adjunction.unit_leftAdjointUniq_hom_app]
  rw [adjH.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact hq'.symm

universe u
open Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry
variable {X : Scheme.{u}} {A : Type*} [Category A]
  (G : Sheaf (Scheme.ProEt.topology X) A)
  {V : X.ProEt} {ι : Type*} (W : ι → X.ProEt) (π : ∀ i, W i ⟶ V)
private lemma Scheme.ProEt.comp_map_eq_of_disjoint [∀ i, Mono (π i)]
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base))
    {E : A} (x : ∀ i, E ⟶ G.obj.obj (op (W i))) ⦃Z : X.ProEt⦄ ⦃i j : ι⦄ (a : Z ⟶ W i)
    (b : Z ⟶ W j) (h : a ≫ π i = b ≫ π j) :
    x i ≫ G.obj.map a.op = x j ≫ G.obj.map b.op := by
  by_cases hij : i = j
  · subst hij
    obtain rfl : a = b := (cancel_mono (π i)).mp h
    rfl
  · -- the source `Z` is empty, so `G Z` is terminal
    have hZ : IsEmpty Z.left := ⟨fun z ↦ by
      have hz := congrArg (fun m ↦ m.left.base z) h
      change (a.left ≫ (π i).left) z = (b.left ≫ (π j).left) z at hz
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hz
      exact Set.disjoint_left.mp (hdisj i j hij) ⟨a.left z, rfl⟩ ⟨b.left z, hz.symm⟩⟩
    exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty G Z).hom_ext _ _

/-- **A sheaf sends a disjoint cover to a product**: if the pairwise disjoint subobjects
`π i : W i ⟶ V` cover `V` in the small pro-étale topology, then the restriction maps exhibit
`G V` as the product of the `G (W i)`. -/
private theorem Scheme.ProEt.isIso_piLift_of_disjoint [∀ i, Mono (π i)]
    (hcov : Sieve.ofArrows W π ∈ (Scheme.ProEt.topology X) V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base))
    [HasProduct fun i ↦ G.obj.obj (op (W i))] :
    IsIso (Pi.lift fun i ↦ G.obj.map (π i).op) := by
  refine isIso_of_yoneda_map_bijective _ fun E ↦ ⟨fun x y hxy ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := G.property.existsUnique_amalgamation_ofArrows π hcov
      (fun i ↦ x ≫ G.obj.map (π i).op) (Scheme.ProEt.comp_map_eq_of_disjoint G W π hdisj _)
    refine (ht x fun i ↦ rfl).trans (ht y fun i ↦ ?_).symm
    simpa using (congrArg (· ≫ Pi.π _ i) hxy).symm
  · obtain ⟨t, ht, -⟩ := G.property.existsUnique_amalgamation_ofArrows π hcov
      (fun i ↦ φ ≫ Pi.π _ i) (Scheme.ProEt.comp_map_eq_of_disjoint G W π hdisj _)
    exact ⟨t, Pi.hom_ext _ _ fun i ↦ by simpa using ht i⟩

private theorem sheetPullback
    {X U Y W : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U)
    (w : t ≫ p = g) (f : W ⟶ Y) :
    let b := pullback.lift t (𝟙 Y) (by simpa using w)
    let σ := pullback.lift (𝟙 W) (f ≫ t) (by simp [Category.assoc, w])
    let v := pullback.lift (pullback.snd (f ≫ g) p)
      (pullback.fst (f ≫ g) p ≫ f) (by simp [Category.assoc, pullback.condition])
    IsPullback σ f v b := by
  dsimp only
  let b : Y ⟶ pullback p g := pullback.lift t (𝟙 Y) (by simpa using w)
  let σ : W ⟶ pullback (f ≫ g) p :=
    pullback.lift (𝟙 W) (f ≫ t) (by simp [Category.assoc, w])
  let v : pullback (f ≫ g) p ⟶ pullback p g :=
    pullback.lift (pullback.snd (f ≫ g) p)
      (pullback.fst (f ≫ g) p ≫ f) (by simp [Category.assoc, pullback.condition])
  change IsPullback σ f v b
  have hw : σ ≫ v = f ≫ b := by
    apply pullback.hom_ext
    · simp only [v, b, Category.assoc, pullback.lift_fst, σ, pullback.lift_snd]
    · simp only [v, b, Category.assoc, pullback.lift_snd, σ, pullback.lift_fst_assoc,
        Category.comp_id]
      erw [Category.id_comp]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c ↦ c.fst ≫ pullback.fst (f ≫ g) p) ?_ ?_ ?_)
  · intro c
    apply pullback.hom_ext
    · simp [σ, Category.assoc]
    · have h₁ := congrArg (fun z ↦ z ≫ pullback.fst p g) c.condition
      simp only [v, b, Category.assoc, pullback.lift_fst] at h₁
      have h₂ := congrArg (fun z ↦ z ≫ pullback.snd p g) c.condition
      simp only [v, b, Category.assoc, pullback.lift_snd, Category.comp_id] at h₂
      simpa [σ, Category.assoc] using
        (congrArg (fun z ↦ z ≫ t) h₂).trans h₁.symm
  · intro c
    have h₂ := congrArg (fun z ↦ z ≫ pullback.snd p g) c.condition
    simpa [v, b, Category.assoc] using h₂
  · intro c m hm _
    simpa [σ, Category.assoc] using congrArg (fun z ↦ z ≫ pullback.fst (f ≫ g) p) hm
end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale
private noncomputable def sectionSheet
    {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U)
    (w : t ≫ p = g) [WeaklyEtale t] [WeaklyEtale g]
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    (localizationRestriction Ab.{u + 1} g inferInstance).obj
        ((lowerStar Ab.{u + 1} p).obj N) ⟶
      (localizationRestriction Ab.{u + 1} t inferInstance).obj N := by
  let σ (W : Y.ProEt) :
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale t)).obj W ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj W) :=
    MorphismProperty.Over.homMk
      (pullback.lift (𝟙 W.left) (W.hom ≫ t) (by
        change (𝟙 W.left) ≫ W.hom ≫ g = (W.hom ≫ t) ≫ p
        simp only [Category.assoc, Category.id_comp, w])) (by simp)
  refine ⟨{app := fun W ↦ N.obj.map (σ W.unop).op, naturality := ?_}⟩
  intro W W' h
  change N.obj.map _ ≫ N.obj.map _ = N.obj.map _ ≫ N.obj.map _
  rw [← N.obj.map_comp, ← N.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  dsimp [σ]
  apply pullback.hom_ext
  · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.homMk_hom,
      Over.homMk_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.map_map_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
    change 𝟙 _ ≫ h.unop.left = h.unop.left ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.map, Category.assoc]

private theorem sectionSheet_transpose
    {X U Y : Scheme.{u}} (p : U ⟶ X) (t : Y ⟶ U)
    [WeaklyEtale t] [WeaklyEtale (t ≫ p)]
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} (t ≫ p) inferInstance).homEquiv
        _ _ (sectionSheet p (t ≫ p) t rfl N) =
      (lowerStar Ab.{u + 1} p).map
        ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} t inferInstance).unit.app N) ≫
      (lowerStarComp Ab.{u + 1} t p).hom.app
        ((localizationRestriction Ab.{u + 1} t inferInstance).obj N) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext ⟨V⟩
  simp only [Adjunction.homEquiv_unit, localizationRestrictionLowerStarAdjunction,
    Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft_unit_app_app,
    Adjunction.op_unit_app, MorphismProperty.Over.mapPullbackAdj_counit_app,
    sectionSheet, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.id_obj, Functor.op_obj, lowerStar_map_hom_app]
  rw [lowerStarComp_hom_app_hom_app]
  change N.obj.map _ ≫ N.obj.map _ = N.obj.map _ ≫ N.obj.map _
  rw [← N.obj.map_comp, ← N.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  dsimp
  apply pullback.hom_ext
  · simp only [MorphismProperty.Over.map, MorphismProperty.Over.pullback,
      Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.mk_hom,
      MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left,
      MorphismProperty.Over.pullbackComp, Functor.comp_obj, NatIso.ofComponents_hom_app,
      MorphismProperty.Comma.mapRight_map_left, MorphismProperty.Over.isoMk_hom_left,
      Iso.trans_hom, pullback.congrHom_hom, pullback.map_id, Iso.symm_hom]
    erw [Category.id_comp, Category.id_comp, pullbackLeftPullbackSndIso_inv_fst]
  · simp only [MorphismProperty.Over.map, MorphismProperty.Over.pullback,
      Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.mk_hom,
      MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, MorphismProperty.Over.pullbackComp, Functor.comp_obj,
      NatIso.ofComponents_hom_app, MorphismProperty.Comma.mapRight_map_left,
      MorphismProperty.Over.isoMk_hom_left, Iso.trans_hom, pullback.congrHom_hom,
      pullback.map_id, Iso.symm_hom]
    erw [Category.id_comp, pullbackLeftPullbackSndIso_inv_fst_snd]

private theorem canonicalSheet_is_restriction
    {X U Y : Scheme.{u}} (p : U ⟶ X) (t : Y ⟶ U)
    [WeaklyEtale t] [WeaklyEtale (t ≫ p)]
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    (upperStarComp Ab.{u + 1} t p).hom.app ((lowerStar Ab.{u + 1} p).obj N) ≫
        (upperStar Ab.{u + 1} t).map
          ((upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N) ≫
        (upperStarIsoLocalizationRestriction Ab.{u + 1} t inferInstance).hom.app N =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (t ≫ p) inferInstance).hom.app
          ((lowerStar Ab.{u + 1} p).obj N) ≫ sectionSheet p (t ≫ p) t rfl N := by
  exact sheetNormalized (upperStarLowerStarAdjunction Ab.{u + 1} p)
    (upperStarLowerStarAdjunction Ab.{u + 1} t)
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} t inferInstance)
    (upperStarLowerStarAdjunction Ab.{u + 1} (t ≫ p))
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} (t ≫ p) inferInstance)
    (upperStarComp Ab.{u + 1} t p).hom (lowerStarComp Ab.{u + 1} t p).hom
    (conjugateEquiv_upperStarComp_hom Ab.{u + 1} t p) N (sectionSheet p (t ≫ p) t rfl N)
    (sectionSheet_transpose p t N)

private theorem canonicalSheet_is_restriction_of_comm
    {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U)
    (w : t ≫ p = g) [WeaklyEtale t] [WeaklyEtale g]
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    ((eqToIso (congrArg (upperStar Ab.{u + 1}) w)).symm ≪≫
        upperStarComp Ab.{u + 1} t p).hom.app ((lowerStar Ab.{u + 1} p).obj N) ≫
        (upperStar Ab.{u + 1} t).map
          ((upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N) ≫
        (upperStarIsoLocalizationRestriction Ab.{u + 1} t inferInstance).hom.app N =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom.app
          ((lowerStar Ab.{u + 1} p).obj N) ≫ sectionSheet p g t w N := by
  subst g
  simpa only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans] using
    canonicalSheet_is_restriction p t N

private theorem splitSections_limit
    {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X) [WeaklyEtale g]
    (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    [∀ j, WeaklyEtale (t j)]
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (W : Y.ProEt) :
    Nonempty (IsLimit (Fan.mk
      (((localizationRestriction Ab.{u + 1} g inferInstance).obj
        ((lowerStar Ab.{u + 1} p).obj N)).obj.obj (op W))
      (fun j ↦ (sectionSheet p g (t j) (w j) N).hom.app (op W)))) := by
  classical
  let b (j : Fin n) : Y ⟶ pullback p g :=
    pullback.lift (t j) (𝟙 Y) (by simpa using w j)
  let e : (∐ (fun _ : Fin n ↦ Y)) ≅ pullback p g :=
    colimit.isoColimitCocone ⟨Cofan.mk _ b, hc.some⟩
  have hb (j : Fin n) : Sigma.ι (fun _ : Fin n ↦ Y) j ≫ e.hom = b j :=
    colimit.isoColimitCocone_ι_hom ⟨Cofan.mk _ b, hc.some⟩ ⟨j⟩
  have hop (j : Fin n) : IsOpenImmersion (b j) := by
    rw [← hb j]
    infer_instance
  let B := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj
    ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj W)
  let A (j : Fin n) :=
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (t j))).obj W
  let σ (j : Fin n) : A j ⟶ B := MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ t j) (by
      change (𝟙 W.left) ≫ W.hom ≫ g = (W.hom ≫ t j) ≫ p
      simp only [Category.assoc, Category.id_comp, w j])) (by
        change pullback.lift _ _ _ ≫ pullback.snd (W.hom ≫ g) p = W.hom ≫ t j
        exact pullback.lift_snd _ _ _)
  let v : B.left ⟶ pullback p g :=
    pullback.lift (pullback.snd (W.hom ≫ g) p)
      (pullback.fst (W.hom ≫ g) p ≫ W.hom)
        (by simp [Category.assoc, pullback.condition])
  have hpb (j : Fin n) : IsPullback (σ j).left W.hom v (b j) :=
    sheetPullback p g (t j) (w j) W.hom
  have hr (j : Fin n) : Set.range (σ j).left = v ⁻¹' Set.range (b j) :=
    Scheme.range_snd_of_isPullback (hpb j).flip
  have : ∀ j, Mono (σ j) := fun j ↦ by
    let _ := hop j
    have : IsOpenImmersion (σ j).left := (hpb j).isOpenImmersion_fst
    exact (MorphismProperty.Over.forget @WeaklyEtale ⊤ U ⋙ Over.forget U).mono_of_mono_map
      (by change Mono (σ j).left; infer_instance)
  have hy (z : (pullback p g : Scheme.{u})) : ∃ j, z ∈ Set.range (b j) := by
    obtain ⟨z', hz⟩ := (Scheme.homeoOfIso e).surjective z
    obtain ⟨k, y, hk⟩ := (sigmaOpenCover (fun _ : Fin n ↦ Y)).exists_eq z'
    change (Sigma.ι (fun _ : Fin n ↦ Y) k) y = z' at hk
    refine ⟨k, y, ?_⟩
    rw [← hb k, Scheme.Hom.comp_apply, hk]
    exact hz
  have hd (j k : Fin n) (hjk : j ≠ k) : Disjoint (Set.range (b j)) (Set.range (b k)) := by
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have heq : Sigma.ι (fun _ : Fin n ↦ Y) j x = Sigma.ι (fun _ : Fin n ↦ Y) k y :=
      (Scheme.homeoOfIso e).injective (by
        simpa only [Scheme.coe_homeoOfIso, ← Scheme.Hom.comp_apply, hb] using hxy)
    exact hjk (Sigma.mk.inj_iff.mp ((sigmaι_eq_iff (fun _ : Fin n ↦ Y) j k x y).mp heq)).1
  have hcov : Sieve.ofArrows A σ ∈ Scheme.ProEt.topology U B := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    constructor
    · intro z
      obtain ⟨j, hj⟩ := hy (v z)
      exact ⟨j, (hr j).symm ▸ hj⟩
    · intro j
      let _ := hop j
      exact (hpb j).isOpenImmersion_fst
  have hdisj (j k : Fin n) (hjk : j ≠ k) :
      Disjoint (Set.range (σ j).left.base) (Set.range (σ k).left.base) := by
    rw [hr j, hr k]
    exact (hd j k hjk).preimage v
  change Nonempty (IsLimit (Fan.mk (N.obj.obj (op B))
    (fun j ↦ N.obj.map (σ j).op)))
  exact (Fan.nonempty_isLimit_iff_isIso_piLift _).mpr
    (Scheme.ProEt.isIso_piLift_of_disjoint N A σ hcov hdisj)

private theorem sectionProduct_isIso
    {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X) [WeaklyEtale g]
    (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    [∀ j, WeaklyEtale (t j)]
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    IsIso (Pi.lift (fun j ↦ sectionSheet p g (t j) (w j) N)) := by
  let c := Fan.mk
    ((localizationRestriction Ab.{u + 1} g inferInstance).obj
      ((lowerStar Ab.{u + 1} p).obj N)) (fun j ↦ sectionSheet p g (t j) (w j) N)
  have hl : IsLimit c := by
    apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    apply (Fan.isLimitMapConeEquiv
      (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) _ c).2
    apply evaluationJointlyReflectsLimits
    intro W
    apply (Fan.isLimitMapConeEquiv
      ((evaluation Y.ProEtᵒᵖ Ab.{u + 1}).obj W) _ _).2
    exact (splitSections_limit p g n t w hc N W.unop).some
  exact (Fan.nonempty_isLimit_iff_isIso_piLift c).mp ⟨hl⟩

/-- The counit maps to the sheets of a split finite cover form an isomorphism.

Source: Stacks Project, Tag 095B, proof by sections over a split finite cover; the
weakly etale base-change argument for the pro-etale site.
(auxiliary; not a blueprint node)

Proof in words. Compute inverse image along the weakly etale map g by restriction
along the localization functor of pro-etale sites. For a test W over Y, the assumed
coproduct decomposition, after base change to W, decomposes W times_X U into n
open-and-closed copies of W. The counit on the j-th sheet is the restriction to
that copy. The sheaf condition identifies sections on their disjoint union with
the finite product of their sections: distinct overlaps are empty, and on a
self-overlap the two restrictions agree. This also proves the empty case.
The comparison is the canonical one: its components are inverse-image
composition followed by the pushforward counit. Under the identification of
weakly etale inverse image with restriction, these components are exactly the
restriction maps to the sheet copies. Products and isomorphisms of sheaves are
tested on sections, giving the assertion. -/
theorem splitProEtaleAbelianProductMap_isIso
    {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) [WeaklyEtale g]
    (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (N : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    let a := fun j ↦ (eqToIso (congrArg (upperStar Ab.{u + 1}) (w j))).symm ≪≫
      upperStarComp Ab.{u + 1} (t j) p
    IsIso (Pi.lift (fun j ↦
      (a j).hom.app ((lowerStar Ab.{u + 1} p).obj N) ≫
        (upperStar Ab.{u + 1} (t j)).map
          ((upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N))) := by
  classical
  let b (j : Fin n) : Y ⟶ pullback p g :=
    pullback.lift (t j) (𝟙 Y) (by simpa using w j)
  let e : (∐ (fun _ : Fin n ↦ Y)) ≅ pullback p g :=
    colimit.isoColimitCocone ⟨Cofan.mk _ b, hc.some⟩
  have hb (j : Fin n) : Sigma.ι (fun _ : Fin n ↦ Y) j ≫ e.hom = b j :=
    colimit.isoColimitCocone_ι_hom ⟨Cofan.mk _ b, hc.some⟩ ⟨j⟩
  have ht (j : Fin n) : WeaklyEtale (t j) := by
    have : IsOpenImmersion (b j) := by rw [← hb j]; infer_instance
    have : WeaklyEtale (b j ≫ pullback.fst p g) := inferInstance
    simpa only [b, pullback.lift_fst] using this
  let _ := ht
  let q := Pi.lift (fun j ↦
    ((eqToIso (congrArg (upperStar Ab.{u + 1}) (w j))).symm ≪≫
      upperStarComp Ab.{u + 1} (t j) p).hom.app ((lowerStar Ab.{u + 1} p).obj N) ≫
    (upperStar Ab.{u + 1} (t j)).map
      ((upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N))
  let q' := Pi.lift (fun j ↦ sectionSheet p g (t j) (w j) N)
  have : IsIso q' := sectionProduct_isIso p g n t w hc N
  let d := Pi.mapIso (fun j ↦
    (upperStarIsoLocalizationRestriction Ab.{u + 1} (t j) inferInstance).app N)
  have hq : q ≫ d.hom =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).hom.app
        ((lowerStar Ab.{u + 1} p).obj N) ≫ q' := by
    apply Pi.hom_ext
    intro j
    simp only [d, Category.assoc, Pi.mapIso_hom_π]
    dsimp only [q, q']
    erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    simpa only [Iso.app_hom, Category.assoc] using
      canonicalSheet_is_restriction_of_comm p g (t j) (w j) N
  have : IsIso (q ≫ d.hom) := hq.symm ▸ inferInstance
  have : IsIso q := by
    have h : q = (q ≫ d.hom) ≫ d.inv := by simp
    rw [h]
    infer_instance
  exact this

end AlgebraicGeometry.ProEtale
