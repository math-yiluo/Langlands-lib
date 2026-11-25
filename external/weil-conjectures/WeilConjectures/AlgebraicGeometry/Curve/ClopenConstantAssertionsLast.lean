/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.FiniteCoproductCohomologyAssembly
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve

private noncomputable def cohomologyEquiv {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    Sheaf.H F q ≃ Sheaf.H G q where
  toFun := Sheaf.H.map e.hom q
  invFun := Sheaf.H.map e.inv q
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id]; simp
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id]; simp

private theorem comparison_conjugate {X Y : Scheme.{u}} (a : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    Etale.cohomologyMap a G q =
      cohomologyEquiv ((Etale.upperStar _ a).mapIso e) q ∘
        Etale.cohomologyMap a F q ∘ (cohomologyEquiv e q).symm := by
  funext x
  change Etale.cohomologyMap a G q x =
    Sheaf.H.map ((Etale.upperStar _ a).map e.hom) q
      (Etale.cohomologyMap a F q (Sheaf.H.map e.inv q x))
  rw [← Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply, e.inv_hom_id]
  simp

private theorem opens_coproduct {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) :
    Nonempty (IsColimit (Cofan.mk X (fun i ↦ (U i).ι))) := by
  apply nonempty_isColimit_cofanMk_of
  · apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := hcov x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨i, by simpa using hi⟩
  · intro i j hij
    simpa only [Function.onFun_apply, Scheme.Opens.opensRange_ι] using
      TopologicalSpace.Opens.coe_disjoint.mp (hdisj hij)

private noncomputable def underlyingConstantIso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) (M : ModuleCat.{u + 1} Λ) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
  have : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology _
  exact (constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app M

private noncomputable def restrictedConstantIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (a : Y ⟶ X)
    (M : ModuleCat.{u + 1} Λ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} a).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (Etale.upperStar _ a).mapIso (underlyingConstantIso Λ X M) ≪≫
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} a).app
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M) ≪≫
    (underlyingConstantIso Λ Y M).symm

private theorem pullback_coproduct {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} (U : ι → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) :
    Nonempty (IsColimit (Cofan.mk Y (fun i ↦ pullback.fst g (U i).ι))) := by
  apply nonempty_isColimit_cofanMk_of
  · apply top_unique
    intro y hy
    apply TopologicalSpace.Opens.mem_iSup.mpr
    change ∃ i, y ∈ Set.range (pullback.fst g (U i).ι)
    obtain ⟨i, hi⟩ := hcov (g y)
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hi
  · intro i j hij
    suffices h : Disjoint (Set.range (pullback.fst g (U i).ι))
        (Set.range (pullback.fst g (U j).ι)) by
      exact TopologicalSpace.Opens.coe_disjoint.mp h
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst,
      Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact (hdisj hij).preimage g

private theorem comparison_congr {X Y : Scheme.{u}} {a b : Y ⟶ X} (h : a = b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H F q) :
    Sheaf.H.map (eqToHom (congrArg
      (fun m ↦ (Etale.upperStar AddCommGrpCat.{u + 1} m).obj F) h)) q
      (Etale.cohomologyMap a F q x) = Etale.cohomologyMap b F q x := by
  subst h
  simp

private theorem comparison_surjective_components {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (H : ∀ i, Function.Surjective (Etale.cohomologyMap (pullback.snd g (U i).ι)
      ((Etale.upperStar _ (U i).ι).obj F) q)) :
    Function.Surjective (Etale.cohomologyMap g F q) := by
  classical
  let C := fun i ↦ (U i).toScheme
  let D := fun i ↦ pullback g (U i).ι
  let b := fun i ↦ (U i).ι
  let d := fun i ↦ pullback.fst g (U i).ι
  let a := fun i ↦ pullback.snd g (U i).ι
  obtain ⟨hc⟩ := opens_coproduct U hdisj hcov
  obtain ⟨hd⟩ := pullback_coproduct g U hdisj hcov
  have hx := Etale.finiteCoproductCohomologyAssembly C X b hc F q
  have hy := Etale.finiteCoproductCohomologyAssembly D Y d hd
    ((Etale.upperStar _ g).obj F) q
  let e (i : ι) : (Etale.upperStar _ (a i)).obj ((Etale.upperStar _ (b i)).obj F) ≅
      (Etale.upperStar _ (d i)).obj ((Etale.upperStar _ g).obj F) :=
    ((Etale.upperStarComp _ (a i) (b i)).app F).symm ≪≫
      eqToIso (congrArg (fun m ↦ (Etale.upperStar AddCommGrpCat.{u + 1} m).obj F)
        (pullback.condition (f := g) (g := (U i).ι)).symm) ≪≫
      (Etale.upperStarComp _ (d i) g).app F
  have he (i : ι) (x : Sheaf.H F q) :
      cohomologyEquiv (e i) q
        (Etale.cohomologyMap (a i) _ q (Etale.cohomologyMap (b i) F q x)) =
      Etale.cohomologyMap (d i) _ q (Etale.cohomologyMap g F q x) := by
    rw [(Etale.cohomologyPullbackFunctorial (a i) (b i) F q).2.1]
    change Sheaf.H.map (e i).hom q (Sheaf.H.map _ q _) = _
    rw [← Sheaf.H.map_comp_apply]
    dsimp [e]
    rw [Iso.hom_inv_id_app_assoc, Sheaf.H.map_comp_apply]
    rw [comparison_congr (pullback.condition (f := g) (g := (U i).ι)).symm]
    exact ((Etale.cohomologyPullbackFunctorial (d i) g F q).2.1 x).symm
  intro y
  choose z hz using fun i ↦ H i ((cohomologyEquiv (e i) q).symm
    (Etale.cohomologyMap (d i) _ q y))
  obtain ⟨x, hx⟩ := hx.2 z
  refine ⟨x, hy.1 (funext fun i ↦ ?_)⟩
  dsimp only
  rw [← he]
  change cohomologyEquiv (e i) q
    (Etale.cohomologyMap (a i) _ q ((Etale.cohomologyMap (b i) F q) x)) = _
  have hxi : Etale.cohomologyMap (b i) F q x = z i := congrFun hx i
  rw [hxi, hz]
  exact (cohomologyEquiv (e i) q).apply_symm_apply _

private theorem comparison_bijective_components {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (H : ∀ i, Function.Bijective (Etale.cohomologyMap (pullback.snd g (U i).ι)
      ((Etale.upperStar _ (U i).ι).obj F) q)) :
    Function.Bijective (Etale.cohomologyMap g F q) := by
  refine ⟨?_, comparison_surjective_components g U hdisj hcov F q (fun i ↦ (H i).2)⟩
  obtain ⟨hc⟩ := opens_coproduct U hdisj hcov
  intro x y hxy
  apply (Etale.finiteCoproductCohomologyAssembly (fun i ↦ (U i).toScheme) X
    (fun i ↦ (U i).ι) hc F q).1
  funext i
  apply (H i).1
  rw [(Etale.cohomologyPullbackFunctorial (pullback.snd g (U i).ι) (U i).ι F q).2.1,
    (Etale.cohomologyPullbackFunctorial (pullback.snd g (U i).ι) (U i).ι F q).2.1]
  apply congrArg (Sheaf.H.map _ q)
  rw [← pullback.condition]
  apply (Etale.injective_sheafHMap_of_isIso
    ((Etale.upperStarComp _ (pullback.fst g (U i).ι) g).hom.app F) q)
  rw [← (Etale.cohomologyPullbackFunctorial (pullback.fst g (U i).ι) g F q).2.1,
    ← (Etale.cohomologyPullbackFunctorial (pullback.fst g (U i).ι) g F q).2.1, hxy]

private theorem invertibleOrder_of_iso
    {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S G := by
  constructor
  intro Ω _ _ t x
  let es := ((Scheme.pointSmallEtale t).sheafFiber.mapIso e).toLinearEquiv
  obtain ⟨n, hn, hu, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω t (es.symm x)
  exact ⟨n, hn, hu, es.symm.injective (by simpa only [map_nsmul, map_zero] using hx)⟩

private theorem invertibleOrder_upperStar
    {Λ : Type (u + 1)} [CommRing Λ] {X Y S : Scheme.{u}} (a : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S ((Etale.upperStar _ a).obj F) := by
  constructor
  intro Ω _ _ t x
  let e := ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) a t).app F).toLinearEquiv
  obtain ⟨n, hn, hu, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω (t ≫ a) (e x)
  exact ⟨n, hn, hu, e.injective (by simpa only [map_nsmul, map_zero] using hx)⟩

/-- The last four curve assertions transfer across a finite clopen partition.
Source: the finite disjoint-union argument in the proof of the clopen constant
assertions lemma. Properness, base-change bijectivity, and restriction
surjectivity are all componentwise and hence pass to finite products.
(blueprint: lem-pbc-k2-clopen-constant-assertions-last)
-/
theorem clopen_last_four (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (M : ModuleCat.{u + 1} Λ)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (H : ∀ i, Assertions Λ ((U i).ι ≫ f)
      ((constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    FiniteOfIsProper Λ
      f ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    BaseChangeOfInvertibleOrder Λ
      f ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    BaseChangeOfIsProper Λ
      f ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    SurjectiveRestrictionTwo Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let A := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let Fi := fun i ↦
    (constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let ei := fun i ↦ (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (U i).ι).app M
  have hi (i : ι) : IsClosedImmersion (U i).ι :=
    .of_isOpenImmersion _ (by simpa using hU i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ q
    have hfin (i : ι) : Finite (Sheaf.H ((Etale.upperStar _ (U i).ι).obj A) q) := by
      let : IsProper (U i).ι := inferInstance
      let : IsProper ((U i).ι ≫ f) := inferInstance
      let : Scheme.IsConstructibleSheaf ((Etale.upperStar _ (U i).ι).obj F) :=
        Scheme.IsConstructibleSheaf.upperStar _ _
      let : Scheme.IsConstructibleSheaf (Fi i) :=
        Scheme.IsConstructibleSheaf.of_iso
          (F := (Etale.upperStar _ (U i).ι).obj F) (ei i)
      let : Finite (Sheaf.H
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            (Fi i)) q) := (H i).finite_of_isProper q
      exact Finite.of_injective _ (cohomologyEquiv
        (restrictedConstantIso Λ (U i).ι M) q).injective
    let (i : ι) : Finite (Sheaf.H ((Etale.upperStar _ (U i).ι).obj A) q) := hfin i
    obtain ⟨hc⟩ := opens_coproduct U hdisj hcov
    exact Finite.of_injective _
      (Etale.finiteCoproductCohomologyAssembly (fun i ↦ (U i).toScheme) X
        (fun i ↦ (U i).ι) hc A q).1
  · intro _ k' _ _ X' ι f' ι' hp q
    apply comparison_bijective_components ι' U hdisj hcov A q
    intro i
    let : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k))
        ((Etale.upperStar _ (U i).ι).obj F) := invertibleOrder_upperStar (U i).ι F
    let : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (Fi i) :=
      invertibleOrder_of_iso
        (F := (Etale.upperStar _ (U i).ι).obj F) (ei i)
    have hpi : IsPullback (pullback.snd ι' (U i).ι)
        (pullback.fst ι' (U i).ι ≫ f') ((U i).ι ≫ f) ι :=
      (IsPullback.of_hasPullback ι' (U i).ι).flip.paste_vert hp
    rw [comparison_conjugate _ (restrictedConstantIso Λ (U i).ι M).symm q]
    exact (cohomologyEquiv _ q).bijective.comp
      (((H i).bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' hpi q).comp
        (cohomologyEquiv _ q).symm.bijective)
  · intro _ k' _ _ X' ι f' ι' hp q
    apply comparison_bijective_components ι' U hdisj hcov A q
    intro i
    let : IsProper (U i).ι := inferInstance
    let : IsProper ((U i).ι ≫ f) := inferInstance
    have hpi : IsPullback (pullback.snd ι' (U i).ι)
        (pullback.fst ι' (U i).ι ≫ f') ((U i).ι ≫ f) ι :=
      (IsPullback.of_hasPullback ι' (U i).ι).flip.paste_vert hp
    rw [comparison_conjugate _ (restrictedConstantIso Λ (U i).ι M).symm q]
    exact (cohomologyEquiv _ q).bijective.comp
      (((H i).bijective_cohomologyMap_of_isProper k' hpi q).comp
        (cohomologyEquiv _ q).symm.bijective)
  · intro W a _
    apply comparison_surjective_components a U hdisj hcov A 2
    intro i
    rw [comparison_conjugate _ (restrictedConstantIso Λ (U i).ι M).symm 2]
    exact (cohomologyEquiv _ 2).surjective.comp
      (((H i).surjective_cohomologyMap_of_isOpenImmersion (pullback.snd a (U i).ι)).comp
        (cohomologyEquiv _ 2).symm.surjective)
end AlgebraicGeometry.IsCurve
