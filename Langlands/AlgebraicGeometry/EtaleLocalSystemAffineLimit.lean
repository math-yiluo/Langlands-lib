import Langlands.AlgebraicGeometry.EtaleLocalSystemIsoDescent
import Langlands.AlgebraicGeometry.LocallyConstantAffineLimit
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLimits

/-! # Spreading a local-system trivialization along an affine inverse limit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

open EtaleEquivalenceRelation.Action

set_option backward.isDefEq.respectTransparency false

variable {S T U X Y : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}}

/-- A finitely generated local system on an affine scheme has a finite affine trivializing cover. -/
private theorem exists_finite_affine_cover [IsAffine S]
    (hF : IsFinitelyGeneratedLocallyConstant.{u, u} F) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S, Finite 𝒰.I₀ ∧
      (∀ i, IsAffine (𝒰.X i)) ∧ ∀ i, ∃ N : AddCommGrpCat.{u}, AddGroup.FG N ∧
        Nonempty (restrict (𝒰.f i) F ≅ constant (𝒰.X i) N) := by
  classical
  obtain ⟨_, 𝒱, h𝒱⟩ := hF
  let A (i : 𝒱.I₀) : Scheme.Cover.{u} (Scheme.precoverage @Etale) (𝒱.X i) :=
    (𝒱.X i).affineCover.changeProp (fun _ => inferInstance)
  let B : Scheme.Cover.{u} (Scheme.precoverage @Etale) S := 𝒱.bind A
  have hB (i : B.I₀) : IsAffine (B.X i) := by
    change IsAffine ((𝒱.X i.1).affineCover.X i.2)
    infer_instance
  have htriv (i : B.I₀) : ∃ N : AddCommGrpCat.{u}, AddGroup.FG N ∧
      Nonempty (restrict (B.f i) F ≅ constant (B.X i) N) := by
    obtain ⟨N, hN, ⟨e⟩⟩ := h𝒱 i.1
    exact ⟨N, hN, ⟨pullIso (G := constant S N) e ((A i.1).f i.2) rfl⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i => Set.range (B.f i))
    (fun i => (B.f i).isOpenMap.isOpen_range) (by rw [B.iUnion_range])
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers s (fun i => B.X i) (fun i => B.f i) (fun x => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
      obtain ⟨his, hx⟩ := Set.mem_iUnion.mp hi
      obtain ⟨y, hy⟩ := hx
      exact ⟨⟨i, his⟩, y, hy⟩) (fun i => inferInstance)
  exact ⟨𝒰, inferInstanceAs (Finite s), fun i => hB i.1, fun i => htriv i.1⟩

/-- The structure morphism of a base-changed chart. -/
private abbrev chartBase (p : T ⟶ S) (q : U ⟶ S) : pullback p q ⟶ S :=
  pullback.snd p q ≫ q

private abbrev ChartModel (p : T ⟶ S) (q : U ⟶ S)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) (M : AddCommGrpCat.{u}) :=
  restrict (chartBase p q) F ≅ constant (pullback p q) M

/-- Base change of a morphism between charts over the fixed base. -/
private abbrev chartMap (p : T ⟶ S) {q : U ⟶ S} {q' : Y ⟶ S}
    (b : U ⟶ Y) (hb : b ≫ q' = q) : pullback p q ⟶ pullback p q' :=
  pullback.map p q p q' (𝟙 T) b (𝟙 S) (by simp) (by simp [hb])

@[reassoc (attr := simp)]
private theorem chartMap_base (p : T ⟶ S) {q : U ⟶ S} {q' : Y ⟶ S}
    (b : U ⟶ Y) (hb : b ≫ q' = q) :
    chartMap p b hb ≫ chartBase p q' = chartBase p q := by
  simp [hb]

section ChartLimits

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p) (q : U ⟶ S)

private abbrev chartCone : Cone (TargetLimit.diagram D t q) :=
  TargetLimit.coneOfPullback D t q c p hp (IsPullback.of_hasPullback p q)

@[reassoc (attr := simp)]
private theorem chartCone_fst (i : I) :
    (chartCone D t c p hp q).π.app i ≫ pullback.fst (t.app i) q =
      pullback.fst p q ≫ c.π.app i :=
  TargetLimit.coneOfPullback_π_fst _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
private theorem chartCone_snd (i : I) :
    (chartCone D t c p hp q).π.app i ≫ pullback.snd (t.app i) q =
      pullback.snd p q :=
  TargetLimit.coneOfPullback_π_snd _ _ _ _ _ _ _ _

@[reassoc (attr := simp)]
private theorem chartDiagram_map_fst {i j : I} (r : i ⟶ j) :
    (TargetLimit.diagram D t q).map r ≫ pullback.fst (t.app j) q =
      pullback.fst (t.app i) q ≫ D.map r :=
  (TargetLimit.projection D t q).naturality r

@[reassoc (attr := simp)]
private theorem chartDiagram_map_snd {i j : I} (r : i ⟶ j) :
    (TargetLimit.diagram D t q).map r ≫ pullback.snd (t.app j) q =
      pullback.snd (t.app i) q := by
  have h := (TargetLimit.comparison D t q).naturality r
  change (TargetLimit.diagram D t q).map r ≫ pullback.snd (t.app j) q =
    pullback.snd (t.app i) q ≫ 𝟙 U at h
  rw [Category.comp_id] at h
  exact h

private theorem chartCone_base (i : I) :
    (chartCone D t c p hp q).π.app i ≫ chartBase (t.app i) q = chartBase p q := by
  rw [chartBase, chartBase, chartCone_snd_assoc]

private theorem chartDiagram_map_base {i j : I} (r : i ⟶ j) :
    (TargetLimit.diagram D t q).map r ≫ chartBase (t.app j) q =
      chartBase (t.app i) q := by
  rw [chartBase, chartBase, chartDiagram_map_snd_assoc]

private theorem chartCone_naturality {q' : Y ⟶ S}
    (b : U ⟶ Y) (hb : b ≫ q' = q) (i : I) :
    (chartCone D t c p hp q).π.app i ≫ chartMap (t.app i) b hb =
      chartMap p b hb ≫ (chartCone D t c p hp q').π.app i := by
  apply pullback.hom_ext <;> simp

private theorem chartDiagram_naturality {q' : Y ⟶ S}
    (b : U ⟶ Y) (hb : b ≫ q' = q) {i j : I} (r : i ⟶ j) :
    (TargetLimit.diagram D t q).map r ≫ chartMap (t.app j) b hb =
      chartMap (t.app i) b hb ≫ (TargetLimit.diagram D t q').map r := by
  apply pullback.hom_ext <;> simp

end ChartLimits

/-- The trivialization pulled to a chart is the old model composed with the pulled back
locally constant comparison of the two models. -/
private theorem pullIso_eq_compare {f : T ⟶ S} {g : U ⟶ S}
    {M N : AddCommGrpCat.{u}} [AddGroup.FG N]
    (a : restrict f F ≅ constant T N) (e : restrict f F ≅ constant T M)
    (r : U ⟶ T) (hr : r ≫ f = g) :
    pullIso (G := constant S M) e r hr =
      pullIso (G := constant S N) a r hr ≪≫
        constantIsoOfValues ((constantIsoValues (a.symm ≪≫ e)).comap ⟨r, r.continuous⟩) := by
  rw [← pullIso_constantIsoOfValues (f := f) (g := g) _ r hr,
    constantIsoOfValues_constantIsoValues]
  rw [pullIso_trans, pullIso_symm, Iso.self_symm_id_assoc]

private theorem pullIso_eq_iff {f : T ⟶ S} {g : U ⟶ S}
    {M N : AddCommGrpCat.{u}} [AddGroup.FG N]
    (a : restrict f F ≅ constant T N) (e e' : restrict f F ≅ constant T M)
    (r : U ⟶ T) (hr : r ≫ f = g) :
    pullIso (G := constant S M) e r hr = pullIso (G := constant S M) e' r hr ↔
      ∀ x : U, constantIsoValues (a.symm ≪≫ e) (r x) =
        constantIsoValues (a.symm ≪≫ e') (r x) := by
  rw [pullIso_eq_compare a e, pullIso_eq_compare a e']
  constructor
  · intro h x
    have h' := congrArg (fun z => constantIsoValues
      ((pullIso (G := constant S N) a r hr).symm ≪≫ z) x) h
    simp only [Iso.symm_self_id_assoc, constantIsoValues_constantIsoOfValues] at h'
    exact h'
  · intro h
    congr 2
    exact LocallyConstant.ext h

private abbrev overlapBase (q : U ⟶ S) (q' : Y ⟶ S) : pullback q q' ⟶ S :=
  pullback.fst q q' ≫ q

private def coverOverlapMap (p : T ⟶ S) (q : U ⟶ S) (q' : Y ⟶ S) :
    pullback (pullback.fst p q) (pullback.fst p q') ⟶ pullback p (overlapBase q q') := by
  let a := pullback.fst (pullback.fst p q) (pullback.fst p q')
  let b := pullback.snd (pullback.fst p q) (pullback.fst p q')
  let l := pullback.lift (a ≫ pullback.snd p q) (b ≫ pullback.snd p q') (by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    rw [show a ≫ pullback.fst p q = b ≫ pullback.fst p q' from pullback.condition]
    rw [Category.assoc, pullback.condition, Category.assoc])
  refine pullback.lift (a ≫ pullback.fst p q) l ?_
  calc
    (a ≫ pullback.fst p q) ≫ p = (a ≫ pullback.snd p q) ≫ q := by
      simp only [Category.assoc, pullback.condition (f := p) (g := q)]
    _ = l ≫ overlapBase q q' := by
      dsimp only [l, overlapBase]
      rw [pullback.lift_fst_assoc]

@[reassoc (attr := simp)]
private theorem coverOverlapMap_fst (p : T ⟶ S) (q : U ⟶ S) (q' : Y ⟶ S) :
    coverOverlapMap p q q' ≫ chartMap p (pullback.fst q q') rfl =
      pullback.fst (pullback.fst p q) (pullback.fst p q') := by
  apply pullback.hom_ext <;> simp [coverOverlapMap]

@[reassoc (attr := simp)]
private theorem coverOverlapMap_snd (p : T ⟶ S) (q : U ⟶ S) (q' : Y ⟶ S) :
    coverOverlapMap p q q' ≫ chartMap p (pullback.snd q q') pullback.condition.symm =
      pullback.snd (pullback.fst p q) (pullback.fst p q') := by
  apply pullback.hom_ext <;> simp [coverOverlapMap, pullback.condition]

private theorem glue_chart_models (p : T ⟶ S)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {M : AddCommGrpCat.{u}} (m : ∀ a, ChartModel p (𝒰.f a) F M)
    (hF : IsEtaleSheaf F)
    (h : ∀ a b,
      pullIso (G := constant S M) (m a) (chartMap p (pullback.fst (𝒰.f a) (𝒰.f b)) rfl)
          (chartMap_base p _ rfl) =
        pullIso (G := constant S M) (m b)
          (chartMap p (pullback.snd (𝒰.f a) (𝒰.f b)) pullback.condition.symm)
          (chartMap_base p _ pullback.condition.symm)) :
    Nonempty (restrict p F ≅ constant T M) := by
  let 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T := 𝒰.pullback₁ p
  let n (a : 𝒱.I₀) : restrict (𝒱.f a ≫ p) F ≅ restrict (𝒱.f a ≫ p) (constant S M) :=
    pullIso (G := constant S M) (m a) (𝟙 _) (Category.id_comp _ |>.trans pullback.condition.symm)
  refine nonempty_iso_of_cover p 𝒱 n hF (isEtaleSheaf_constant S M) (fun a b => ?_)
  let q := 𝒰.f a
  let q' := 𝒰.f b
  have ha : coverOverlapMap p q q' ≫ chartBase p (overlapBase q q') =
      pullback.fst (𝒱.f a) (𝒱.f b) ≫ 𝒱.f a ≫ p := by
    change coverOverlapMap p q q' ≫ chartBase p (overlapBase q q') =
      pullback.fst (pullback.fst p q) (pullback.fst p q') ≫ pullback.fst p q ≫ p
    rw [← chartMap_base p (pullback.fst q q') (q := overlapBase q q') rfl,
      coverOverlapMap_fst_assoc, pullback.condition]
  have hpull := congrArg (fun z => pullIso (G := constant S M) z (coverOverlapMap p q q') ha)
    (h a b)
  simp only [n, pullIso_comp, Category.comp_id] at hpull ⊢
  exact (pullIso_congr _ _ _ (coverOverlapMap_fst p q q').symm).trans
    (hpull.trans (pullIso_congr _ _ _ (coverOverlapMap_snd p q q')))

section Spreading

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  [IsAffine S] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
  (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
  {M : AddCommGrpCat.{u}} (e : restrict p F ≅ constant c.pt M)

include hc in
private theorem exists_chart_models {A : Type u} [Finite A] {V : A → Scheme.{u}}
    [∀ a, IsAffine (V a)] (q : ∀ a, V a ⟶ S)
    (N : A → AddCommGrpCat.{u}) [∀ a, AddGroup.FG (N a)]
    (trivialization : ∀ a, restrict (q a) F ≅ constant (V a) (N a)) :
    ∃ j : I, ∃ model : ∀ a, restrict (chartBase (t.app j) (q a)) F ≅
      constant (pullback (t.app j) (q a)) M,
      ∀ a, pullIso (G := constant S M) (model a) ((chartCone D t c p hp (q a)).π.app j)
          (chartCone_base D t c p hp (q a) j) =
        pullIso (G := constant S M) e (pullback.fst p (q a)) pullback.condition := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let oldModel (a : A) : restrict (chartBase p (q a)) F ≅
      constant (pullback p (q a)) (N a) :=
    pullIso (G := constant S (N a)) (trivialization a) (pullback.snd p (q a)) rfl
  let limitModel (a : A) : restrict (chartBase p (q a)) F ≅
      constant (pullback p (q a)) M :=
    pullIso (G := constant S M) e (pullback.fst p (q a)) pullback.condition
  let comparison (a : A) := constantIsoValues ((oldModel a).symm ≪≫ limitModel a)
  have hlevels (a : A) := LocallyConstantAffineLimit.exists_level (TargetLimit.diagram D t (q a))
    (chartCone D t c p hp (q a)) (TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _ hc)
    (comparison a)
  choose i v hv using hlevels
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let r (a : A) : j ⟶ i a := (hj (Finset.mem_image_of_mem i (Finset.mem_univ a))).some
  let values (a : A) : LocallyConstant ↥(pullback (t.app j) (q a)) (N a ≃+ M) :=
    (v a).comap ⟨(TargetLimit.diagram D t (q a)).map (r a), Scheme.Hom.continuous _⟩
  let stageModel (a : A) : restrict (chartBase (t.app j) (q a)) F ≅
      constant (pullback (t.app j) (q a)) (N a) :=
    pullIso (G := constant S (N a)) (trivialization a) (pullback.snd (t.app j) (q a)) rfl
  refine ⟨j, fun a => stageModel a ≪≫ constantIsoOfValues (values a), fun a => ?_⟩
  let l : pullback p (q a) ⟶ pullback (t.app j) (q a) :=
    (chartCone D t c p hp (q a)).π.app j
  change pullIso (G := constant S M) (stageModel a ≪≫ constantIsoOfValues (values a)) l _ =
    limitModel a
  have hstage : pullIso (G := constant S (N a)) (stageModel a) l
      (chartCone_base D t c p hp (q a) j) = oldModel a := by
    dsimp only [stageModel]
    rw [pullIso_comp]
    exact pullIso_congr _ _ _ (chartCone_snd D t c p hp (q a) j)
  have hvalues : (values a).comap ⟨l, l.continuous⟩ = comparison a := by
    apply LocallyConstant.ext
    intro x
    change v a ((TargetLimit.diagram D t (q a)).map (r a) (l x)) = comparison a x
    have hx := congrArg (fun f => f x) ((chartCone D t c p hp (q a)).w (r a))
    exact (congrArg (v a) hx).trans (hv a x)
  rw [pullIso_trans, hstage, pullIso_constantIsoOfValues, hvalues]
  dsimp only [comparison]
  rw [constantIsoOfValues_constantIsoValues, Iso.self_symm_id_assoc]

omit [IsCofiltered I] [IsAffine S] [∀ i, IsAffine (D.obj i)] in
private theorem pull_overlap_limit {j : I} (q : U ⟶ S) (q' : Y ⟶ S)
    (b : U ⟶ Y) (hb : b ≫ q' = q)
    (m : ChartModel (t.app j) q' F M)
    (hm : pullIso (G := constant S M) m ((chartCone D t c p hp q').π.app j)
        (chartCone_base D t c p hp q' j) =
      pullIso (G := constant S M) e (pullback.fst p q') pullback.condition) :
    pullIso (G := constant S M)
        (pullIso (G := constant S M) m (chartMap (t.app j) b hb) (chartMap_base _ b hb))
        ((chartCone D t c p hp q).π.app j) (chartCone_base D t c p hp q j) =
      pullIso (G := constant S M) e (pullback.fst p q) pullback.condition := by
  calc
    _ = pullIso (G := constant S M)
        (pullIso (G := constant S M) m ((chartCone D t c p hp q').π.app j)
          (chartCone_base D t c p hp q' j)) (chartMap p b hb) (chartMap_base _ b hb) := by
      simp only [pullIso_comp]
      exact pullIso_congr _ _ _ (chartCone_naturality D t c p hp q b hb j)
    _ = _ := by
      rw [hm, pullIso_comp]
      exact pullIso_congr _ _ _ (by simp)

include hc in
private theorem exists_overlap_level {N : AddCommGrpCat.{u}} [AddGroup.FG N]
    [IsAffine U] (q : U ⟶ S) {j : I}
    (a : ChartModel (t.app j) q F N) (m m' : ChartModel (t.app j) q F M)
    (h : pullIso (G := constant S M) m ((chartCone D t c p hp q).π.app j)
        (chartCone_base D t c p hp q j) =
      pullIso (G := constant S M) m' ((chartCone D t c p hp q).π.app j)
        (chartCone_base D t c p hp q j)) :
    ∃ (l : I) (r : l ⟶ j),
      pullIso (G := constant S M) m ((TargetLimit.diagram D t q).map r)
          (chartDiagram_map_base D t q r) =
        pullIso (G := constant S M) m' ((TargetLimit.diagram D t q).map r)
          (chartDiagram_map_base D t q r) := by
  have hvalues := (pullIso_eq_iff a m m' _ _).mp h
  obtain ⟨l, r, hr⟩ := LocallyConstantAffineLimit.exists_level_eq (TargetLimit.diagram D t q)
    (chartCone D t c p hp q) (TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _ hc)
    (constantIsoValues (a.symm ≪≫ m)) (constantIsoValues (a.symm ≪≫ m')) hvalues
  exact ⟨l, r, (pullIso_eq_iff a m m' _ _).mpr hr⟩

omit [IsCofiltered I] [IsAffine S] [∀ i, IsAffine (D.obj i)] in
private theorem pull_chartModel_map {i j : I} (r : i ⟶ j) (q : U ⟶ S) (q' : Y ⟶ S)
    (b : U ⟶ Y) (hb : b ≫ q' = q) (m : ChartModel (t.app j) q' F M) :
    pullIso (G := constant S M)
        (pullIso (G := constant S M) m ((TargetLimit.diagram D t q').map r)
          (chartDiagram_map_base D t q' r))
        (chartMap (t.app i) b hb) (chartMap_base _ b hb) =
      pullIso (G := constant S M)
        (pullIso (G := constant S M) m (chartMap (t.app j) b hb) (chartMap_base _ b hb))
        ((TargetLimit.diagram D t q).map r) (chartDiagram_map_base D t q r) := by
  simp only [pullIso_comp]
  exact pullIso_congr _ _ _ (chartDiagram_naturality D t q b hb r).symm

include hc hp e in
/-- A trivialization of a finitely generated local system on a cofiltered limit of affine
schemes over an affine base exists at some level of the diagram. -/
theorem exists_level_trivialization (hF : IsFinitelyGeneratedLocallyConstant.{u, u} F) :
    ∃ i : I, Nonempty (restrict (t.app i) F ≅ constant (D.obj i) M) := by
  classical
  obtain ⟨𝒰, hfin, ha, htriv⟩ := exists_finite_affine_cover hF
  choose N hN hex using htriv
  let a (i : 𝒰.I₀) := (hex i).some
  let : Finite 𝒰.I₀ := hfin
  let : ∀ i, IsAffine (𝒰.X i) := ha
  let : ∀ i, AddGroup.FG (N i) := hN
  obtain ⟨j, m, hm⟩ := exists_chart_models D t c hc p hp e 𝒰.f N a
  let q (ab : 𝒰.I₀ × 𝒰.I₀) : pullback (𝒰.f ab.1) (𝒰.f ab.2) ⟶ S :=
    overlapBase (𝒰.f ab.1) (𝒰.f ab.2)
  let left (ab : 𝒰.I₀ × 𝒰.I₀) : ChartModel (t.app j) (q ab) F M :=
    pullIso (G := constant S M) (m ab.1) (chartMap (t.app j)
      (pullback.fst (𝒰.f ab.1) (𝒰.f ab.2)) rfl) (chartMap_base _ _ rfl)
  let right (ab : 𝒰.I₀ × 𝒰.I₀) : ChartModel (t.app j) (q ab) F M :=
    pullIso (G := constant S M) (m ab.2) (chartMap (t.app j)
      (pullback.snd (𝒰.f ab.1) (𝒰.f ab.2)) pullback.condition.symm)
      (chartMap_base _ _ pullback.condition.symm)
  have hpair (ab : 𝒰.I₀ × 𝒰.I₀) : ∃ (l : I) (r : l ⟶ j),
      pullIso (G := constant S M) (left ab) ((TargetLimit.diagram D t (q ab)).map r)
          (chartDiagram_map_base D t (q ab) r) =
        pullIso (G := constant S M) (right ab) ((TargetLimit.diagram D t (q ab)).map r)
          (chartDiagram_map_base D t (q ab) r) := by
    let : IsAffineHom (𝒰.f ab.2) := inferInstance
    let : IsAffine (pullback (𝒰.f ab.1) (𝒰.f ab.2)) := inferInstance
    let oldModel : ChartModel (t.app j) (q ab) F (N ab.1) :=
      pullIso (G := constant S (N ab.1)) (a ab.1)
        (pullback.snd (t.app j) (q ab) ≫ pullback.fst (𝒰.f ab.1) (𝒰.f ab.2))
        (Category.assoc _ _ _)
    refine exists_overlap_level D t c hc p hp (q ab) oldModel (left ab) (right ab) ?_
    exact (pull_overlap_limit D t c p hp e (q ab) (𝒰.f ab.1)
      (pullback.fst (𝒰.f ab.1) (𝒰.f ab.2)) rfl (m ab.1) (hm ab.1)).trans
      (pull_overlap_limit D t c p hp e (q ab) (𝒰.f ab.2)
        (pullback.snd (𝒰.f ab.1) (𝒰.f ab.2)) pullback.condition.symm (m ab.2) (hm ab.2)).symm
  choose l r hr using hpair
  obtain ⟨k, d, factor, hfactor⟩ := IsCofiltered.wideCospan r
  let n (i : 𝒰.I₀) : ChartModel (t.app k) (𝒰.f i) F M :=
    pullIso (G := constant S M) (m i) ((TargetLimit.diagram D t (𝒰.f i)).map d)
      (chartDiagram_map_base D t (𝒰.f i) d)
  refine ⟨k, glue_chart_models (t.app k) 𝒰 n hF.1 (fun i i' => ?_)⟩
  dsimp only [n]
  rw [pull_chartModel_map, pull_chartModel_map]
  let ab : 𝒰.I₀ × 𝒰.I₀ := (i, i')
  let Q := TargetLimit.diagram D t (q ab)
  have hd : Q.map (factor ab) ≫ Q.map (r ab) = Q.map d := by
    rw [← Q.map_comp, hfactor ab]
  have h := congrArg
    (fun z => pullIso (G := constant S M) z (Q.map (factor ab))
      (chartDiagram_map_base D t (q ab) (factor ab))) (hr ab)
  simp only [pullIso_comp] at h
  exact (pullIso_congr _ _ _ hd.symm).trans (h.trans (pullIso_congr _ _ _ hd))

end Spreading

end Langlands.AlgebraicGeometry.EtaleLocalSystem
