import Langlands.GroupScheme.Torus.Split
import Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.FieldTheory.SeparableClosure

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open scoped CategoryTheory.Obj in
private theorem isMonHom_of_faithful_map
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    [@IsMonHom _ _ _ (F.obj X) (F.obj Y) (F.monObjObj X) (F.monObjObj Y) (F.map f)] :
    IsMonHom f where
  one_hom := F.map_injective <| by
    simpa [cancel_epi] using IsMonHom.one_hom (M := F.obj X) (N := F.obj Y) (F.map f)
  mul_hom := F.map_injective <| by
    simpa [cancel_epi] using IsMonHom.mul_hom (M := F.obj X) (N := F.obj Y) (F.map f)

private theorem isIso_of_fpqc_pullback {S S' : Scheme.{u}} (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b] {X Y : Over S} (f : X ⟶ Y)
    [IsIso ((Over.pullback b).map f)] : IsIso f := by
  have hp : IsPullback ((Over.pullback b).map f).left
      (pullback.fst X.hom b) (pullback.fst Y.hom b) f.left := by
    refine .of_right (t := .flip <| .of_hasPullback Y.hom b)
      (by simpa using (.flip <| .of_hasPullback X.hom b)) (by simp)
  have : IsIso ((Over.pullback b).map f).left := inferInstance
  have : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso ((Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget S)


open Langlands.AlgebraicGeometry.Picard

private theorem exists_finite_stage_map
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (f : ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj G).X ⟶
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj H).X) :
    ∃ E : FinIntermediateField k Ω,
      ∃ g : ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj G).X ⟶
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj H).X,
        (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) ≫ g.left =
          f.left ≫ (baseChangeCone (Ω := Ω) H.X.left H.X.hom).π.app (op E) := by
  let D := baseChangeDiagram (Ω := Ω) G.X.left G.X.hom
  let c := baseChangeCone (Ω := Ω) G.X.left G.X.hom
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) :=
    { app E := pullback.fst _ _ ≫ G.X.hom
      naturality E E' a := by simp [D, baseChangeDiagram] }
  let a : c.pt ⟶ H.X.left := f.left ≫ pullback.fst _ _
  have fw : f.left ≫ pullback.snd H.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) =
      pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := f.w
  have aw : a ≫ H.X.hom = pullback.fst G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≫ G.X.hom := by
    dsimp [a]
    calc
      _ = (f.left ≫ pullback.snd _ _) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
        simp only [Category.assoc, pullback.condition]
      _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by rw [fw]
      _ = _ := pullback.condition.symm
  have ha : c.π ≫ t = (Functor.const _).map (a ≫ H.X.hom) := by
    rw [aw]
    ext E
    simp [c, t, baseChangeCone]
  obtain ⟨E, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D t H.X.hom c (isLimitBaseChangeCone G.X.left G.X.hom) a ha
  have hg'' : g ≫ H.X.hom = pullback.snd _ _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E.unop.1)) := by
    simpa [t, pullback.condition] using hg'
  let gE : ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.unop.1)))).obj G).X ⟶
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.unop.1)))).obj H).X :=
    Over.homMk (pullback.lift g (pullback.snd _ _) hg'') (by simp)
  refine ⟨E.unop, gE, ?_⟩
  apply pullback.hom_ext
  · simpa [gE, c, a, baseChangeCone] using hg
  · simp only [gE, Over.homMk_left, Category.assoc, pullback.lift_snd,
      baseChangeCone_π_app]
    rw [← Category.assoc, fw]


private theorem baseChangeCompIso_hom_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (G : GroupScheme S) :
    (baseChangeCompIso b c G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) c =
      pullback.map G.X.hom (c ≫ b) G.X.hom b (𝟙 _) c (𝟙 _)
        (by simp) (by simp) := by
  apply (cancel_epi (baseChangeCompIso b c G).inv.hom.hom.left).mp
  have hi : (baseChangeCompIso b c G).inv.hom.hom.left ≫
      (baseChangeCompIso b c G).hom.hom.hom.left = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.left) (baseChangeCompIso b c G).inv_hom_id
  rw [← Category.assoc, hi, Category.id_comp]
  apply pullback.hom_ext
  · simp [Category.assoc]
  · have wi : (baseChangeCompIso b c G).inv.hom.hom.left ≫
        pullback.snd G.X.hom (c ≫ b) =
        pullback.snd (pullback.snd G.X.hom b) c := (baseChangeCompIso b c G).inv.hom.hom.w
    simp only [Category.assoc, pullback.lift_snd]
    rw [pullback.condition, ← Category.assoc, wi]

private def overPullbackTowerIso {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b') :
    Over.pullback b' ≅ Over.pullback b ⋙ Over.pullback c := by
  subst b'
  exact Over.pullbackComp c b

private def baseChangeTowerIso {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b')
    (G : GroupScheme S) : (baseChange b').obj G ≅
      (baseChange c).obj ((baseChange b).obj G) :=
  (Functor.mapGrpNatIso (overPullbackTowerIso b c b' h)).app G ≪≫
    Functor.mapGrpCompIso.app G

private theorem overPullbackTowerIso_hom_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b')
    (G : Over S) :
    ((overPullbackTowerIso b c b' h).hom.app G).left ≫
        pullback.fst (pullback.snd G.hom b) c =
      pullback.map G.hom b' G.hom b (𝟙 _) c (𝟙 _)
        (by simp) (by simp [h]) := by
  subst b'
  apply (cancel_epi ((overPullbackTowerIso b c (c ≫ b) rfl).inv.app G).left).mp
  have hi : ((overPullbackTowerIso b c (c ≫ b) rfl).inv.app G).left ≫
      ((overPullbackTowerIso b c (c ≫ b) rfl).hom.app G).left = 𝟙 _ :=
    congrArg (fun f => f.left) ((overPullbackTowerIso b c (c ≫ b) rfl).app G).inv_hom_id
  rw [← Category.assoc, hi, Category.id_comp]
  apply pullback.hom_ext
  · simp [overPullbackTowerIso, Over.pullbackComp, conjugateIsoEquiv,
      Adjunction.comp_counit_app, Category.assoc]
  · have wi := ((overPullbackTowerIso b c (c ≫ b) rfl).inv.app G).w
    simp only [Category.assoc, pullback.lift_snd]
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (fun z => z ≫ c) wi.symm

private theorem baseChangeTowerIso_hom_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (b' : S'' ⟶ S) (h : c ≫ b = b')
    (G : GroupScheme S) :
    (baseChangeTowerIso b c b' h G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom b) c =
      pullback.map G.X.hom b' G.X.hom b (𝟙 _) c (𝟙 _)
        (by simp) (by simp [h]) := by
  change ((overPullbackTowerIso b c b' h).hom.app G.X).left ≫ _ = _
  exact overPullbackTowerIso_hom_fst b c b' h G.X

private def finiteStageBaseChangeIso
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : FinIntermediateField k Ω) (G : GroupScheme (Spec (CommRingCat.of k))) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj G ≅
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj G) :=
  baseChangeTowerIso (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))
    (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (by rw [← Spec.map_comp, algebraMap_comp_algebraMap]) G

private theorem finiteStageBaseChangeIso_hom_fst
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : FinIntermediateField k Ω) (G : GroupScheme (Spec (CommRingCat.of k))) :
    (finiteStageBaseChangeIso k Ω E G).hom.hom.hom.left ≫
        pullback.fst (pullback.snd G.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k E.1))))
            (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω))) =
      (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (op E) :=
  baseChangeTowerIso_hom_fst _ _ _ _ G


private theorem finiteStageBaseChangeIso_hom_snd
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : FinIntermediateField k Ω) (G : GroupScheme (Spec (CommRingCat.of k))) :
    (finiteStageBaseChangeIso k Ω E G).hom.hom.hom.left ≫
        pullback.snd (pullback.snd G.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k E.1))))
            (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω))) =
      pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
  (finiteStageBaseChangeIso k Ω E G).hom.hom.hom.w

private theorem over_pullback_comm_of_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {S S' : C} (b : S' ⟶ S) {X Y : Over S} {X' Y' : Over S'}
    (a : X' ⟶ (Over.pullback b).obj X)
    (c : Y' ⟶ (Over.pullback b).obj Y) (f : X' ⟶ Y') (g : X ⟶ Y)
    (h : a.left ≫ pullback.fst X.hom b ≫ g.left =
      f.left ≫ c.left ≫ pullback.fst Y.hom b) :
    a ≫ (Over.pullback b).map g = f ≫ c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      pullback.lift_fst] using h
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      pullback.lift_snd]
    calc
      _ = X'.hom := a.w
      _ = f.left ≫ Y'.hom := f.w.symm
      _ = f.left ≫ c.left ≫ pullback.snd Y.hom b :=
        congrArg (fun z => f.left ≫ z) c.w.symm

private theorem over_pullback_comm_of_fst_factors
    {C : Type*} [Category C] [HasPullbacks C]
    {S S' : C} (b : S' ⟶ S) {X Y : Over S} {X' Y' : Over S'}
    (a : X' ⟶ (Over.pullback b).obj X)
    (c : Y' ⟶ (Over.pullback b).obj Y) (f : X' ⟶ Y') (g : X ⟶ Y)
    (p : X'.left ⟶ X.left) (q : Y'.left ⟶ Y.left)
    (ha : a.left ≫ pullback.fst X.hom b = p)
    (hc : c.left ≫ pullback.fst Y.hom b = q)
    (h : p ≫ g.left = f.left ≫ q) :
    a ≫ (Over.pullback b).map g = f ≫ c := by
  apply over_pullback_comm_of_fst
  rw [← Category.assoc, ha, hc]
  exact h

open scoped CategoryTheory.Obj in
private theorem group_iso_of_fpqc_pullback_compat
    {S S' : Scheme.{u}} (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b]
    (G H : GroupScheme S) (G' H' : GroupScheme S')
    (a : G' ≅ (baseChange b).obj G) (c : H' ≅ (baseChange b).obj H)
    (e : G' ≅ H') (g : G.X ⟶ H.X)
    (p : G'.X.left ⟶ G.X.left) (q : H'.X.left ⟶ H.X.left)
    (ha : a.hom.hom.hom.left ≫ pullback.fst G.X.hom b = p)
    (hc : c.hom.hom.hom.left ≫ pullback.fst H.X.hom b = q)
    (hg : p ≫ g.left = e.hom.hom.hom.left ≫ q) : Nonempty (G ≅ H) := by
  have hcomm : a.hom.hom.hom ≫ (Over.pullback b).map g =
      e.hom.hom.hom ≫ c.hom.hom.hom :=
    over_pullback_comm_of_fst_factors b a.hom.hom.hom c.hom.hom.hom
      e.hom.hom.hom g p q ha hc hg
  let e' := a.symm ≪≫ e ≪≫ c
  have hmap : (Over.pullback b).map g = e'.hom.hom.hom := by
    let aX := (Grp.forget _).mapIso a
    let eX := (Grp.forget _).mapIso e
    let cX := (Grp.forget _).mapIso c
    change (Over.pullback b).map g = (aX.symm ≪≫ eX ≪≫ cX).hom
    apply (cancel_epi aX.hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact hcomm
  have : IsMonHom ((Over.pullback b).map g) := by rw [hmap]; infer_instance
  have : IsMonHom g := isMonHom_of_faithful_map (Over.pullback b) g
  have : IsIso ((Over.pullback b).map g) := by rw [hmap]; infer_instance
  have : IsIso g := isIso_of_fpqc_pullback b g
  exact ⟨Grp.mkIso (asIso g) (IsMonHom.one_hom g) (IsMonHom.mul_hom g)⟩

private theorem exists_finite_stage_iso
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj G ≅
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj H) :
    ∃ E : FinIntermediateField k Ω,
      Nonempty ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj G ≅
        (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj H) := by
  obtain ⟨E, g, hg⟩ := exists_finite_stage_map k Ω G H e.hom.hom.hom
  refine ⟨E, ?_⟩
  exact group_iso_of_fpqc_pullback_compat
    (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj G)
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj H)
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj G)
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj H)
    (finiteStageBaseChangeIso k Ω E G) (finiteStageBaseChangeIso k Ω E H) e g _ _
    (finiteStageBaseChangeIso_hom_fst k Ω E G)
    (finiteStageBaseChangeIso_hom_fst k Ω E H) hg

/-- Splitting over an algebraic extension descends to a finite intermediate field
when the original group scheme is quasi-compact and quasi-separated. -/
theorem IsSplitTorus.exists_finiteIntermediateField_of_algebraic
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj G)) :
    ∃ E : FinIntermediateField k Ω,
      IsSplitTorus ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))).obj G) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := h
  have : Smooth (splitTorus (Spec (CommRingCat.of k)) I).X.hom := smooth_splitTorus I
  obtain ⟨E, ⟨eE⟩⟩ := exists_finite_stage_iso k Ω G
    (splitTorus (Spec (CommRingCat.of k)) I)
    (e ≪≫ (splitTorus.baseChangeIso
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) I).symm)
  refine ⟨E, IsSplitTorus.of_iso eE ?_⟩
  exact (isSplitTorus_splitTorus I).baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k E.1)))

/-- A chosen finite intermediate field of the separable closure over which a given
quasi-compact, quasi-separated group scheme splits. The input is a splitting over
the separable closure. -/
def IsSplitTorus.finiteSeparableSplittingField
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))).obj G)) :
    FinIntermediateField k (SeparableClosure k) :=
  Classical.choose (h.exists_finiteIntermediateField_of_algebraic k (SeparableClosure k) G)

/-- The chosen finite intermediate field has the asserted splitting property. -/
theorem IsSplitTorus.finiteSeparableSplittingField_isSplit
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))).obj G)) :
    IsSplitTorus ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
      (algebraMap k (h.finiteSeparableSplittingField k G).1)))).obj G) :=
  Classical.choose_spec (h.exists_finiteIntermediateField_of_algebraic k (SeparableClosure k) G)

/-- A quasi-compact, quasi-separated group scheme which splits over the separable
closure splits over a finite separable extension in the original universe. -/
theorem IsSplitTorus.exists_finiteSeparable_of_separableClosure
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (h : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))).obj G)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      IsSplitTorus ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  let E := h.finiteSeparableSplittingField k G
  have : FiniteDimensional k E.1 := E.2
  refine ⟨E.1, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact h.finiteSeparableSplittingField_isSplit k G

end Langlands.GroupScheme
