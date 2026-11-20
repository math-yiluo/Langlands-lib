import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.HomScheme.TorusCentralizerPresheaf
import Langlands.GroupScheme.IdentityJetOpenSubgroup
import Langlands.GroupScheme.IdentityJetSmoothUnitLocus
import Langlands.GroupScheme.IdentityJetStabilizerOpenLocus
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothAtUnit

/-! # The chart of fixed rank and detecting jet order -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open IdentityJet SubgroupFunctor Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter

private def evaluatedOpenFactor {S : Scheme.{u}} {M U T : Over S} {N : GroupScheme M.left}
    {H : GroupScheme U.left} (b : U ⟶ M) (c : H ⟶ (baseChange b.left).obj N) (a : T ⟶ U) :
    (baseChange a.left).obj H ⟶ (baseChange (a ≫ b).left).obj N :=
  (baseChange a.left).map c ≫ (familySourceComparison N b a).hom

private theorem evaluatedOpenFactor_isOpenImmersion {S : Scheme.{u}} {M U T : Over S}
    {N : GroupScheme M.left} {H : GroupScheme U.left} (b : U ⟶ M)
    (c : H ⟶ (baseChange b.left).obj N) [IsOpenImmersion c.hom.hom.left] (a : T ⟶ U) :
    IsOpenImmersion (evaluatedOpenFactor b c a).hom.hom.left := by
  have : IsOpenImmersion ((baseChange a.left).map c).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _ inferInstance
  exact inferInstanceAs (IsOpenImmersion (((baseChange a.left).map c).hom.hom.left ≫
    (familySourceComparison N b a).hom.hom.hom.left))

private theorem evaluatedOpenFactor_comp {S : Scheme.{u}} {G : GroupScheme S}
    {M U T : Over S} {N : GroupScheme M.left} {H : GroupScheme U.left}
    (j : N ⟶ (baseChange M.hom).obj G) (b : U ⟶ M)
    (c : H ⟶ (baseChange b.left).obj N) (a : T ⟶ U) :
    evaluatedOpenFactor b c a ≫ familyHom j (a ≫ b) = familyHom (c ≫ familyHom j b) a := by
  rw [evaluatedOpenFactor, Category.assoc, ← familyHom_evaluate_comp]
  simp only [familyHom, Functor.map_comp, Category.assoc]

private theorem hasTorusCentralizerResidueFibres_of_evaluate_eq {S : Scheme.{u}} {G : GroupScheme S}
    {B T : Over S} {H : GroupScheme B.left} {K : GroupScheme T.left}
    (c : H ⟶ (baseChange B.hom).obj G) (a : T ⟶ B) (i : K ⟶ (baseChange T.hom).obj G)
    (he : evaluate c a = range i) (hi : HasTorusCentralizerResidueFibres i) :
    HasTorusCentralizerResidueFibres ((baseChange a.left).map c) := by
  apply (hasTorusCentralizerResidueFibres_familyHom_iff c a).mp
  exact (hasTorusCentralizerResidueFibres_iff_of_range_eq (i := familyHom c a) (j := i) he).mpr hi

private theorem range_subset_centralizerOpen_of_evaluate_eq {S : Scheme.{u}} {G : GroupScheme S}
    {B T : Over S} {H : GroupScheme B.left} {K : GroupScheme T.left} [Smooth H.X.hom]
    (hG : HasAffineResidueFibers ((baseChange B.hom).obj G))
    (c : H ⟶ (baseChange B.hom).obj G) (hc : HasClosedResidueFibres c) (W : B.left.Opens)
    (hW : (W : Set B.left) = {s | IsTorusCentralizerAt c s})
    (a : T ⟶ B) (i : K ⟶ (baseChange T.hom).obj G)
    (he : evaluate c a = range i) (hi : HasTorusCentralizerResidueFibres i) :
    Set.range a.left ⊆ (W : Set B.left) := by
  rw [hW]
  exact (range_subset_torusCentralizerResidueLocus_iff_of_closedFibres hG c hc a.left).mpr
    (hasTorusCentralizerResidueFibres_of_evaluate_eq c a i he hi)

/-- For fixed rank and jet order, the centralizers that are open in their
actual jet stabilizer have a locally finite-type parameter with a universal closed subgroup. -/
def TorusCentralizerJetChartStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (G : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom], HasAffineResidueFibers G → ∀ (n r : ℕ),
    ∃ (M : Over (Spec R)) (H : GroupScheme M.left) (j : H ⟶ (baseChange M.hom).obj G),
      LocallyOfFiniteType M.hom ∧ IsClosedSubgroup j ∧ Smooth H.X.hom ∧
      GeometricallyConnected H.X.hom ∧ HasTorusCentralizerResidueFibres j ∧
      ∀ (T : Over (Spec R)) (K : GroupScheme T.left) [Smooth K.X.hom]
        [GeometricallyConnected K.X.hom] (i : K ⟶ (baseChange T.hom).obj G),
        IsClosedSubgroup i →
        (∀ a b : T ⟶ M, evaluate j a = range i → evaluate j b = range i → a = b) ∧
          (HasTorusCentralizerResidueFibres i →
            ((∃ a : T ⟶ M, evaluate j a = range i) ↔
              SmoothAlongUnitOfRank K r ∧ OpenInStabilizer i n))

set_option maxHeartbeats 4500000 in
theorem torusCentralizerJetChart : TorusCentralizerJetChartStatement.{u} := by
  intro R _ G _ _ _ _ hG n r
  obtain ⟨D, N, j, hjrep, hj⟩ := identityJetStabilizerParameter R G n
  have : LocallyOfFinitePresentation D.base.hom := D.locallyOfFinitePresentation
  have : IsSeparated D.base.hom := D.separated
  have : IsLocallyNoetherian D.base.left := LocallyOfFiniteType.isLocallyNoetherian D.base.hom
  let Gd := (baseChange D.base.hom).obj G
  have : Smooth Gd.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom D.base.hom))
  have : IsSeparated Gd.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom D.base.hom))
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsSeparated N.X.hom := by rw [← Over.w j.hom.hom]; infer_instance
  have : LocallyOfFiniteType N.X.hom := by rw [← Over.w j.hom.hom]; infer_instance
  have : LocallyOfFinitePresentation N.X.hom := inferInstance
  obtain ⟨V, Z, z, hz, hZ⟩ := identityJetSmoothUnitLocus D.base.left N r
  have : IsClosedImmersion z := hz
  let B := Over.mk ((z ≫ V.ι) ≫ D.base.hom)
  let b : B ⟶ D.base := Over.homMk (z ≫ V.ι) rfl
  have : Mono b.left := inferInstanceAs (Mono (z ≫ V.ι))
  have : Mono b := Over.mono_of_mono_left _
  have : LocallyOfFiniteType b.left := inferInstanceAs (LocallyOfFiniteType (z ≫ V.ι))
  have : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType ((z ≫ V.ι) ≫ D.base.hom))
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  let N₀ := (baseChange b.left).obj N
  have : IsSeparated N₀.X.hom := inferInstanceAs (IsSeparated (pullback.snd N.X.hom b.left))
  have : LocallyOfFinitePresentation N₀.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd N.X.hom b.left))
  have hs : SmoothAlongUnitOfRank N₀ r := (hZ B.left b.left).mp ⟨𝟙 B.left, by simp [b], by
    intro f hf
    exact (cancel_mono (z ≫ V.ι)).mp (hf.trans (Category.id_comp _).symm)⟩
  obtain ⟨H, c, hc, hHs, hHconn, _, _⟩ :=
    RelativeIdentityComponent.smoothAtUnitIdentityComponent B.left N₀ hs.1
  let j₀ := familyHom j b
  let i₀ := c ≫ j₀
  let G₀ := (baseChange B.hom).obj G
  have hj₀ : IsClosedSubgroup j₀ := isClosedSubgroup_familyHom j hj b
  have : IsClosedImmersion j₀.hom.hom.left := hj₀
  have : IsOpenImmersion c.hom.hom.left := hc.isOpenImmersion
  have : Mono i₀.hom.hom.left := inferInstanceAs (Mono (c.hom.hom.left ≫ j₀.hom.hom.left))
  have hi₀ : HasClosedResidueFibres i₀ := by
    intro s
    dsimp only [i₀]
    rw [Functor.map_comp]
    exact IsClosedSubgroup.comp (hc.isClosedImmersion_residueFiber s) (hj₀.baseChange _)
  have : Smooth H.X.hom := hHs
  have : GeometricallyConnected H.X.hom := hHconn
  have : IsSeparated H.X.hom := by rw [← Over.w c.hom.hom]; infer_instance
  have : Smooth G₀.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom B.hom))
  have : IsSeparated G₀.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom B.hom))
  have : QuasiCompact G₀.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom B.hom))
  have : GeometricallyConnected G₀.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom B.hom))
  have : IsLocallyNoetherian N₀.X.left := LocallyOfFiniteType.isLocallyNoetherian N₀.X.hom
  have : QuasiCompact H.X.hom := by
    have : QuasiCompact N₀.X.hom := by rw [← Over.w j₀.hom.hom]; infer_instance
    rw [← Over.w c.hom.hom]
    infer_instance
  have hrH : SmoothAlongUnitOfRank H r := (smoothAlongUnitOfRank_iff_of_open c r).mpr hs
  have hG₀ : HasAffineResidueFibers G₀ := hG.baseChange B.hom
  obtain ⟨W, hW, hiW⟩ := exists_torusCentralizerResidueOpen_of_mono B.left G₀ H hG₀ i₀ hi₀
  let C := Over.mk (W.ι ≫ B.hom)
  let w : C ⟶ B := Over.homMk W.ι rfl
  have : Mono w := Over.mono_of_mono_left w
  let iC := familyHom i₀ w
  have hC : IsClosedSubgroup iC := hiW.comp_iso (Descent.pullbackComparison B.hom w.left C.hom w.w G)
  have hCC : HasTorusCentralizerResidueFibres iC := by
    apply (hasTorusCentralizerResidueFibres_familyHom_iff i₀ w).mpr
    apply (range_subset_torusCentralizerResidueLocus_iff_of_closedFibres hG₀ i₀ hi₀ W.ι).mp
    exact ((Scheme.Opens.range_ι W).trans hW).le
  have : Smooth ((baseChange w.left).obj H).X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom w.left))
  have : GeometricallyConnected ((baseChange w.left).obj H).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom w.left))
  obtain ⟨p, hp, _⟩ := existsUnique_subgroupJetPoint G n D iC hC
  let q := w ≫ b
  let M := equalizer q p
  let m : M ⟶ C := equalizer.ι q p
  let iM := familyHom iC m
  have hM : IsClosedSubgroup iM := isClosedSubgroup_familyHom iC hC m
  have : LocallyOfFiniteType M.hom := by
    rw [← Over.w m, show C.hom = W.ι ≫ B.hom from rfl]
    infer_instance
  have hMC : HasTorusCentralizerResidueFibres iM := by
    apply (hasTorusCentralizerResidueFibres_familyHom_iff iC m).mpr
    exact (range_subset_torusCentralizerResidueLocus_iff (hG.baseChange C.hom) iC hC m.left).mp
      (fun _ _ => hCC _)
  refine ⟨M, _, iM, inferInstance, hM,
    inferInstanceAs (Smooth (pullback.snd ((baseChange w.left).obj H).X.hom m.left)),
    inferInstanceAs (GeometricallyConnected (pullback.snd ((baseChange w.left).obj H).X.hom m.left)),
    hMC, ?_⟩
  intro T K _ _ i hi
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsSeparated ((baseChange T.hom).obj G).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom T.hom))
  have : IsSeparated K.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  obtain ⟨g, hg, hguniq⟩ := existsUnique_subgroupJetPoint G n D i hi
  have evalAux (a : T ⟶ M) : evaluate iM a = evaluate i₀ ((a ≫ m) ≫ w) := by
    rw [show iM = familyHom iC m from rfl, evaluate_comp,
      show iC = familyHom i₀ w from rfl, evaluate_comp]
  have auxJet (a : T ⟶ M) (ha : evaluate iM a = range i) : (((a ≫ m) ≫ w) ≫ b) = g := by
    apply hguniq
    rw [Category.assoc (a ≫ m), Category.assoc a, show m ≫ (w ≫ b) = m ≫ p from equalizer.condition q p,
      ← Category.assoc, Parameter.eval_comp, hp, subgroupJetIdeal_testMap G n iC hC]
    apply subgroupJetIdeal_eq_of_range_eq G n (isClosedSubgroup_familyHom iC hC (a ≫ m)) hi
    exact (evaluate_comp iC m a).symm.trans ha
  refine ⟨fun a a' ha ha' => ?_, fun hiTor => ?_⟩
  · have he := (auxJet a ha).trans (auxJet a' ha').symm
    exact (cancel_mono m).mp ((cancel_mono w).mp ((cancel_mono b).mp he))
  constructor
  · rintro ⟨a, ha⟩
    let v := (a ≫ m) ≫ w
    let l := evaluatedOpenFactor b c v
    have : IsOpenImmersion l.hom.hom.left := evaluatedOpenFactor_isOpenImmersion b c v
    have he : range (familyHom i₀ v) = range i := (evalAux a).symm.trans ha
    have : Mono (familyHom i₀ v).hom.hom.left := by
      change Mono (((baseChange v.left).map i₀).hom.hom.left ≫
        (Descent.pullbackComparison B.hom v.left T.hom v.w G).hom.hom.hom.left)
      have : Mono ((baseChange v.left).map i₀).hom.hom.left :=
        MorphismProperty.overPullbackMap (P := MorphismProperty.monomorphisms Scheme) _ _ inferInstance
      infer_instance
    have : Mono (familyHom i₀ v).hom.hom := Over.mono_of_mono_left _
    have : IsSeparated ((baseChange v.left).obj H).X.hom :=
      inferInstanceAs (IsSeparated (pullback.snd H.X.hom v.left))
    have : LocallyOfFinitePresentation ((baseChange v.left).obj H).X.hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd H.X.hom v.left))
    let he₁ : (range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
    let he₂ : (range i).IsRepresentedBy (familyHom i₀ v) := ⟨inferInstance, he⟩
    let e := he₁.isoOfIsRepresentedBy he₂
    have hel : (e.hom ≫ l) ≫ familyHom j (v ≫ b) = i := by
      rw [Category.assoc, evaluatedOpenFactor_comp, he₁.isoOfIsRepresentedBy_hom_comp he₂]
    have hjet : D.eval (overScheme G n) (v ≫ b) = subgroupJetIdeal G n i := (auxJet a ha).symm ▸ hg
    have hjT := isClosedSubgroup_familyHom j hj (v ≫ b)
    have hrep := isRepresentedBy_subgroupJetStabilizer G n D j hj hjrep (v ≫ b) i hi hjet
    refine ⟨SmoothAlongUnitOfRank.of_iso (SmoothAlongUnitOfRank.baseChange hrH v.left) e,
      ⟨_, _, hjT, hrep, e.hom ≫ l, hel, ?_⟩⟩
    exact inferInstanceAs (IsOpenImmersion (e.hom.hom.hom.left ≫ l.hom.hom.left))
  · rintro ⟨hr, ho⟩
    have hrep := isRepresentedBy_subgroupJetStabilizer G n D j hj hjrep g i hi hg
    have hclosed := isClosedSubgroup_familyHom j hj g
    let f := stabilizerFactor hi hrep
    have hf : f ≫ familyHom j g = i := stabilizerFactor_comp hi hrep
    have : IsOpenImmersion f.hom.hom.left := (openInStabilizer_iff hclosed hrep f hf).mp ho
    have : IsSeparated ((baseChange g.left).obj N).X.hom :=
      inferInstanceAs (IsSeparated (pullback.snd N.X.hom g.left))
    have : LocallyOfFinitePresentation ((baseChange g.left).obj N).X.hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd N.X.hom g.left))
    obtain ⟨k, hk, _⟩ := (hZ T.left g.left).mpr ((smoothAlongUnitOfRank_iff_of_open f r).mp hr)
    let a : T ⟶ B := Over.homMk k (by
      dsimp only [B, Over.mk_hom]
      rw [← Category.assoc, hk, Over.w g])
    have ha : a ≫ b = g := Over.OverMorphism.ext hk
    have hjet' : D.eval (overScheme G n) (a ≫ b) = subgroupJetIdeal G n i := by rwa [ha]
    have hrep' := isRepresentedBy_subgroupJetStabilizer G n D j hj hjrep (a ≫ b) i hi hjet'
    have hclosed' := isClosedSubgroup_familyHom j hj (a ≫ b)
    let f' := stabilizerFactor hi hrep'
    have hf' : f' ≫ familyHom j (a ≫ b) = i := stabilizerFactor_comp hi hrep'
    have : IsOpenImmersion f'.hom.hom.left := (openInStabilizer_iff hclosed' hrep' f' hf').mp ho
    have : LocallyOfFiniteType ((baseChange (a ≫ b).left).obj N).X.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom (a ≫ b).left))
    let l := evaluatedOpenFactor b c a
    have : IsOpenImmersion l.hom.hom.left := evaluatedOpenFactor_isOpenImmersion b c a
    have : Smooth ((baseChange a.left).obj H).X.hom := inferInstanceAs (Smooth (pullback.snd H.X.hom a.left))
    have : GeometricallyConnected ((baseChange a.left).obj H).X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd H.X.hom a.left))
    have hef : range f' = range l := relativeIdentityComponent_range_eq
      (isRelativeIdentityComponent_of_open f') (isRelativeIdentityComponent_of_open l)
    let h₁ : (range f').IsRepresentedBy f' := ⟨Over.mono_of_mono_left _, rfl⟩
    let h₂ : (range f').IsRepresentedBy l := ⟨Over.mono_of_mono_left _, hef.symm⟩
    let e := h₁.isoOfIsRepresentedBy h₂
    have hEval : evaluate i₀ a = range i := by
      rw [evaluate, ← evaluatedOpenFactor_comp j b c a, ← hf']
      exact (range_iso_comp e (l ≫ familyHom j (a ≫ b))).symm.trans (by
        rw [← Category.assoc, h₁.isoOfIsRepresentedBy_hom_comp h₂])
    have haW : Set.range a.left ⊆ (W : Set B.left) :=
      range_subset_centralizerOpen_of_evaluate_eq hG₀ i₀ hi₀ W hW a i hEval hiTor
    let aC : T ⟶ C := Over.homMk (IsOpenImmersion.lift W.ι a.left
      (haW.trans (Scheme.Opens.range_ι W).ge)) (by
        dsimp only [C, Over.mk_hom]
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w a])
    have haC : aC ≫ w = a := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have hEvalC : evaluate iC aC = range i := by
      rw [show iC = familyHom i₀ w from rfl, evaluate_comp, haC, hEval]
    have hEq : aC ≫ q = aC ≫ p := by
      have hp' : aC ≫ p = g := hguniq _ (by
        change D.eval (overScheme G n) (aC ≫ p) = subgroupJetIdeal G n i
        rw [Parameter.eval_comp, hp, subgroupJetIdeal_testMap G n iC hC]
        exact subgroupJetIdeal_eq_of_range_eq G n (isClosedSubgroup_familyHom iC hC aC) hi hEvalC)
      rw [hp', show q = w ≫ b from rfl, ← Category.assoc, haC, ha]
    let aM : T ⟶ M := equalizer.lift aC hEq
    have haM : aM ≫ m = aC := equalizer.lift_ι aC hEq
    have haEval : evaluate iM aM = range i := by
      rw [show iM = familyHom iC m from rfl, evaluate_comp, haM, hEvalC]
    exact ⟨aM, haEval⟩

end Langlands.GroupScheme.TorusSubgroupModuli
