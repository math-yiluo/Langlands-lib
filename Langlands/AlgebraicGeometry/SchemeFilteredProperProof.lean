import Langlands.AlgebraicGeometry.SchemeFilteredProperStatement
import Langlands.AlgebraicGeometry.SchemeFilteredModelProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativeClosedImmersionProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsSeparatedSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.FinitePresentation

/-! # Proof of properness descent along actual limits -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit
open EtaleEquivalenceRelation.Action.TargetLimit

private theorem properSubalgebraDescent
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀]
    {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]
    (hA : IsProper (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))) :
    ∃ (V : Subalgebra A₀ A), V.FG ∧
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥V)))) := by
  let : IsProper (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))) := hA
  obtain ⟨T, hT, _, hsep⟩ := NoetherianApproximation.isSeparatedSubalgebraDescent (A := A) f ∅
  let : Algebra.FiniteType A₀ T := T.fg_iff_finiteType.mp hT
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A₀ T
  let b := Spec.map (CommRingCat.ofHom (algebraMap A₀ T))
  let fT := pullback.snd f b
  let : IsSeparated fT := hsep
  let a := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
  let aT := Spec.map (CommRingCat.ofHom (algebraMap T A))
  have hfac : aT ≫ b = a := by
    dsimp [aT, b, a]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have houter : IsPullback (pullback.fst f a) (pullback.snd f a) f (aT ≫ b) :=
    hfac.symm ▸ IsPullback.of_hasPullback f a
  have hright : IsPullback (pullback.fst f b) fT f b := IsPullback.of_hasPullback f b
  have hin := houter.of_right' hright
  have : IsProper (pullback.snd fT aT) := by
    rw [← hin.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp @IsProper _ _ hA
  obtain ⟨U, hU, _, hp⟩ := NoetherianApproximation.isProperSubalgebraDescent (A := A) fT ∅
  let V : Subalgebra A₀ A := U.restrictScalars A₀
  let : Algebra.FiniteType T U := U.fg_iff_finiteType.mp hU
  have hV : V.FG := by
    apply V.fg_iff_finiteType.mpr
    change Algebra.FiniteType A₀ U
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A₀ T)
      (inferInstance : Algebra.FiniteType T U)
  let v := Spec.map (CommRingCat.ofHom (algebraMap A₀ V))
  let vT := Spec.map (CommRingCat.ofHom (algebraMap T U))
  have hvfac : vT ≫ b = v := by
    dsimp [vT, b, v, V]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    congr 1
  have hvouter : IsPullback (pullback.fst f v) (pullback.snd f v) f (vT ≫ b) :=
    hvfac.symm ▸ IsPullback.of_hasPullback f v
  have hvin := hvouter.of_right' hright
  refine ⟨V, hV, ?_⟩
  change IsProper (pullback.snd f v)
  rw [← hvin.isoPullback_hom_snd]
  exact MorphismProperty.RespectsIso.precomp @IsProper _ _ hp

private theorem propertyModelExistence
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : ∀ {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀]
      {A : Type u} [CommRing A] [Algebra A₀ A]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))
      [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f],
      P (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))) →
      ∃ (T : Subalgebra A₀ A), T.FG ∧
        P (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))) :
    SchemeFilteredPropertyModelExistence P := by
  intro J _ _ F c hc X g _ _ _ hg
  let : Algebra (ULift.{u} ℤ) c.pt := ULift.algebra' ℤ c.pt
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨T₀, hT₀, _, X₀, f₀, π₀, hfp₀, hqc₀, hqs₀, hpb₀⟩ :=
    NoetherianApproximation.schemeSubalgebraDescent
      (A₀ := ULift.{u} ℤ) g ∅
  let : LocallyOfFinitePresentation f₀ := hfp₀
  let : QuasiCompact f₀ := hqc₀
  let : QuasiSeparated f₀ := hqs₀
  let : Algebra.FiniteType (ULift.{u} ℤ) T₀ := T₀.fg_iff_finiteType.mp hT₀
  let : IsNoetherianRing T₀ := Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) T₀
  have hg₀ : P (pullback.snd f₀
      (Spec.map (CommRingCat.ofHom (algebraMap T₀ c.pt)))) := by
    rw [← hpb₀.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp P _ _ hg
  obtain ⟨T₁, hT₁, hg₁⟩ := hdesc f₀ hg₀
  let : Algebra.FiniteType T₀ T₁ := T₁.fg_iff_finiteType.mp hT₁
  let : Algebra.FiniteType (ULift.{u} ℤ) T₁ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType (ULift.{u} ℤ) T₀)
    (inferInstance : Algebra.FiniteType T₀ T₁)
  let : Algebra.FinitePresentation (ULift.{u} ℤ) T₁ :=
    (Algebra.FinitePresentation.of_finiteType (R := ULift.{u} ℤ) (A := T₁)).mp
      inferInstance
  let b : Spec (CommRingCat.of T₁) ⟶ Spec (CommRingCat.of T₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap T₀ T₁))
  let a₁ : Spec c.pt ⟶ Spec (CommRingCat.of T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap T₁ c.pt))
  have ha₁ : a₁ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap T₀ c.pt)) := by
    dsimp [a₁, b]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let g₁ := pullback.snd f₀ b
  let : LocallyOfFinitePresentation g₁ := inferInstance
  let : QuasiCompact g₁ := inferInstance
  let : QuasiSeparated g₁ := inferInstance
  have houter₁ : IsPullback π₀ g f₀ (a₁ ≫ b) := ha₁.symm ▸ hpb₀
  have hright₁ : IsPullback (pullback.fst f₀ b) g₁ f₀ b :=
    IsPullback.of_hasPullback f₀ b
  let π₁ : X ⟶ pullback f₀ b :=
    hright₁.lift π₀ (g ≫ a₁) (by simpa only [Category.assoc] using houter₁.w)
  have hpb₁ : IsPullback π₁ g g₁ a₁ := houter₁.of_right' hright₁
  let z : Spec (CommRingCat.of T₁) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) T₁))
  let : LocallyOfFinitePresentation z := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let D : Jᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let d : Cone D := Scheme.Spec.mapCone c.op
  let hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  let t : D ⟶ (Functor.const Jᵒᵖ).obj (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    { app := fun i => Spec.map (CommRingCat.isInitial.to (F.obj i.unop))
      naturality := fun _ _ _ => specULiftZIsTerminal.hom_ext _ _ }
  let (i : Jᵒᵖ) : IsAffine (D.obj i) := by
    dsimp [D]
    infer_instance
  have ha : d.π ≫ t = (Functor.const Jᵒᵖ).map (a₁ ≫ z) := by
    ext i
    exact specULiftZIsTerminal.hom_ext _ _
  obtain ⟨i, q, hq, _⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t z d hd a₁ ha
  let Xj := pullback g₁ q
  let gj : Xj ⟶ Spec (F.obj i.unop) := pullback.snd g₁ q
  have houter : IsPullback π₁ g g₁ (Spec.map (c.ι.app i.unop) ≫ q) := by
    simpa only [D, d] using hq ▸ hpb₁
  have hright : IsPullback (pullback.fst g₁ q) gj g₁ q :=
    IsPullback.of_hasPullback g₁ q
  exact ⟨i.unop, Xj, gj, _, inferInstance, inferInstance, inferInstance,
    MorphismProperty.pullback_snd _ _ hg₁, houter.of_right' hright⟩

private theorem initialRingModelPropertyDescent
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hmodel : SchemeFilteredPropertyModelExistence P) :
    InitialRingModelPropertyDescent P := by
  intro J _ _ F c hc j₀ X _ _ _
  let p := Spec.map (c.ι.app j₀)
  let g := pullback.fst p X.hom
  constructor
  · intro hg
    let F' := Under.forget j₀ ⋙ F
    let c' := c.whisker (Under.forget j₀)
    have hc' : IsColimit c' :=
      (Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) c).symm hc
    obtain ⟨j, Y, b, π, hfp, hqc, hqs, hb, hpb⟩ :=
      hmodel (Under j₀) F' c' hc' (pullback p X.hom) g hg
    let : LocallyOfFinitePresentation b := hfp
    let : QuasiCompact b := hqc
    let : QuasiSeparated b := hqs
    let q := Spec.map (c.ι.app j.right)
    let r := Spec.map (F.map j.hom)
    let Xj : Over (Spec (F.obj j.right)) := Over.mk (pullback.fst r X.hom)
    let Yj : Over (Spec (F.obj j.right)) := Over.mk b
    let : QuasiCompact Xj.hom := by dsimp [Xj]; infer_instance
    let : QuasiSeparated Xj.hom := by dsimp [Xj]; infer_instance
    let : LocallyOfFinitePresentation Xj.hom := by dsimp [Xj]; infer_instance
    let : QuasiCompact Yj.hom := hqc
    let : QuasiSeparated Yj.hom := hqs
    let : LocallyOfFinitePresentation Yj.hom := hfp
    have hpbY : IsPullback π g Yj.hom q := hpb
    have hqr : q ≫ r = p := by
      dsimp [q, r, p]
      rw [← Spec.map_comp, c.w j.hom]
    have houter : IsPullback (pullback.snd p X.hom) g X.hom (q ≫ r) :=
      hqr.symm ▸ (IsPullback.of_hasPullback p X.hom).flip
    have hright : IsPullback (pullback.snd r X.hom) Xj.hom X.hom r :=
      (IsPullback.of_hasPullback r X.hom).flip
    have hpbX := houter.of_right' hright
    let e : pullback q Xj.hom ≅ pullback q Yj.hom :=
      hpbX.flip.isoPullback.symm ≪≫ hpbY.flip.isoPullback
    have he : e.hom ≫ pullback.fst q Yj.hom = pullback.fst q Xj.hom := by
      simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_inv_fst]
    obtain ⟨k, ek, hek, _⟩ :=
      (initialRingModelMorphismDescent F c hc j.right Xj Yj).2.2
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance e he
    let s := Spec.map (F.map k.hom)
    have hY : P (pullback.fst s Yj.hom) := MorphismProperty.pullback_fst _ _ hb
    have hX : P (pullback.fst s Xj.hom) := by
      rw [← hek]
      exact MorphismProperty.RespectsIso.precomp P _ _ hY
    let htotal := (IsPullback.of_hasPullback s Xj.hom).paste_vert
      (IsPullback.of_hasPullback r X.hom)
    refine ⟨Under.mk (j.hom ≫ k.hom), ?_⟩
    have hsr : Spec.map (F.map (j.hom ≫ k.hom)) = s ≫ r := by
      simp only [Functor.map_comp, Spec.map_comp, s, r]
    change P (pullback.fst (Spec.map (F.map (j.hom ≫ k.hom))) X.hom)
    rw [hsr, ← htotal.isoPullback_inv_fst]
    exact MorphismProperty.RespectsIso.precomp P _ _ hX
  · rintro ⟨j, hj⟩
    let q := Spec.map (c.ι.app j.right)
    let r := Spec.map (F.map j.hom)
    have hqr : q ≫ r = p := by
      dsimp [q, r, p]
      rw [← Spec.map_comp, c.w j.hom]
    have houter : IsPullback (pullback.snd p X.hom) g X.hom (q ≫ r) :=
      hqr.symm ▸ (IsPullback.of_hasPullback p X.hom).flip
    have hright : IsPullback (pullback.snd r X.hom)
        (pullback.fst r X.hom) X.hom r :=
      (IsPullback.of_hasPullback r X.hom).flip
    exact MorphismProperty.of_isPullback (P := P) (houter.of_right' hright) hj

private theorem affineTargetDiagramPropertyDescent
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : InitialRingModelPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (E F : I ⥤ Scheme.{u}) [∀ i, IsAffine (F.obj i)] (α : E ⟶ F)
    (cE : Cone E) (cF : Cone F) (hcF : IsLimit cF)
    (f : cE.pt ⟶ cF.pt) (i₀ : I)
    [LocallyOfFinitePresentation (α.app i₀)] [QuasiCompact (α.app i₀)]
    [QuasiSeparated (α.app i₀)]
    (hcart : ∀ {j : I} (r : j ⟶ i₀),
      IsPullback (E.map r) (α.app j) (α.app i₀) (F.map r))
    (hlim : IsPullback (cE.π.app i₀) f (α.app i₀) (cF.π.app i₀))
    (H : P f) : ∃ i, P (α.app i) := by
  have : IsAffine cF.pt := Scheme.isAffine_of_isLimit cF hcF
  have (i : Iᵒᵖ) : IsAffine (F.op.obj i).unop := by dsimp; infer_instance
  let A := F.op ⋙ Scheme.Γ
  let dA := Scheme.Γ.mapCocone cF.op
  have hcA : IsColimit dA := isColimitOfPreserves Scheme.Γ hcF.op
  let X₀ : Over (Spec (A.obj (op i₀))) :=
    Over.mk (α.app i₀ ≫ (F.obj i₀).isoSpec.hom)
  have : LocallyOfFinitePresentation X₀.hom := by dsimp [X₀]; infer_instance
  have : QuasiCompact X₀.hom := by dsimp [X₀]; infer_instance
  have : QuasiSeparated X₀.hom := by dsimp [X₀]; infer_instance
  have hpb : IsPullback (cE.π.app i₀) (f ≫ cF.pt.isoSpec.hom)
      X₀.hom (Spec.map (dA.ι.app (op i₀))) := by
    apply hlim.of_iso (Iso.refl _) (Iso.refl _) cF.pt.isoSpec (F.obj i₀).isoSpec
    · simp
    · simp
    · simp [X₀]
    · exact (Scheme.isoSpec_hom_naturality
        (X := cF.pt) (Y := F.obj i₀) (cF.π.app i₀)).symm
  have hP : P (pullback.fst (Spec.map (dA.ι.app (op i₀))) X₀.hom) := by
    rw [← hpb.flip.isoPullback_inv_fst]
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _ H)
  obtain ⟨j, hj⟩ := (hdesc A dA hcA (op i₀) X₀).mp hP
  have hpj : IsPullback (E.map j.hom.unop)
      (α.app j.right.unop ≫ (F.obj j.right.unop).isoSpec.hom)
      X₀.hom (Spec.map (A.map j.hom)) := by
    apply (hcart j.hom.unop).of_iso (Iso.refl _) (Iso.refl _)
      (F.obj j.right.unop).isoSpec (F.obj i₀).isoSpec
    · simp
    · simp
    · simp [X₀]
    · exact (Scheme.isoSpec_hom_naturality (F.map j.hom.unop)).symm
  refine ⟨j.right.unop, ?_⟩
  apply (P.cancel_right_of_respectsIso _ (F.obj j.right.unop).isoSpec.hom).mp
  rw [← hpj.flip.isoPullback_hom_fst]
  exact MorphismProperty.RespectsIso.precomp P _ _ hj

private theorem exists_property_level_of_affine_target
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : InitialRingModelPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S X Y : Scheme.{u}}
    [IsAffine S] [IsAffine Y] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (H : P (baseChangeMap a b f w p)) :
    ∃ i, P (baseChangeMap a b f w (t.app i)) := by
  let i₀ : I := Classical.choice (IsCofiltered.nonempty (C := I))
  have : LocallyOfFinitePresentation (baseChangeMap a b f w (t.app i₀)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (baseChangeMap_isPullback a b f w (t.app i₀)).flip inferInstance
  have : QuasiCompact (baseChangeMap a b f w (t.app i₀)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (baseChangeMap_isPullback a b f w (t.app i₀)).flip inferInstance
  have : QuasiSeparated (baseChangeMap a b f w (t.app i₀)) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (baseChangeMap_isPullback a b f w (t.app i₀)).flip inferInstance
  have : LocallyOfFinitePresentation ((Geometry.morphismDiagram a b f w D t).app i₀) :=
    ‹LocallyOfFinitePresentation (baseChangeMap a b f w (t.app i₀))›
  have : QuasiCompact ((Geometry.morphismDiagram a b f w D t).app i₀) :=
    ‹QuasiCompact (baseChangeMap a b f w (t.app i₀))›
  have : QuasiSeparated ((Geometry.morphismDiagram a b f w D t).app i₀) :=
    ‹QuasiSeparated (baseChangeMap a b f w (t.app i₀))›
  exact affineTargetDiagramPropertyDescent P hdesc
    (diagram D t a) (diagram D t b) (Geometry.morphismDiagram a b f w D t)
    (cone D t a c p hp) (cone D t b c p hp)
    (isLimitCone D t b c p hp hc) (baseChangeMap a b f w p) i₀
    (fun r ↦ (Geometry.morphismDiagram_cartesian a b f w D t r).flip)
    (cone_baseChangeMap_isPullback a b f w D t c p hp i₀).flip H

private theorem property_of_charts
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    {S X Y T : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    (p : T ⟶ S) (𝒰 : Y.OpenCover)
    (H : ∀ k, P
      (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl p)) :
    P (baseChangeMap a b f w p) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (baseChangeCover b p 𝒰)
  intro k
  let h := chart_isPullback a b f w p (𝒰.f k)
  change P (pullback.snd (baseChangeMap a b f w p)
    (baseChangeMap (𝒰.f k ≫ b) b (𝒰.f k) rfl p))
  rw [← h.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P _ _ (H k)

private theorem relativePropertyDescent
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    (hdesc : InitialRingModelPropertyDescent P) :
    RelativePropertyDescent P := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ c hc p hp
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  let 𝒰 := Y.affineCover.finiteSubcover
  constructor
  · intro H
    have hchart (k : 𝒰.I₀) :
        ∃ i, P
          (baseChangeMap (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
            (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl (t.app i)) := by
      let g := pullback.snd f (𝒰.f k)
      let z := g ≫ (𝒰.f k ≫ b)
      have hP : P (baseChangeMap z (𝒰.f k ≫ b) g rfl p) :=
        MorphismProperty.of_isPullback (P := P)
          (chart_isPullback a b f w p (𝒰.f k)) H
      exact exists_property_level_of_affine_target P hdesc D t
        z (𝒰.f k ≫ b) g rfl c hc p hp hP
    choose j hj using hchart
    obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
    let r (k : 𝒰.I₀) : i ⟶ j k := (hi (by simp)).some
    refine ⟨i, property_of_charts P a b f w (t.app i) 𝒰 ?_⟩
    intro k
    exact MorphismProperty.of_isPullback (P := P)
      (Geometry.morphismDiagram_cartesian
        (pullback.snd f (𝒰.f k) ≫ (𝒰.f k ≫ b))
        (𝒰.f k ≫ b) (pullback.snd f (𝒰.f k)) rfl D t (r k)).flip (hj k)
  · rintro ⟨i, H⟩
    exact MorphismProperty.of_isPullback (P := P)
      (cone_baseChangeMap_isPullback a b f w D t c p hp i).flip H

private theorem spectrumRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) (hdesc : RelativePropertyDescent P) :
    SpectrumRelativePropertyDescent P := by
  intro R _ J _ _ F c hc X Y f _ _ _ _
  refine (hdesc (spectrumDiagram R F) (spectrumStructure R F)
      X.hom Y.hom f.left (Over.w f) (spectrumCone R F c)
      (spectrumConeIsLimit R F c hc) (spectrumBaseMap R F c)
      (spectrumCone_compat R F c)).trans ?_
  exact ⟨fun ⟨j, h⟩ ↦ ⟨j.unop, h⟩, fun ⟨j, h⟩ ↦ ⟨op j, h⟩⟩

private theorem initialRingRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) (hdesc : SpectrumRelativePropertyDescent P) :
    InitialRingRelativePropertyDescent P := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _
  exact hdesc (F.obj j₀) (initialRingAlgebraDiagram F j₀)
    (initialRingAlgebraCocone F j₀ c) (initialRingAlgebraCoconeIsColimit F j₀ c hc)
      X Y f

private theorem finitePresentationInitialRingRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) (hdesc : InitialRingRelativePropertyDescent P) :
    FinitePresentationInitialRingRelativePropertyDescent P := by
  intro J _ _ F c hc j₀ X Y f _ _ _ _ _ _
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp f.left Y.hom
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  exact hdesc F c hc j₀ X Y f

/-- The separated-model requirement is discharged inside subalgebra descent. -/
theorem schemeFilteredProperModelExistence : SchemeFilteredProperModelExistence.{u} :=
  propertyModelExistence @IsProper properSubalgebraDescent

theorem initialRingModelProperDescent : InitialRingModelProperDescent.{u} :=
  initialRingModelPropertyDescent @IsProper schemeFilteredProperModelExistence

theorem relativeProperDescent : RelativeProperDescent.{u} :=
  relativePropertyDescent @IsProper initialRingModelProperDescent

theorem spectrumProperDescent : SpectrumProperDescent.{u} :=
  spectrumRelativePropertyDescent @IsProper relativeProperDescent

theorem initialRingProperDescent : InitialRingProperDescent.{u} :=
  initialRingRelativePropertyDescent @IsProper spectrumProperDescent

theorem finitePresentationInitialRingProperDescent :
    FinitePresentationInitialRingProperDescent.{u} :=
  finitePresentationInitialRingRelativePropertyDescent @IsProper initialRingProperDescent

/-- All properness forms use actual limits, original ring arrows and arbitrary models. -/
theorem properDescent : ProperDescent.{u} :=
  ⟨schemeFilteredProperModelExistence, initialRingModelProperDescent,
    relativeProperDescent, spectrumProperDescent, initialRingProperDescent,
    finitePresentationInitialRingProperDescent⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
