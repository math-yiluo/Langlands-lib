import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement
import Langlands.GroupScheme.Descent.AffineLimitIsomorphism
import Langlands.GroupScheme.HomScheme.AdmissibleMatching
import Langlands.GroupScheme.HomScheme.ChartCoverTransport
import Langlands.GroupScheme.HomScheme.TorusSubgroupCoefficientModel
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Filtered colimits of actual closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open Langlands.AlgebraicGeometry.UnramifiedFunctor
open Langlands.AlgebraicGeometry.SchemeLimitModel
open SubgroupFunctor

/-- Murre's filtered-colimit condition for actual closed torus subgroups. -/
def AdmissibleFilteredColimitsStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G : GroupScheme S)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom],
    FilteredColimits (smallAdmissiblePresheaf G)

private abbrev underlyingRing (R : Type u) [CommRing R] :
    CommAlgCat.{u} R ⥤ CommRingCat.{u} :=
  (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget _

section AlgebraColimit

variable {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
  (K : J ⥤ CommAlgCat.{u} R) {c : Cocone K} (hc : IsColimit c)

include hc in
private theorem exists_algHom_factor (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (φ : B →ₐ[R] c.pt) :
    ∃ (i : J) (ψ : B →ₐ[R] K.obj i), (c.ι.app i).hom.comp ψ = φ := by
  let : IsConnected J := IsFiltered.isConnected J
  let F := K ⋙ underlyingRing R
  let c₀ := (underlyingRing R).mapCocone c
  have hc₀ : IsColimit c₀ := isColimitOfPreserves (underlyingRing R) hc
  let a (A : CommAlgCat.{u} R) : CommRingCat.of R ⟶ (underlyingRing R).obj A :=
    CommRingCat.ofHom (algebraMap R A)
  let α : (Functor.const J).obj (CommRingCat.of R) ⟶ F :=
    { app i := a (K.obj i)
      naturality := by
        intro i j r
        change 𝟙 _ ≫ a (K.obj j) = a (K.obj i) ≫ F.map r
        rw [Category.id_comp]
        exact (Under.w ((commAlgCatEquivUnder (CommRingCat.of R)).functor.map (K.map r))).symm }
  let b := a (CommAlgCat.of R B)
  have hb : b.hom.FinitePresentation := by
    change (algebraMap R B).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨i, ψ, hw, hψ⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of R) F α b c₀ hc₀ hb (CommRingCat.ofHom φ.toRingHom) (by
      intro i
      ext1
      exact φ.comp_algebraMap.trans (c.ι.app i).hom.comp_algebraMap.symm)
  let ψ' : B →ₐ[R] K.obj i :=
    { toRingHom := ψ.hom
      commutes' := fun x => congrArg (fun k : CommRingCat.of R ⟶ F.obj i => k.hom x) hw }
  refine ⟨i, ψ', ?_⟩
  ext x
  exact congrArg (fun k : CommRingCat.of B ⟶ c₀.pt => k.hom x) hψ.symm

end AlgebraColimit

private theorem exists_level_range_le
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S : Scheme.{u}} [IsAffine S] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    {H L G : GroupScheme S} [IsAffine H.X.left]
    [LocallyOfFinitePresentation H.X.hom] [LocallyOfFinitePresentation L.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (j : H ⟶ G) (k : L ⟶ G) (hk : IsClosedSubgroup k)
    (h : range ((baseChange p).map j) ≤ range ((baseChange p).map k)) :
    ∃ i : I, ∀ (l : I) (_ : l ⟶ i),
      range ((baseChange (t.app l)).map j) ≤ range ((baseChange (t.app l)).map k) := by
  let v := j.hom.hom
  let w := k.hom.hom
  let q := pullback.fst v w
  have hpb := IsPullback.of_hasPullback v w
  have hpb' := hpb.map (Over.forget S)
  have hw : IsClosedImmersion w.left := hk
  have : IsClosedImmersion q.left :=
    MorphismProperty.of_isPullback hpb'.flip hw
  have : IsAffine (pullback v w).left := isAffine_of_isAffineHom q.left
  have : LocallyOfFinitePresentation (w.left ≫ G.X.hom) :=
    w.w.symm ▸ inferInstanceAs (LocallyOfFinitePresentation L.X.hom)
  have hwfp : LocallyOfFinitePresentation w.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp _ G.X.hom
  have : LocallyOfFinitePresentation q.left :=
    MorphismProperty.of_isPullback hpb'.flip hwfp
  have : LocallyOfFinitePresentation (pullback v w).hom := by
    rw [← q.w]
    infer_instance
  let P := Over.pullback p
  have hj : P.map v ∈ (range ((baseChange p).map j)).carrier (P.obj H.X) :=
    mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨d, hd⟩ := mem_range.mp ((le_def.mp h) _ hj)
  have hP := hpb.map P
  have : IsClosedImmersion (P.map w).left :=
    (hk.baseChange p)
  have : Mono (P.map w) := (Over.forget _).mono_of_mono_map
    (inferInstanceAs (Mono (P.map w).left))
  have : Mono (P.map q) := hP.mono_fst_of_mono
  have : IsSplitEpi (P.map q) := IsSplitEpi.mk'
    ⟨hP.lift (𝟙 _) d ((Category.id_comp _).trans hd.symm), hP.lift_fst _ _ _⟩
  have : IsIso (P.map q) := isIso_of_mono_of_isSplitEpi _
  have : IsIso (P.map q).left := (Over.forget _).map_isIso (P.map q)
  obtain ⟨i, hi⟩ := Descent.AffineLimit.exists_level_isIso D t c hc p hp q
  refine ⟨i, fun l r => le_def.mpr fun U x hx => ?_⟩
  let Pₗ := Over.pullback (t.app l)
  have hcomp : D.map r ≫ t.app i = t.app l :=
    (t.naturality r).trans (Category.comp_id _)
  have : IsIso ((Over.pullback (t.app i)).map q).left := hi
  have hIso : IsIso (Pₗ.map q).left := Descent.AffineLimit.isIso_pullback_of_comp
    (t.app i) (D.map r) (t.app l) hcomp q
  have : IsIso ((Over.forget _).map (Pₗ.map q)) := hIso
  have : IsIso (Pₗ.map q) := isIso_of_reflects_iso (Pₗ.map q) (Over.forget (D.obj l))
  obtain ⟨y, hy⟩ := mem_range.mp hx
  refine mem_range.mpr ⟨y ≫ inv (Pₗ.map q) ≫ Pₗ.map (pullback.snd v w), ?_⟩
  change (y ≫ inv (Pₗ.map q) ≫ Pₗ.map (pullback.snd v w)) ≫ Pₗ.map w = x
  rw [Category.assoc, Category.assoc, ← Pₗ.map_comp, ← hpb.w,
    Pₗ.map_comp, IsIso.inv_hom_id_assoc]
  exact hy

set_option maxHeartbeats 900000 in
private theorem exists_stage_range_eq {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (i : J)
    {H L G : GroupScheme (Spec (F.obj i))} [IsAffine H.X.left] [IsAffine L.X.left]
    [LocallyOfFinitePresentation H.X.hom] [LocallyOfFinitePresentation L.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (j : H ⟶ G) (k : L ⟶ G) (hj : IsClosedSubgroup j) (hk : IsClosedSubgroup k)
    (h : range ((baseChange (Spec.map (c.ι.app i))).map j) =
      range ((baseChange (Spec.map (c.ι.app i))).map k)) :
    ∃ (l : J) (r : i ⟶ l), range ((baseChange (Spec.map (F.map r))).map j) =
      range ((baseChange (Spec.map (F.map r))).map k) := by
  let K := initialRingAlgebraDiagram F i
  let c₀ := initialRingAlgebraCocone F i c
  let B := F.obj i
  let D := spectrumDiagram B K
  let t := spectrumStructure B K
  let C := spectrumCone B K c₀
  let p := spectrumBaseMap B K c₀
  have hC : IsLimit C :=
    spectrumConeIsLimit B K c₀ (initialRingAlgebraCoconeIsColimit F i c hc)
  have hp : ∀ l, C.π.app l ≫ t.app l = p := spectrumCone_compat B K c₀
  have : ∀ l, IsAffine (D.obj l) := spectrumDiagram_obj_isAffine B K
  have hlim : range ((baseChange p).map j) = range ((baseChange p).map k) := h
  obtain ⟨l₁, hl₁⟩ := exists_level_range_le D (S := Spec B) t C hC p hp j k hk hlim.le
  obtain ⟨l₂, hl₂⟩ := exists_level_range_le D (S := Spec B) t C hC p hp k j hj hlim.ge
  obtain ⟨l, r₁, r₂, -⟩ := IsCofilteredOrEmpty.cone_objs l₁ l₂
  exact ⟨l.unop.right, l.unop.hom, le_antisymm (hl₁ l r₁) (hl₂ l r₂)⟩

section SubgroupColimit

variable {S : Scheme.{u}} (G : GroupScheme S) {R : Type u} [CommRing R]
  (f : Spec (CommRingCat.of R) ⟶ S)
  {J : Type u} [SmallCategory J] [IsFiltered J]
  (K : J ⥤ CommAlgCat.{u} R) {c : Cocone K} (hc : IsColimit c)

include hc in
set_option maxHeartbeats 1600000 in
private theorem exists_restrict_eq [IsNoetherianRing R]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    (x : AdmissibleSubgroup ((baseChange (algebraOver f c.pt).hom).obj G)) :
    ∃ (i : J) (y : AdmissibleSubgroup ((baseChange (algebraOver f (K.obj i)).hom).obj G)),
      restrict (algHomOver f (c.ι.app i).hom) y = x := by
  let G₀ := (baseChange f).obj G
  have : LocallyOfFinitePresentation G₀.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  have : IsSeparated G₀.X.hom :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : QuasiCompact G₀.X.hom :=
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  let e := Descent.pullbackComparison f (Spec.algebraMap R c.pt)
    (algebraOver f c.pt).hom rfl G
  let x₀ : AdmissibleSubgroup ((baseChange (Spec.algebraMap R c.pt)).obj G₀) :=
    ⟨x.val.comap e.hom, isAdmissible_comapIso x e⟩
  obtain ⟨m⟩ := exists_admissibleCoefficientModel R c.pt G₀ x₀
  let B := m.coefficients
  have : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp m.finite
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨i, ψ, hψ⟩ := exists_algHom_factor K hc B m.coefficients.val
  let A := algSpec (CommRingCat.of R)
  let a : Over.mk (Spec.algebraMap R (K.obj i)) ⟶ Over.mk (Spec.algebraMap R B) :=
    A.map (CommAlgCat.ofHom ψ).op
  let b : Over.mk (Spec.algebraMap R c.pt) ⟶ Over.mk (Spec.algebraMap R (K.obj i)) :=
    A.map (c.ι.app i).op
  have hab : b ≫ a = coefficientMap R B c.pt := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (c.ι.app i).hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) = Spec.algebraMap B c.pt
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun d : B →ₐ[R] c.pt => Spec.map (CommRingCat.ofHom d.toRingHom)) hψ
  let j := familyHom m.hom a
  let j' := pushFamily f j
  let y : AdmissibleSubgroup ((baseChange (algebraOver f (K.obj i)).hom).obj G) :=
    ⟨range j', isAdmissible_range _ (isClosedSubgroup_pushFamily f _
      (isClosedSubgroup_familyHom _ m.closed a)) (m.torus.baseChange a.left)⟩
  refine ⟨i, y, Subtype.ext ?_⟩
  have hb : (Over.map f).map b = algHomOver f (c.ι.app i).hom := by
    apply Over.OverMorphism.ext
    rfl
  rw [restrict_eq_evaluate y j' rfl, ← hb, evaluate, familyHom_pushFamily]
  let r := admissibleRepresentative x
  have heval : range (familyHom j b) = range (r.hom ≫ e.inv) := by
    change evaluate (familyHom m.hom a) b = _
    rw [evaluate_comp, hab, m.evaluates]
    change x.val.comap e.hom = range (r.hom ≫ e.inv)
    exact (congrArg (comap e.hom) r.represents.2).symm.trans (range_comp_iso r.hom e.symm).symm
  calc
    _ = range (r.hom ≫ e.inv ≫ e.hom) := by
      rw [← Category.assoc]
      exact range_postcomp_congr _ _ e.hom heval
    _ = x.val := by simpa only [Iso.inv_hom_id, Category.comp_id] using r.represents.2

private theorem evaluate_eq_iff_range_baseChange {T U : Over S} {H L : GroupScheme T.left}
    (j : H ⟶ (baseChange T.hom).obj G) (k : L ⟶ (baseChange T.hom).obj G)
    (a : U ⟶ T) :
    evaluate j a = evaluate k a ↔
      range ((baseChange a.left).map j) = range ((baseChange a.left).map k) :=
  range_comp_iso_eq_iff _ _ (Descent.pullbackComparison T.hom a.left U.hom a.w G)

include hc in
set_option maxHeartbeats 1000000 in
private theorem exists_restrict_eq_of_eq [LocallyOfFinitePresentation G.X.hom] (i : J)
    (x y : AdmissibleSubgroup ((baseChange (algebraOver f (K.obj i)).hom).obj G))
    (h : restrict (algHomOver f (c.ι.app i).hom) x =
      restrict (algHomOver f (c.ι.app i).hom) y) :
    ∃ (l : J) (r : i ⟶ l),
      restrict (algHomOver f (K.map r).hom) x = restrict (algHomOver f (K.map r).hom) y := by
  let : IsConnected J := IsFiltered.isConnected J
  let F := K ⋙ underlyingRing R
  let c₀ := (underlyingRing R).mapCocone c
  have hc₀ : IsColimit c₀ := isColimitOfPreserves (underlyingRing R) hc
  let j := admissibleRepresentative x
  let k := admissibleRepresentative y
  have : IsAffine (algebraOver f (K.obj i)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (K.obj i))))
  have : IsAffineHom j.group.X.hom := j.torus.isAffineHom
  have : IsAffineHom k.group.X.hom := k.torus.isAffineHom
  have : IsAffine j.group.X.left := isAffine_of_isAffineHom j.group.X.hom
  have : IsAffine k.group.X.left := isAffine_of_isAffineHom k.group.X.hom
  have : Smooth j.group.X.hom := j.torus.smooth
  have : Smooth k.group.X.hom := k.torus.smooth
  let Gᵢ := (baseChange (algebraOver f (K.obj i)).hom).obj G
  have : LocallyOfFiniteType Gᵢ.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  let a := algHomOver f (c.ι.app i).hom
  have he : evaluate j.hom a = evaluate k.hom a :=
    (restrict_eq_evaluate x j.hom j.represents.2 a).symm.trans
      ((congrArg Subtype.val h).trans (restrict_eq_evaluate y k.hom k.represents.2 a))
  have hlim : range ((baseChange (Spec.map (c₀.ι.app i))).map j.hom) =
      range ((baseChange (Spec.map (c₀.ι.app i))).map k.hom) :=
    (evaluate_eq_iff_range_baseChange G j.hom k.hom a).mp he
  obtain ⟨l, r, hr⟩ := exists_stage_range_eq F c₀ hc₀ i
    j.hom k.hom j.closed k.closed hlim
  let b := algHomOver f (K.map r).hom
  have hb : evaluate j.hom b = evaluate k.hom b :=
    (evaluate_eq_iff_range_baseChange G j.hom k.hom b).mpr hr
  exact ⟨l, r, Subtype.ext ((restrict_eq_evaluate x j.hom j.represents.2 b).trans
    (hb.trans (restrict_eq_evaluate y k.hom k.represents.2 b).symm))⟩

end SubgroupColimit

set_option maxHeartbeats 1000000 in
/-- The small presheaf of actual closed torus subgroups commutes with filtered
colimits on the affine opens of a locally noetherian base. -/
theorem smallAdmissiblePresheaf_filteredColimits : AdmissibleFilteredColimitsStatement.{u} := by
  intro S _ G _ _ _ R _ f hf
  let : IsOpenImmersion f := hf
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion f)
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y h => ?_)
  · let e := smallAdmissibleEquiv G (algebraOver f c.pt)
    obtain ⟨i, z, hz⟩ := exists_restrict_eq G f K hc (e x)
    let eᵢ := smallAdmissibleEquiv G (algebraOver f (K.obj i))
    refine ⟨i, eᵢ.symm z, e.injective ?_⟩
    exact ((smallAdmissibleEquiv_map (algHomOver f (c.ι.app i).hom) (eᵢ.symm z)).trans
      ((congrArg (restrict (algHomOver f (c.ι.app i).hom)) (eᵢ.apply_symm_apply z)).trans hz)).symm
  · let e := smallAdmissibleEquiv G (algebraOver f c.pt)
    let eᵢ := smallAdmissibleEquiv G (algebraOver f (K.obj i))
    let a := algHomOver f (c.ι.app i).hom
    have he : restrict a (eᵢ x) = restrict a (eᵢ y) :=
      (smallAdmissibleEquiv_map a x).symm.trans ((congrArg e h).trans (smallAdmissibleEquiv_map a y))
    obtain ⟨j, r, hr⟩ := exists_restrict_eq_of_eq G f K hc i (eᵢ x) (eᵢ y) he
    let eⱼ := smallAdmissibleEquiv G (algebraOver f (K.obj j))
    refine ⟨j, r, eⱼ.injective ?_⟩
    let b := algHomOver f (K.map r).hom
    have hx : eⱼ ((smallAdmissiblePresheaf G).map b.op x) = restrict b (eᵢ x) :=
      smallAdmissibleEquiv_map b x
    have hy : eⱼ ((smallAdmissiblePresheaf G).map b.op y) = restrict b (eᵢ y) :=
      smallAdmissibleEquiv_map b y
    exact hx.trans (hr.trans hy.symm)

end Langlands.GroupScheme.TorusSubgroupModuli
