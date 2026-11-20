import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingLocus
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.HomScheme.AdmissibleFilteredColimits
import Langlands.GroupScheme.HomScheme.AffineFiberArtinian
import Langlands.GroupScheme.HomScheme.AffineFiberTorusCentralizer
import Langlands.GroupScheme.HomScheme.ArtinianCentralizerParameterSmooth
import Langlands.GroupScheme.SmoothProducts

/-! # Geometry of torus centralizers over arbitrary tests of a Noetherian affine base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

private theorem range_familyHom_eq_centralizer {S : Scheme.{u}} {G : GroupScheme S}
    {U V : Over S} {T C : GroupScheme U.left}
    (c : C ⟶ (baseChange U.hom).obj G) (t : T ⟶ (baseChange U.hom).obj G)
    (h : range c = (range t).centralizer) (a : V ⟶ U) :
    evaluate c a = (evaluate t a).centralizer := by
  let e := Descent.pullbackComparison U.hom a.left V.hom a.w G
  change range ((baseChange a.left).map c ≫ e.hom) =
    (range ((baseChange a.left).map t ≫ e.hom)).centralizer
  rw [range_comp_iso, range_baseChangeHom, h, SubgroupFunctor.centralizer_baseChange,
    ← range_baseChangeHom]
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (centralizer_range_eq_comap_of_iso ((baseChange a.left).map t ≫ e.hom) e.symm).symm

private theorem smooth_of_centralizer_family_pullback {S : Scheme.{u}} {G : GroupScheme S}
    {U V : Over S} {T D : GroupScheme V.left}
    (l : T ⟶ (baseChange V.hom).obj G) (d : D ⟶ (baseChange V.hom).obj G)
    (hd : IsClosedSubgroup d) (hD : Smooth D.X.hom) (hDr : range d = (range l).centralizer)
    (b : U ⟶ V) {C : GroupScheme U.left} (c : C ⟶ (baseChange U.hom).obj G)
    (hc : IsClosedSubgroup c) (he : range c = (evaluate l b).centralizer) : Smooth C.X.hom := by
  let j := familyHom d b
  have : IsClosedImmersion j.hom.hom.left := isClosedSubgroup_familyHom d hd b
  have : IsClosedImmersion c.hom.hom.left := hc
  have hjr : range j = range c := (range_familyHom_eq_centralizer d l hDr b).trans he.symm
  let hj : (range c).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hjr⟩
  let hr : (range c).IsRepresentedBy c := ⟨Over.mono_of_mono_left _, rfl⟩
  exact smooth_of_over_iso ((Grp.forget _).mapIso (hr.isoOfIsRepresentedBy hj))
    (MorphismProperty.pullback_snd (P := @Smooth) _ _ hD)

private theorem hasTorusCentralizerResidueFibres_of_range_eq {S : Scheme.{u}}
    {G T C : GroupScheme S} (t : T ⟶ G) (ht : IsClosedSubgroup t) (hT : RelativeTorus.IsTorus T)
    (c : C ⟶ G) (he : range c = (range t).centralizer) : HasTorusCentralizerResidueFibres c := by
  intro s
  let b := S.fromSpecResidueField s
  refine ⟨_, (baseChange b).map t, ht.baseChange b, hT.baseChange b, ?_⟩
  rw [range_baseChangeHom, range_baseChangeHom, he, SubgroupFunctor.centralizer_baseChange]

section Approximation

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
local notation "S" => Spec (CommRingCat.of R)

set_option maxHeartbeats 1200000 in
private theorem exists_admissible_finite_stage (G : GroupScheme S)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    {B : Type u} [CommRing B] (f : Spec (CommRingCat.of B) ⟶ S)
    {T : GroupScheme (Spec (CommRingCat.of B))} (t : T ⟶ (baseChange f).obj G)
    (ht : IsClosedSubgroup t) (hT : RelativeTorus.IsTorus T) :
    ∃ (V : Over S) (_ : IsLocallyNoetherian V.left) (b : Over.mk f ⟶ V)
      (L : GroupScheme V.left) (l : L ⟶ (baseChange V.hom).obj G),
        IsClosedSubgroup l ∧ RelativeTorus.IsTorus L ∧ evaluate l b = range t := by
  let P := smallAdmissiblePresheaf G
  let U := Over.mk f
  let F : AdmissibleSubgroup ((baseChange U.hom).obj G) := ⟨range t, isAdmissible_range t ht hT⟩
  let x := (smallAdmissibleEquiv G U).symm F
  let : Algebra R B := (Spec.preimage f).hom.toAlgebra
  let K := ChartGluing.adjoinCocone R B
  let h : S ⟶ S := 𝟙 _
  let U' := ((BaseChange.specOver h).obj K.pt).unop
  have hu : U'.hom = f := by
    change Spec.map (Spec.preimage f) ≫ 𝟙 _ = f
    rw [Category.comp_id, Spec.map_preimage]
  let e : U' ≅ U := Over.isoMk (Iso.refl _) ((Category.id_comp _).trans hu.symm)
  have hGood : BaseChange.Good P h :=
    BaseChange.good_of_isOpenImmersion (smallAdmissiblePresheaf_filteredColimits S G) h
  obtain ⟨n, y, hy⟩ := ChartGluing.exists_of_isColimit hGood
    (ChartGluing.isColimitAdjoinCocone R B) (P.map e.hom.op x)
  let V := ((BaseChange.specOver h).obj ((ChartGluing.adjoinDiagram R B).obj n)).unop
  let b' : U' ⟶ V := ((BaseChange.specOver h).map (K.ι.app n)).unop
  let b : U ⟶ V := e.inv ≫ b'
  have hby : P.map b.op y = x := by
    change P.map b'.op y = P.map e.hom.op x at hy
    change P.map (e.inv ≫ b').op y = x
    rw [op_comp, Functor.map_comp_apply, hy, ← Functor.map_comp_apply, ← op_comp,
      Iso.inv_hom_id, op_id, Functor.map_id_apply]
  let v := smallAdmissibleEquiv G V y
  let l := admissibleRepresentative v
  have hb' := congrArg (fun z => (smallAdmissibleEquiv G U z).val) hby
  rw [smallAdmissibleEquiv_map, Equiv.apply_symm_apply] at hb'
  have he := (restrict_eq_evaluate v l.hom l.represents.2 b).symm.trans hb'
  have hV : IsLocallyNoetherian V.left :=
    (inferInstance : IsLocallyNoetherian (Spec (CommRingCat.of (Algebra.adjoin R (n : Set B)))))
  exact ⟨V, hV, b, l.group, l.hom, l.closed, l.torus, he⟩

set_option maxHeartbeats 1200000 in
private theorem smooth_centralizer_of_affine_test (G : GroupScheme S) [Smooth G.X.hom]
    [QuasiCompact G.X.hom] [IsSeparated G.X.hom] (hG : HasAffineResidueFibers G)
    {B : Type u} [CommRing B] (f : Spec (CommRingCat.of B) ⟶ S)
    {T C : GroupScheme (Spec (CommRingCat.of B))}
    (t : T ⟶ (baseChange f).obj G) (ht : IsClosedSubgroup t) (hT : RelativeTorus.IsTorus T)
    (c : C ⟶ (baseChange f).obj G) (hc : IsClosedSubgroup c)
    (hEq : range c = (range t).centralizer) : Smooth C.X.hom := by
  obtain ⟨V, hV, b, L, l, _, hL, hEqL⟩ := exists_admissible_finite_stage G f t ht hT
  let Gv := (baseChange V.hom).obj G
  have : IsSeparated Gv.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : Smooth Gv.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  let Lc := hL.commGroupScheme
  let lc : Lc.toGrp ⟶ Gv := l
  obtain ⟨D, d, hrep, hd⟩ := relativeTorusCentralizer_isClosedRepresentable_of_separated lc hL
  have hD : Smooth D.X.hom := smooth_of_artinianAffineCentralizer
    (isAffineHom_artinianPullback_of_residueFibers V.left Gv (hG.baseChange V.hom))
    lc hL hd hrep
  have hDr : range d = (range l).centralizer :=
    hrep.2.trans (torusCentralizer_eq_centralizer_range lc)
  exact smooth_of_centralizer_family_pullback l d hd hD hDr b c hc
    (hEq.trans (congrArg centralizer hEqL.symm))

set_option maxHeartbeats 1200000 in
private theorem smooth_centralizer_of_test (G : GroupScheme S) [Smooth G.X.hom]
    [QuasiCompact G.X.hom] [IsSeparated G.X.hom] (hG : HasAffineResidueFibers G)
    {U : Over S} {T C : GroupScheme U.left}
    (t : T ⟶ (baseChange U.hom).obj G) (ht : IsClosedSubgroup t) (hT : RelativeTorus.IsTorus T)
    (c : C ⟶ (baseChange U.hom).obj G) (hc : IsClosedSubgroup c)
    (he : range c = (range t).centralizer) : Smooth C.X.hom := by
  apply DynamicBaseSmoothConnected.smooth_of_baseChange
  intro B _ f
  let V := Over.mk (f ≫ U.hom)
  let b : V ⟶ U := Over.homMk f rfl
  exact smooth_centralizer_of_affine_test G hG V.hom (familyHom t b)
    (isClosedSubgroup_familyHom t ht b) (hT.baseChange f) (familyHom c b)
    (isClosedSubgroup_familyHom c hc b) (range_familyHom_eq_centralizer c t he b)

end Approximation

/-- A closed torus on any test over a Noetherian affine base has an actual
smooth closed centralizer under affineness of the ambient residue fibres.
When the ambient fibres are geometrically connected, so are those of the
centralizer. Its fibres are the centralizers of the restricted torus. -/
def AffineFiberTorusCentralizerOverTestsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [Smooth G.X.hom]
    [QuasiCompact G.X.hom] [IsSeparated G.X.hom] [GeometricallyConnected G.X.hom],
    HasAffineResidueFibers G → ∀ (U : Over (Spec (CommRingCat.of R)))
      (T : GroupScheme U.left) (t : T ⟶ (baseChange U.hom).obj G),
      IsClosedSubgroup t → RelativeTorus.IsTorus T →
      ∃ (C : GroupScheme U.left) (c : C ⟶ (baseChange U.hom).obj G),
        IsClosedSubgroup c ∧ Smooth C.X.hom ∧ GeometricallyConnected C.X.hom ∧
          HasTorusCentralizerResidueFibres c ∧ range c = (range t).centralizer

set_option maxHeartbeats 1200000 in
theorem affineFiberTorusCentralizerOverTests : AffineFiberTorusCentralizerOverTestsStatement.{u} := by
  intro R _ _ G _ _ _ _ hG U T t ht hT
  let G' := (baseChange U.hom).obj G
  have : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsSeparated G'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : GeometricallyConnected G'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
  let Tc := hT.commGroupScheme
  let tc : Tc.toGrp ⟶ G' := t
  obtain ⟨D, d, hrep, hd⟩ := relativeTorusCentralizer_isClosedRepresentable_of_separated tc hT
  have hEq : range d = (range t).centralizer :=
    hrep.2.trans (torusCentralizer_eq_centralizer_range tc)
  exact ⟨D, d, hd, smooth_centralizer_of_test G hG t ht hT d hd hEq,
    geometricallyConnected_of_affineFiberCentralizer (hG.baseChange U.hom) tc hT hrep,
    hasTorusCentralizerResidueFibres_of_range_eq t ht hT d hEq, hEq⟩

end Langlands.GroupScheme.TorusSubgroupModuli
