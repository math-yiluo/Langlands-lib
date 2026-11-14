import Langlands.GroupScheme.RelativeLevi.SplitMaximalTorusChartStatement
import Langlands.GroupScheme.RelativeLevi.BorelFiberTransport
import Langlands.GroupScheme.Absolute.ParabolicMaximalTorusProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.RelativeLiftingProof
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.AlgebraicGeometry.SmoothEtaleLocalSections

/-! # Affine étale split maximal-torus charts for relative parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme

open HomScheme

private theorem evaluate_postcomp {S : Scheme.{u}} {H P G : GroupScheme S}
    {M N : Over S} (a : N ⟶ M) (j : RelativeHom H P M) (i : P ⟶ G) :
    evaluate a (j ≫ (baseChange M.hom).map i) =
      evaluate a j ≫ (baseChange N.hom).map i := by
  change Descent.pullHom a.left (Over.w a) (Over.w a)
    (j ≫ (baseChange M.hom).map i) = _
  rw [Descent.pullHom_comp a.left (Over.w a) (Over.w a) (Over.w a) j
    ((baseChange M.hom).map i),
    Descent.pullHom_map a.left M.hom N.hom (Over.w a) i]
  rfl

private theorem maximal_evaluate_iff {S : Scheme.{u}} {H : CommGroupScheme S}
    {G : GroupScheme S} {M : Over S} {k : Type u} [Field k]
    {c : Spec (CommRingCat.of k) ⟶ S} (a : Over.mk c ⟶ M)
    (j : RelativeHom H.toGrp G M) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange c).obj H) (evaluate a j) ↔
      IsMaximalTorus
        (T := (CommGroupScheme.baseChange a.left).obj
          ((CommGroupScheme.baseChange M.hom).obj H)) ((baseChange a.left).map j) := by
  let eH := Descent.pullbackComparison M.hom a.left c (Over.w a) H.toGrp
  let eG := Descent.pullbackComparison M.hom a.left c (Over.w a) G
  constructor
  · intro h
    have hm := (IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange c).obj H)
      (T' := (CommGroupScheme.baseChange a.left).obj
        ((CommGroupScheme.baseChange M.hom).obj H)) eH h).comp_iso eG.symm
    change IsMaximalTorus (T := (CommGroupScheme.baseChange a.left).obj
      ((CommGroupScheme.baseChange M.hom).obj H))
        ((eH.hom ≫ evaluate a j) ≫ eG.inv) at hm
    simpa only [eH, eG, evaluate, Descent.pullHom, Over.mk_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hm
  · intro h
    have hm := (IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange a.left).obj
        ((CommGroupScheme.baseChange M.hom).obj H))
      (T' := (CommGroupScheme.baseChange c).obj H) eH.symm h).comp_iso eG
    exact hm

private theorem maximal_coordinate_evaluate_iff {S : Scheme.{u}}
    (I : Type u) [Finite I] {G : GroupScheme S} {M : Over S}
    (j : RelativeHom (splitTorus S I) G M)
    {k : Type u} [Field k] {c : Spec (CommRingCat.of k) ⟶ S}
    (a : Over.mk c ⟶ M) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange a.left).obj (splitTorus.commGroupScheme M.left I))
      ((baseChange a.left).map ((splitTorus.baseChangeIso M.hom I).inv ≫ j)) ↔
      IsMaximalTorus (T := (CommGroupScheme.baseChange c).obj
        (splitTorus.commGroupScheme S I)) (evaluate a j) := by
  rw [Functor.map_comp]
  exact (IsMaximalTorus.iso_comp_iff
    (T := (CommGroupScheme.baseChange a.left).obj
      ((CommGroupScheme.baseChange M.hom).obj (splitTorus.commGroupScheme S I)))
    (T' := (CommGroupScheme.baseChange a.left).obj (splitTorus.commGroupScheme M.left I))
    ((baseChange a.left).mapIso (splitTorus.baseChangeIso M.hom I).symm) _).trans
      (maximal_evaluate_iff (H := splitTorus.commGroupScheme S I)
        (G := G) (M := M) a j).symm

private theorem exists_affine_closed_evaluations {S : Scheme.{u}}
    (I : Type u) [Finite I] {P G : GroupScheme S}
    [IsAffineHom P.X.hom] [IsAffineHom G.X.hom]
    {M : Over S} [Smooth M.hom]
    (j : RelativeHom (splitTorus S I) P M)
    (v : RelativeHom (splitTorus S I) G M)
    {k : Type u} [Field k] {c : Spec (CommRingCat.of k) ⟶ S}
    (x : Over.mk c ⟶ M)
    (hxj : IsClosedImmersion (evaluate x j).hom.hom.left)
    (hxv : IsClosedImmersion (evaluate x v).hom.hom.left) :
    ∃ (R : CommRingCat.{u}) (p : Spec R ⟶ S)
      (a : Over.mk p ⟶ M) (b : Over.mk c ⟶ Over.mk p),
      Smooth p ∧ b ≫ a = x ∧
        IsClosedImmersion (evaluate a j).hom.hom.left ∧
        IsClosedImmersion (evaluate a v).hom.hom.left := by
  have : IsAffineHom ((baseChange M.hom).obj P).X.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsAffineHom ((baseChange M.hom).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨V, q, hq, bx, hbx, hqj⟩ :=
    exists_open_isClosedImmersion_baseChange ((isSplitTorus_splitTorus I).baseChange M.hom)
      j k x.left ((isClosedImmersion_evaluate_iff x j).mp hxj)
  let := hq
  let N : Over S := Over.mk (q ≫ M.hom)
  let aN : N ⟶ M := Over.homMk q rfl
  have hbc : bx ≫ N.hom = c := by
    dsimp [N]
    rw [← Category.assoc, hbx]
    exact Over.w x
  let bN : Over.mk c ⟶ N := Over.homMk bx hbc
  have hbN : bN ≫ aN = x := by
    apply Over.OverMorphism.ext
    exact hbx
  have hvN : IsClosedImmersion (evaluate bN (evaluate aN v)).hom.hom.left := by
    rw [← evaluate_comp, hbN]
    exact hxv
  have : IsAffineHom ((baseChange N.hom).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨W, r, hr, byx, hbyx, hrv⟩ :=
    exists_open_isClosedImmersion_baseChange ((isSplitTorus_splitTorus I).baseChange N.hom)
      (evaluate aN v) k bN.left ((isClosedImmersion_evaluate_iff bN _).mp hvN)
  let := hr
  let L : Over S := Over.mk (r ≫ N.hom)
  let aL : L ⟶ N := Over.homMk r rfl
  have hbyc : byx ≫ L.hom = c := by
    dsimp [L]
    rw [← Category.assoc, hbyx]
    exact Over.w bN
  let C := TorusClosedImmersionLocus.fieldPointAffineChart byx
  let := C.isOpen
  let p := C.map ≫ L.hom
  let aC : Over.mk p ⟶ L := Over.homMk C.map rfl
  have hCb : C.lift ≫ p = c := by
    dsimp [p]
    rw [← Category.assoc, C.fac]
    exact hbyc
  let bC : Over.mk c ⟶ Over.mk p := Over.homMk C.lift hCb
  have hba : bC ≫ aC ≫ aL ≫ aN = x := by
    apply Over.OverMorphism.ext
    change C.lift ≫ C.map ≫ r ≫ q = x.left
    rw [← Category.assoc, C.fac, ← Category.assoc, hbyx]
    exact hbx
  refine ⟨C.ring, p, aC ≫ aL ≫ aN, bC, ?_, hba, ?_, ?_⟩
  · dsimp [p, L, N]
    infer_instance
  · rw [evaluate_comp, evaluate_comp]
    apply isClosedImmersion_evaluate
    apply isClosedImmersion_evaluate
    exact (isClosedImmersion_evaluate_iff aN j).mpr hqj
  · rw [evaluate_comp, evaluate_comp]
    apply isClosedImmersion_evaluate
    exact (isClosedImmersion_evaluate_iff aL (evaluate aN v)).mpr hrv

private theorem exists_smooth_affine_parabolic_torus
    (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i) (s : S) :
    ∃ (R : CommRingCat.{u}) (p : Spec R ⟶ S), Smooth p ∧
      ∃ (b : Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ Spec R),
        b ≫ p = geometricPoint S s ∧
        ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
          (j : splitTorus (Spec R) I ⟶ (baseChange p).obj P),
          IsClosedSubgroup j ∧ IsClosedSubgroup (j ≫ (baseChange p).map i) ∧
            IsMaximalTorus
              (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme (Spec R) I))
              ((baseChange b).map (j ≫ (baseChange p).map i)) := by
  classical
  let k := AlgebraicClosure (S.residueField s)
  let c : Spec (CommRingCat.of k) ⟶ S := geometricPoint S s
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hPc := hi.isParabolicSubgroup_baseChange hG c
  obtain ⟨T, l, f, hmax, hfl⟩ := parabolicMaximalTorus k ((baseChange c).obj G)
    (hG.isConnectedReductive_baseChange c) ((baseChange c).obj P)
    ((baseChange c).map i) hPc
  have hT := hmax.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨I, hI, ⟨eI⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let H := splitTorus S I
  let e₀ : (baseChange c).obj H ≅ T.toGrp :=
    splitTorus.baseChangeIso c I ≪≫ eI.symm
  let j₀ : RelativeHom H P (Over.mk c) := e₀.hom ≫ f
  have hf : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hPc.isClosedSubgroup (by rw [hfl]; exact hmax.2.1)
  have hj₀ : IsClosedImmersion j₀.hom.hom.left := hf.iso_comp e₀
  obtain ⟨M, j, hj, hM⟩ :=
    smoothSplitSourceRepresentability S H P (isSplitTorus_splitTorus I)
  let := hM
  obtain ⟨x, hx⟩ := (hj (Over.mk c)).surjective j₀
  change evaluate x j = j₀ at hx
  let v : RelativeHom H G M := j ≫ (baseChange M.hom).map i
  have hxv : evaluate x v = e₀.hom ≫ l := by
    dsimp only [v]
    rw [evaluate_postcomp, hx]
    change (e₀.hom ≫ f) ≫ (baseChange c).map i = _
    rw [Category.assoc, hfl]
  have hm : IsMaximalTorus
      (T := (CommGroupScheme.baseChange c).obj (splitTorus.commGroupScheme S I))
      (evaluate x v) := by
    rw [hxv]
    exact IsMaximalTorus.iso_comp (T := T)
      (T' := (CommGroupScheme.baseChange c).obj (splitTorus.commGroupScheme S I)) e₀ hmax
  obtain ⟨R, p, a, b, hp, hba, hP, hGclosed⟩ :=
    exists_affine_closed_evaluations I j v x (by rw [hx]; exact hj₀) hm.2.1
  let jA : splitTorus (Spec R) I ⟶ (baseChange p).obj P :=
    (splitTorus.baseChangeIso p I).inv ≫ evaluate a j
  have heq : jA ≫ (baseChange p).map i =
      (splitTorus.baseChangeIso p I).inv ≫ evaluate a v := by
    dsimp only [jA, v]
    rw [evaluate_postcomp, Category.assoc]
    rfl
  have hmA : IsMaximalTorus
      (T := (CommGroupScheme.baseChange b.left).obj (splitTorus.commGroupScheme (Spec R) I))
      ((baseChange b.left).map (jA ≫ (baseChange p).map i)) := by
    rw [heq]
    apply (maximal_coordinate_evaluate_iff (S := S) I (evaluate a v) b).mpr
    rw [← evaluate_comp, hba]
    exact hm
  refine ⟨R, p, hp, b.left, Over.w b, I, inferInstance, inferInstance, jA,
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso p I).symm hP, ?_, hmA⟩
  rw [heq]
  exact IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso p I).symm hGclosed

/-- A relative parabolic in a reductive group admits affine étale charts with
an actual split torus maximal in every ambient geometric fibre. -/
theorem relativeParabolicSplitMaximalTorusCharts :
    RelativeParabolicSplitMaximalTorusChartStatement.{u} := by
  intro S G P i hG hi s
  obtain ⟨R, p, hp, b, hb, I, hI, hDI, j, hj, hl, hm⟩ :=
    exists_smooth_affine_parabolic_torus S G P i hG hi s
  let := hp
  let Gp := (baseChange p).obj G
  let l : splitTorus (Spec R) I ⟶ Gp := j ≫ (baseChange p).map i
  have hGp : IsReductive Gp := hG.baseChange p
  let : Smooth Gp.X.hom := hGp.smooth
  let : IsAffineHom Gp.X.hom := hGp.isAffineHom
  have hm₀ : IsMaximalTorus (T := splitTorus.commGroupScheme _ I)
      (splitTorus.RelativeCocharacterCentralizer.baseChangedTorusHom I Gp l b) :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme (Spec R) I))
      (T' := splitTorus.commGroupScheme _ I) (splitTorus.baseChangeIso b I).symm hm
  have hs : b (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) ∈
      identityComponentReductiveLocus Gp :=
    (hGp.geometricFiber _).isConnectedReductive_of_isAlgClosed.identityComponent
  have hmem := splitTorus.mem_geometricSelfCentralizingTorusLocus_of_maximal_fieldPoint
    I Gp l (fun k _ _ H hH T j hj => maximalTorusCentralizer k H hH T j hj) hl b hs hm₀
  let O : (Spec R).Opens := ⟨splitTorus.geometricSelfCentralizingTorusLocus I Gp l,
    splitTorus.isOpen_geometricSelfCentralizingTorusLocus I Gp l hl⟩
  let w : O := ⟨b (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))), hmem⟩
  have hw : (O.ι ≫ p) w = s := by
    change (b ≫ p) (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s
    rw [hb]
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  obtain ⟨A, e, a, he, hsrange, hfac⟩ :=
    Langlands.AlgebraicGeometry.exists_etale_spec_of_smooth (O.ι ≫ p) w
  rw [hw] at hsrange
  obtain ⟨t, ht⟩ := hsrange
  let g : Spec A ⟶ Spec R := a ≫ O.ι
  have hg : g ≫ p = e := by
    dsimp only [g]
    simpa only [Category.assoc] using hfac
  let eP := Descent.pullbackComparison p g e hg P
  let eG := Descent.pullbackComparison p g e hg G
  let jE : splitTorus (Spec A) I ⟶ (baseChange e).obj P :=
    ((splitTorus.baseChangeIso g I).inv ≫ (baseChange g).map j) ≫ eP.hom
  have hjE : IsClosedSubgroup jE :=
    ((hj.baseChange g).iso_comp (splitTorus.baseChangeIso g I).symm).comp_iso eP
  have hEq : jE ≫ (baseChange e).map i =
      ((splitTorus.baseChangeIso g I).inv ≫ (baseChange g).map l) ≫ eG.hom := by
    have hn : (baseChange g).map ((baseChange p).map i) ≫ eG.hom =
        eP.hom ≫ (baseChange e).map i :=
      Descent.pullbackComparison_naturality p g e hg i
    dsimp only [jE, l]
    simp only [Functor.map_comp, Category.assoc]
    rw [← hn]
  refine ⟨A, inferInstance, e, he, t, ht, I, inferInstance, inferInstance, jE, hjE, ?_⟩
  intro z
  let d := geometricPoint (Spec A) z
  have hz : (d ≫ g) (IsLocalRing.closedPoint
      (AlgebraicClosure ((Spec A).residueField z))) ∈
      splitTorus.geometricSelfCentralizingTorusLocus I Gp l := by
    change O.ι (a (d _)) ∈ splitTorus.geometricSelfCentralizingTorusLocus I Gp l
    exact (a _).property
  have hmres := splitTorus.isMaximalTorus_residueFibre_of_geometricFiberHom I Gp l hl _
    (splitTorus.isMaximalTorus_geometricFiberHom_of_mem I Gp l hGp hl _ hz)
  have hmfield := isMaximalTorus_fieldPoint_of_residueFibre
    (T := splitTorus.commGroupScheme (Spec R) I) (i := l) (d ≫ g) hmres
  have hmstd := splitTorus.isMaximalTorus_baseChangedHom_comp I Gp l g d hmfield
  have hmraw : IsMaximalTorus
      (T := (CommGroupScheme.baseChange d).obj (splitTorus.commGroupScheme (Spec A) I))
      ((baseChange d).map (jE ≫ (baseChange e).map i)) := by
    rw [hEq, Functor.map_comp]
    exact hmstd.comp_iso ((baseChange d).mapIso eG)
  exact IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange d).obj (splitTorus.commGroupScheme (Spec A) I))
    (T' := splitTorus.commGroupScheme _ I) (splitTorus.baseChangeIso d I).symm hmraw

end Langlands.GroupScheme
