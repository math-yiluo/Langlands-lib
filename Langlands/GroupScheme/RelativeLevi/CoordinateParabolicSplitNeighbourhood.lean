import Langlands.GroupScheme.RelativeLevi.SplitTorusDynamicNeighbourhood
import Langlands.GroupScheme.Reductive.EtaleLocalSplitProof
import Langlands.GroupScheme.Reductive.AffineRootDatumTransport
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Reductive.AffineRegularBorel

/-! # Principal split face-chart neighborhoods in a prescribed parabolic torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.RelativeLevi

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (p : H ⟶ G) (t : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
  (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) (t ≫ p))

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance (A : Type u) [CommRing A] [Algebra R A] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

include hG hp hmax in
/-- Near a prescribed point, the parabolic is presented by one fixed integral
coordinate cocharacter of the prescribed torus. -/
theorem exists_open_coordinateParabolicPresentation (s : Spec (CommRingCat.of R)) :
    ∃ (wt : I → ℤ) (V : Scheme.{u}) (a : V ⟶ Spec (CommRingCat.of R)),
      IsOpenImmersion a ∧ s ∈ Set.range a ∧
      (Dynamic.parabolic (Dynamic.baseChangeCocharacter a
        (AffineRegularBorel.cocharacter (t ≫ p) wt))).IsRepresentedBy
          ((GroupScheme.baseChange a).map p) := by
  let : Smooth G.X.hom := hG.smooth
  let : GeometricallyConnected G.X.hom := hG.geometricallyConnected
  let : Smooth H.X.hom := hp.smooth
  let : IsAffineHom H.X.hom := hp.isAffineHom
  let : GeometricallyConnected H.X.hom := hp.geometricallyConnected hG
  let : Mono p.hom.hom := hp.mono
  let : Mono p.hom.hom.left := Over.mono_left_of_mono _
  let k := (Spec (CommRingCat.of R)).residueField s
  let b := (Spec (CommRingCat.of R)).fromSpecResidueField s
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I
  have hTP : SubgroupFunctor.range ((GroupScheme.baseChange b).map (t ≫ p)) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map p) := by
    rw [Functor.map_comp]
    exact SubgroupFunctor.range_comp_le _ _
  obtain ⟨ν, hν⟩ := exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup
    (T := (CommGroupScheme.baseChange b).obj T)
    (hG.isConnectedReductive_residueFiber s) ((GroupScheme.baseChange b).map p)
    (hp.residueFiber s) ((GroupScheme.baseChange b).map (t ≫ p)) (hmax s) hTP
  let νk := ν ≫ (splitTorus.commBaseChangeIso b I).hom
  let wt := splitTorus.cocharacterLatticeEquiv k I νk
  let νR := splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I wt
  have hνR : cocharacterLattice.baseChange b T νR = ν := by
    apply (cancel_mono (splitTorus.commBaseChangeIso b I).hom).mp
    rw [splitTorus.exponentCocharacter_baseChange]
    change splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I wt = νk
    rw [splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
    exact (splitTorus.cocharacterLatticeEquiv k I).symm_apply_apply νk
  let χH := CommGroupScheme.groupHom νR ≫ t
  have hχ : χH ≫ p = AffineRegularBorel.cocharacter (t ≫ p) wt := by
    simp only [χH, νR, AffineRegularBorel.cocharacter, Category.assoc]
  have hfield : SubgroupFunctor.range ((GroupScheme.baseChange b).map p) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter b (χH ≫ p)) := by
    have he : Dynamic.baseChangeCocharacter b (χH ≫ p) =
        CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map (t ≫ p) := by
      rw [hχ]
      change Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom νR ≫ (t ≫ p)) = _
      rw [baseChangeCocharacter_torus_comp b T (t ≫ p) νR, hνR]
      rfl
    exact hν.trans (congrArg Dynamic.parabolic he.symm)
  have hb : b (IsLocalRing.closedPoint k) = s := Scheme.fromSpecResidueField_apply _ _
  have hpc : IsClosedSubgroup ((GroupScheme.baseChange
      ((Spec (CommRingCat.of R)).fromSpecResidueField
        (b (IsLocalRing.closedPoint k)))).map p) := by
    rw [hb]
    exact (hp.residueFiber s).isClosedSubgroup
  obtain ⟨V, a, ha, bV, hbV, hpres⟩ :=
    Dynamic.exists_local_presentation_of_fieldPoint p χH b hpc hfield
  refine ⟨wt, V, a, ha, ?_, ?_⟩
  · refine ⟨bV (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply, hbV]
    exact hb
  · rw [hχ] at hpres
    exact ⟨by
      change Mono ((Over.pullback a).map p.hom.hom)
      infer_instance, hpres⟩

/-- Actual simultaneous principal data: one fixed coordinate cocharacter,
a full fibrewise root datum, free actual root lines, and the original
parabolic presentation. -/
structure PrincipalParabolicSplitData (s : Spec (CommRingCat.of R)) where
  element : R
  avoids : element ∉ s.asIdeal
  weight : I → ℤ
  rootType : Type u
  rootDatum : RootDatum rootType (I → ℤ) (I → ℤ)
  fibrewise : IsFibrewiseRootDatumOf I
    ((GroupScheme.baseChange (algebraBaseMap R (Localization.Away element))).obj G)
    (splitTorus.baseChangeHom (K := Localization.Away element) G I (t ≫ p)) rootDatum
  free : ∀ a : rootType, Nonempty
    (splitTorus.exponentWeightSpace I
      ((GroupScheme.baseChange (algebraBaseMap R (Localization.Away element))).obj G)
      (splitTorus.baseChangeHom (K := Localization.Away element) G I (t ≫ p))
      (rootDatum.root a) ≃ₗ[CommRingCat.of (Localization.Away element)]
        CommRingCat.of (Localization.Away element))
  represents : (Dynamic.parabolic (AffineRegularBorel.cocharacter
    (splitTorus.baseChangeHom (K := Localization.Away element) G I (t ≫ p)) weight)).IsRepresentedBy
      ((GroupScheme.baseChange (algebraBaseMap R (Localization.Away element))).map p)

include hG hp hmax in
/-- All actual split data and the fixed-coordinate dynamic presentation hold
on one principal neighborhood through the prescribed point. -/
theorem nonempty_principalParabolicSplitData (s : Spec (CommRingCat.of R)) :
    Nonempty (PrincipalParabolicSplitData p t s) := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨wt, V, a, ha, hs, hpres⟩ :=
    exists_open_coordinateParabolicPresentation p t hG hp hmax s
  let : IsOpenImmersion a := ha
  obtain ⟨J, hJ, P, U, hred, hU, hsU, hrank, hP⟩ :=
    exists_open_coordinateRootDatum I G hG (t ≫ p) hmax s
  let : Finite J := hJ
  have hUa : IsOpen (U ∩ Set.range a) := hU.inter a.isOpenMap.isOpen_range
  obtain ⟨r, hr, hsub, hfree⟩ := splitTorus.exists_principal_exponentWeightLines
    I G (t ≫ p) P.root s (U ∩ Set.range a) hUa ⟨hsU, hs⟩ hrank
  let A := Localization.Away r
  let q := algebraBaseMap R A
  have hqrange : Set.range q ⊆ U ∩ Set.range a := by
    change Set.range (PrimeSpectrum.comap (algebraMap R A)) ⊆ U ∩ Set.range a
    rw [PrimeSpectrum.localization_away_comap_range A r]
    exact hsub
  let qV : Spec (CommRingCat.of A) ⟶ V :=
    IsOpenImmersion.lift a q (fun x hx => (hqrange hx).2)
  have hfac : qV ≫ a = q := IsOpenImmersion.lift_fac _ _ _
  have hroot : IsFibrewiseRootDatumOf I ((GroupScheme.baseChange q).obj G)
      (splitTorus.baseChangeHom (K := A) G I (t ≫ p)) P :=
    fibrewiseRootDatumOf_principalRestriction I G (t ≫ p) P hred U hP r
      (fun x hx => (hsub hx).1)
  have hpr := Dynamic.pullbackCocharacter_presents a qV q hfac p
    (Dynamic.baseChangeCocharacter a (AffineRegularBorel.cocharacter (t ≫ p) wt)) hpres.2
  rw [Dynamic.pullbackCocharacter, Dynamic.baseChangeCocharacter_tower] at hpr
  have hco : Dynamic.baseChangeCocharacter q (AffineRegularBorel.cocharacter (t ≫ p) wt) =
      AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I (t ≫ p)) wt :=
    splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange I G (t ≫ p) wt q
  rw [hco] at hpr
  exact ⟨⟨r, hr, wt, J, P, hroot, hfree, (hp.baseChange hG q).mono, hpr⟩⟩

/-- Choose the proved actual principal split data for the prescribed torus. -/
def principalParabolicSplitAt (s : Spec (CommRingCat.of R)) :
    PrincipalParabolicSplitData p t s :=
  Classical.choice (nonempty_principalParabolicSplitData p t hG hp hmax s)

end Langlands.GroupScheme.RelativeLevi
