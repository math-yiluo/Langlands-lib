import Langlands.Global.AdelicLeviFibreConstantTerm
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.GroupScheme.Rational.ReductiveParabolicContraction
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.Rational.SimultaneousStandardConjugation
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Cuspidality of relatively cuspidal Levi fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "pM(" J ")" => (fam.l J ≫ fam.p J)
local notation "rad(" J ")" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "Γ(" P ")" => parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)

variable (P : StandardIndex F G fam.i fam.ν)
  {L V : GroupScheme (Spec (CommRingCat.of F))} (p : L ⟶ fam.M P) (r : V ⟶ L)

omit [NumberField F] in
/-- Every proper radical of the specified Levi is rationally conjugate to
its intersection with the radical of a strictly smaller standard parabolic. -/
private theorem exists_conjugate_radical_of_proper (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hproper : SubgroupFunctor.range p ≠ ⊤) :
    ∃ Q : Idx, Q < P ∧ ∃ c : GroupScheme.rationalPoints (fam.M P),
      SubgroupFunctor.range (r ≫ p ≫ ((fam.M P).innerIso c).hom) = (rad(Q)).comap (pM(P)) := by
  let M := fam.M P
  have hM := (fam.isCompatible P).levi.isConnectedReductive
  let : IsAffineHom M.X.hom := hM.isAffineHom
  have hMc : IsClosedSubgroup (pM(P)) := (fam.isCompatible P).levi.isClosedSubgroup.comp
    (fam.isCompatible P).parabolic.isClosedSubgroup
  let : IsClosedImmersion (pM(P)).hom.hom.left := hMc
  have hrep : (standardLevi fam.i fam.ν P.val).IsRepresentedBy (pM(P)) :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible P).levi_eq⟩
  let iM := standardLeviTorusFactor fam.i fam.ν P.val hrep
  have hiM : IsMaximalSplitTorus iM :=
    fam.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor fam.i fam.ν P.val hrep hMc
  obtain ⟨hsimple, hνM, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
    F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic P.val P.2 M hM
    (pM(P)) hrep hMc
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  obtain ⟨χ, hχ⟩ := (parabolicDynamic F M hM L p hp.isClosedSubgroup).mp hp
  have hpRep : (Dynamic.parabolic χ).IsRepresentedBy p := ⟨Over.mono_of_mono_left _, hχ⟩
  have hrχ := Dynamic.range_comp_radical_eq_unipotent_of_reductive hM χ p hpRep r hr.1
  obtain ⟨c, J, ζ, hζ, hc⟩ := exists_innerIso_comp_eq_standardCocharacter
    smoothMaximalSplitTorusConjugacy hM hiM (ν := fam.ν)
    (relativeRootSystem F M hM fam.T iM hiM) hνM χ
  let e := M.innerIso c
  have hc' : χ ≫ e.hom = CommGroupScheme.groupHom ζ ≫ iM := hc
  have hJ : J ⊆ P.val := hsimple ▸ hζ.1
  let Q : Idx := ⟨J, hJ.trans P.2⟩
  have hStd := (standardCocharacter F M hM fam.T iM hiM fam.ν hνM J hζ.1).2 ζ hζ
  have hPar : Dynamic.parabolic χ = (standardParabolic iM fam.ν J).comap e.hom := by
    rw [hStd.1, ← hc']
    exact Dynamic.parabolic_eq_comap_of_iso χ e
  have hQ : Q < P := by
    refine lt_of_le_of_ne hJ (fun h => hproper ?_)
    have hj : J = P.val := congrArg Subtype.val h
    have htop : standardParabolic iM fam.ν P.val = ⊤ := by
      rw [← hsimple]
      exact (standardParabolicEndpoints F M hM fam.T iM hiM fam.ν hνM).2.2.1
    rw [hχ, hPar, hj, htop, SubgroupFunctor.comap_top]
  have hRes := (standardLeviStandardFamilies_inter fam.i fam.ν fam.connectedReductive
    fam.maximalSplit fam.generic P.val J P.2 Q.2 hM (pM(P)) hrep hMc).2.2
  rw [Set.inter_eq_right.mpr hJ, ← fam.range_radical_eq_standardUnipotent Q] at hRes
  have hU : Dynamic.unipotent χ = (standardUnipotent iM fam.ν J).comap e.hom := by
    rw [hStd.2.2, ← hc']
    exact Dynamic.unipotent_eq_comap_of_iso χ e
  have hOld : SubgroupFunctor.range (r ≫ p) = ((rad(Q)).comap (pM(P))).comap e.hom := by
    rw [hrχ, hU, hRes]
  let k := r ≫ p ≫ e.hom
  have hk : SubgroupFunctor.range (r ≫ p) = (SubgroupFunctor.range k).comap e.hom :=
    SubgroupFunctor.range_eq_comap_of_iso_square e (Iso.refl V) (by simp [k, Category.assoc])
  exact ⟨Q, hQ, c, ((SubgroupFunctor.eq_comap_iso_iff e).mp hk).symm.trans
    ((SubgroupFunctor.eq_comap_iso_iff e).mp hOld)⟩

/-- For a relatively cuspidal continuous function on one parabolic quotient,
every right translate restricted to the original Levi is intrinsically cuspidal. -/
def LeviFibreCuspidalityStatement : Prop :=
  ∀ (P : Idx) (f : A → ℂ), Continuous f → IsLeftInvariantUnder F G (Γ(P)) f →
    fam.IsCuspidalAlong P f → ∀ g : A, fam.IsLeviCuspidal P (fam.leviFibre P f g)

theorem leviFibreCuspidality : fam.LeviFibreCuspidalityStatement := by
  intro P f hf hInv hC g L V p r _ _ hp hr hproper
  let M := fam.M P
  obtain ⟨Q, hQ, c, hc⟩ := fam.exists_conjugate_radical_of_proper P p r hp hr hproper
  let e := M.innerIso c
  let j := r ≫ p
  let k := r ≫ p ≫ e.hom
  have hjc : IsClosedSubgroup j := hr.1.isClosedSubgroup.comp hp.isClosedSubgroup
  let : IsClosedImmersion j.hom.hom.left := hjc
  have hkc : IsClosedSubgroup k := by
    change IsClosedSubgroup (r ≫ p ≫ e.hom)
    rw [← Category.assoc]
    exact (IsClosedSubgroup.comp_iso_iff _ e).mpr hjc
  let : IsClosedImmersion k.hom.hom.left := hkc
  let W := SubgroupFunctor.range k
  let W' := SubgroupFunctor.range j
  let : IsClosed (adelicPoints F M W : Set (AdelicGroupPoints F M)) := isClosed_adelicPoints_range F M k
  let : IsClosed (adelicPoints F M W' : Set (AdelicGroupPoints F M)) := isClosed_adelicPoints_range F M j
  let : CompactSpace (RationalQuotient F M W) := compactSpace_rationalQuotient_range_unipotent F k
    hr.1.smooth hr.1.connectedSpace hr.1.isUnipotent
  have hW : W' = W.comap e.hom :=
    SubgroupFunctor.range_eq_comap_of_iso_square e (Iso.refl V) (by simp [j, k, Category.assoc])
  let φ : ContinuousRationalFunctions F M :=
    ⟨⟨fam.leviFibre P f g, fun q => fam.isLeftInvariantUnder_leviFibre P hInv g _ ⟨q, rfl⟩⟩,
      fam.continuous_leviFibre P hf g⟩
  have hzero (m : AdelicGroupPoints F M) : subgroupConstantTerm F k (fam.leviFibre P f g) m = 0 := by
    rw [fam.subgroupConstantTerm_leviFibre k hQ.le hc hf hInv, hC Q hQ]
    rfl
  funext m
  change subgroupConstantTerm F j (evaluate F M φ) m = 0
  rw [subgroupConstantTerm_eq_continuousConstantTerm j φ]
  have h := constantTerm_comap_innerIso F M c W W' hW φ (innerAdelicPoint F M c * m)
  rw [inv_mul_cancel_left, ← subgroupConstantTerm_eq_continuousConstantTerm k φ] at h
  exact h.symm.trans (hzero _)

end Langlands.Global.StandardParabolicFamily
