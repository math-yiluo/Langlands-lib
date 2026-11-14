import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
import Langlands.Geometry.Building.KPMinimalLeviZeroComparisonProof
import Langlands.GroupScheme.SimplyConnected.HomLift
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Rational.FiniteFieldMaximalTorusTransporterReduction
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageProof
import Langlands.GroupScheme.SimplyConnected.FieldExtensionProof

/-! # Zero subgroups and split-torus centralizers over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

/-- An arbitrary homomorphism carries the simply connected image into the
simply connected image, for every pair of supplied derived covers. -/
theorem map_simplyConnectedImage_le_of_hom
    {k : Type u} [Field k]
    {G H D E C Q : GroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} {π : C ⟶ D} {e : E ⟶ H} {ρ : Q ⟶ E}
    (hG : IsSimplyConnectedDerivedCover d π)
    (hH : IsSimplyConnectedDerivedCover e ρ) (f : G ⟶ H) :
    (simplyConnectedImage d π).map (rationalPoints.map f) ≤
      simplyConnectedImage e ρ := by
  let δ := hG.isDerivedSubgroup.map hH.isDerivedSubgroup f
  let q := SimplyConnectedHomLift.liftHom (π ≫ δ) ρ
    hH.isSimplyConnectedCover.isCentralIsogeny
    hG.isSimplyConnectedCover.isSimplyConnected
    hH.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
    hH.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isSeparated
  have hq : q ≫ ρ = π ≫ δ :=
    SimplyConnectedHomLift.liftHom_comp _ _ _ _ _ _
  have hcomp : q ≫ ρ ≫ e = π ≫ d ≫ f := by
    rw [← Category.assoc, hq, Category.assoc,
      IsDerivedSubgroup.map_comp]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  refine ⟨rationalPoints.map q c, ?_⟩
  have hc := congrArg (fun a => rationalPoints.map a c) hcomp
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using hc

/-- Extension of scalars preserves the simply connected image, for any
supplied derived covers on both sides. -/
theorem rationalExtend_mem_simplyConnectedImage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G D C : GroupScheme (Spec (CommRingCat.of k))}
    {DK CK : GroupScheme (Spec (CommRingCat.of K))}
    {d : D ⟶ G} {π : C ⟶ D}
    {dK : DK ⟶ baseChanged k K G} {πK : CK ⟶ DK}
    (h : IsSimplyConnectedDerivedCover d π)
    (hK : IsSimplyConnectedDerivedCover dK πK)
    {g : rationalPoints G} (hg : g ∈ simplyConnectedImage d π) :
    rationalExtend k K G g ∈ simplyConnectedImage dK πK := by
  let b := baseMap k K
  let : IsAffineHom G.X.hom := h.isConnectedReductive.isAffineHom
  have hBC : IsSimplyConnectedDerivedCover
      ((GroupScheme.baseChange b).map d) ((GroupScheme.baseChange b).map π) :=
    ⟨connectedReductiveFieldExtensionStatement k K G h.isConnectedReductive,
      h.isDerivedSubgroup.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G),
      isSimplyConnectedCover_fieldExtension k K C D π h.isSimplyConnectedCover⟩
  rw [← Building.simplyConnectedImage_eq hBC hK]
  obtain ⟨c, rfl⟩ := hg
  refine ⟨rationalExtend k K C c, ?_⟩
  rw [← Functor.map_comp, ← rationalExtend_map]

/-- A maximally split maximal torus of a split-torus centralizer is also a
maximally split maximal torus of the ambient group. -/
theorem isMaximallySplitMaximalTorus_comp_centralizer
    {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} (ha : IsSplitSubtorus a)
    {j : M ⟶ G} (hj : (torusCentralizer a).IsRepresentedBy j)
    (hG : IsConnectedReductive G) (hM : IsConnectedReductive M)
    {t : T.toGrp ⟶ M} (ht : IsMaximallySplitMaximalTorus t) :
    IsMaximallySplitMaximalTorus (t ≫ j) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth M.X.hom := hM.smooth
  have hjc := ha.1.isClosedSubgroup_torusCentralizer a hj
  let aM := torusCentralizerFactor a hj
  have haM : IsCentralSplitTorus aM :=
    ha.isCentralSplitTorus_torusCentralizerFactor hj hjc
  have haMj : aM ≫ j = a := torusCentralizerFactor_comp a hj
  obtain ⟨f, hf⟩ := haM.2.exists_factor_of_isMaximalTorus ha.1.isTorus ht.1
  refine ⟨⟨ht.1.1, ht.1.2.1.comp hjc, ?_⟩, ?_⟩
  · intro T' t' q hT' ht' hqt'
    have hfac : (f ≫ q) ≫ t' = a := by
      rw [Category.assoc, hqt', ← Category.assoc, hf, haMj]
    let tM := hj.factorHom t' (range_le_torusCentralizer_of_factor a t' (f ≫ q) hfac)
    have htM : tM ≫ j = t' := hj.factorHom_comp _ _
    apply ht.1.2.2 T' tM q hT'
      (IsClosedSubgroup.of_comp hjc (by rw [htM]; exact ht'))
    apply hj.hom_ext
    rw [Category.assoc, htM, hqt']
  · obtain ⟨B, b, g, hb, hgt⟩ := ht.2
    obtain ⟨r, hr⟩ := hb.exists_factor_of_commute ha.1 aM
      (haM.2.commute_values b)
    have hrj : r ≫ (b ≫ j) = a := by
      rw [← Category.assoc, hr, haMj]
    have hbG : IsMaximalSplitTorus (b ≫ j) :=
      hb.comp_of_torusCentralizer_le_range hjc
        ((torusCentralizer_le_of_factor (b ≫ j) a r hrj).trans hj.2.ge)
    exact ⟨B, b ≫ j, g, hbG, by rw [← Category.assoc, hgt]⟩

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G M : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  {A : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  {a : A.toGrp ⟶ G} {j : M ⟶ G}

/-- Use a centralizer's torus, with the ambient group's supplied derived cover. -/
def ofCentralizer (E : UnramifiedZeroDatum F G) (EM : UnramifiedZeroDatum F M)
    (ha : IsSplitSubtorus a) (hj : (torusCentralizer a).IsRepresentedBy j) :
    UnramifiedZeroDatum F G where
  T := EM.T
  i := EM.i ≫ j
  isMaximallySplitMaximalTorus :=
    isMaximallySplitMaximalTorus_comp_centralizer ha hj
      E.isSimplyConnectedDerivedCover.isConnectedReductive
      EM.isSimplyConnectedDerivedCover.isConnectedReductive EM.isMaximallySplitMaximalTorus
  L := EM.L
  isSplitTorus := EM.isSplitTorus
  D := E.D
  C := E.C
  d := E.d
  π := E.π
  isSimplyConnectedDerivedCover := E.isSimplyConnectedDerivedCover

/-- The centralizer zero subgroup maps into the ambient zero subgroup. -/
theorem map_zeroPoints_centralizer_le
    (E : UnramifiedZeroDatum F G) (EM : UnramifiedZeroDatum F M)
    (ha : IsSplitSubtorus a) (hj : (torusCentralizer a).IsRepresentedBy j) :
    EM.zeroPoints.map (rationalPoints.map j) ≤ E.zeroPoints := by
  rw [unramifiedZeroPointsIndependence F G E (E.ofCentralizer EM ha hj)]
  rw [zeroPoints, Subgroup.map_sup]
  apply sup_le
  · exact (map_simplyConnectedImage_le_of_hom EM.isSimplyConnectedDerivedCover
      E.isSimplyConnectedDerivedCover j).trans le_sup_left
  · have hmap : rationalPoints.map (EM.i ≫ j) =
        (rationalPoints.map j).comp (rationalPoints.map EM.i) := by
      apply MonoidHom.ext
      intro x
      rfl
    rw [Subgroup.map_map, ← hmap]
    exact (E.ofCentralizer EM ha hj).map_torusIwahori_le_zeroPoints

/-- Upstairs zero points in the centralizer's character kernel are exactly
the centralizer zero points. -/
theorem zeroPoints_comap_centralizer_inf_characterValuationKernel
    (E : UnramifiedZeroDatum F G) (EM : UnramifiedZeroDatum F M)
    (ha : IsSplitSubtorus a) (hj : (torusCentralizer a).IsRepresentedBy j) :
    E.zeroPoints.comap (rationalPoints.map j) ⊓
        characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) M =
      EM.zeroPoints := by
  apply le_antisymm
  · rintro z ⟨hzG, hzNorm⟩
    change rationalPoints.map j z ∈ E.zeroPoints at hzG
    rw [unramifiedZeroPointsIndependence F G E (E.ofCentralizer EM ha hj)] at hzG
    obtain ⟨c, hc, t, ht, heq⟩ :=
      (E.ofCentralizer EM ha hj).mem_zeroPoints_iff.mp hzG
    have htM : rationalPoints.map EM.i t ∈ EM.zeroPoints :=
      EM.map_torusIwahori_le_zeroPoints ⟨t, ht, rfl⟩
    have heq' : c * rationalPoints.map j (rationalPoints.map EM.i t) =
        rationalPoints.map j z := by
      change c * rationalPoints.map (EM.i ≫ j) t = _ at heq
      simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using heq
    have hdiff : rationalPoints.map j (z * (rationalPoints.map EM.i t)⁻¹) = c := by
      rw [map_mul, map_inv, ← heq', mul_inv_cancel_right]
    have hcover : z * (rationalPoints.map EM.i t)⁻¹ ∈
        (Building.simplyConnectedImage E.d E.π).comap (rationalPoints.map j) := by
      change rationalPoints.map j (z * (rationalPoints.map EM.i t)⁻¹) ∈
        Building.simplyConnectedImage E.d E.π
      rw [hdiff]
      exact hc
    have hnorm : z * (rationalPoints.map EM.i t)⁻¹ ∈
        characterValuationKernel (LocalGalois.Separable.fixedFieldValuation F) M :=
      Subgroup.mul_mem _ hzNorm
        (Subgroup.inv_mem _ (EM.zeroPoints_le_characterValuationKernel htM))
    have hzero := coverImage_inf_characterValuationKernel_le_zeroPoints
      cocenterQuotientExistence splitTorusCentralizerCocenterInduced
      inducedTorusIwahori splitTorusCentralizerCoverPreimage
      E.isSimplyConnectedDerivedCover.isConnectedReductive
      E.isSimplyConnectedDerivedCover.isDerivedSubgroup
      E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected
      E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
      ha hj EM ⟨hcover, hnorm⟩
    simpa only [inv_mul_cancel_right] using EM.zeroPoints.mul_mem hzero htM
  · refine le_inf ?_ EM.zeroPoints_le_characterValuationKernel
    intro z hz
    exact E.map_zeroPoints_centralizer_le EM ha hj ⟨z, hz, rfl⟩

end UnramifiedZeroDatum

namespace ZeroSubgroupDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G}
  (Z0 : ZeroSubgroupDatum i j)
  (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))

/-- Scalar extension maps every actual downstairs zero point to an upstairs
zero point, for every supplied pair of zero data. -/
theorem zeroSubgroup_le_comap_unramifiedZeroPoints :
    Z0.zeroSubgroup ≤
      E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) := by
  apply sup_le
  · intro g hg
    exact E.simplyConnectedImage_le_zeroPoints
      (rationalExtend_mem_simplyConnectedImage F (UnramifiedClosure F)
        Z0.isSimplyConnectedDerivedCover E.isSimplyConnectedDerivedCover hg)
  · let b := baseMap F (UnramifiedClosure F)
    have hSK : IsSplitSubtorus (T := (CommGroupScheme.baseChange b).obj S)
        ((GroupScheme.baseChange b).map i) :=
      ⟨Z0.isMaximalSplitTorus.isSplitSubtorus.1.baseChange b,
        Z0.isMaximalSplitTorus.isSplitSubtorus.2.baseChange b⟩
    have hZK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj S)
        ((GroupScheme.baseChange b).map i)).IsRepresentedBy
          ((GroupScheme.baseChange b).map j) := by
      rw [torusCentralizer_baseChange]
      exact Z0.isRepresentedBy.baseChange b
    rintro _ ⟨z, hz, rfl⟩
    change rationalExtend F (UnramifiedClosure F) G (rationalPoints.map j z) ∈ E.zeroPoints
    rw [rationalExtend_map]
    exact E.map_zeroPoints_centralizer_le Z0.centralizerDatum hSK hZK
      ⟨rationalExtend F (UnramifiedClosure F) Z z, hz, rfl⟩

/-- The required unramified descent equality already holds after restricting
to norm-one points of the minimal Levi subgroup. -/
theorem comap_unramifiedZeroPoints_inf_centralizerNormKernel :
    (E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G)).comap
        (rationalPoints.map j) ⊓ Plancherel.rationalCommonNormKernel Z =
      Z0.centralizerZero := by
  let : IsAffineHom G.X.hom := Z0.isSimplyConnectedDerivedCover.isConnectedReductive.isAffineHom
  let : IsAffineHom Z.X.hom := Z0.isClosedSubgroup_centralizer.isAffineHom
  let : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  let b := baseMap F (UnramifiedClosure F)
  have hSK : IsSplitSubtorus (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i) :=
    ⟨Z0.isMaximalSplitTorus.isSplitSubtorus.1.baseChange b,
      Z0.isMaximalSplitTorus.isSplitSubtorus.2.baseChange b⟩
  have hZK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj S)
      ((GroupScheme.baseChange b).map i)).IsRepresentedBy
        ((GroupScheme.baseChange b).map j) := by
    rw [torusCentralizer_baseChange]
    exact Z0.isRepresentedBy.baseChange b
  apply le_antisymm
  · rintro z ⟨hzG, hzNorm⟩
    change rationalExtend F (UnramifiedClosure F) G (rationalPoints.map j z) ∈ E.zeroPoints
      at hzG
    rw [rationalExtend_map] at hzG
    rw [← characterValuationKernelDescent_proof F Z] at hzNorm
    change rationalExtend F (UnramifiedClosure F) Z z ∈ Z0.centralizerDatum.zeroPoints
    rw [← E.zeroPoints_comap_centralizer_inf_characterValuationKernel
      Z0.centralizerDatum hSK hZK]
    exact ⟨hzG, hzNorm⟩
  · refine le_inf ?_ Z0.centralizerZero_le_rationalCommonNormKernel
    intro z hz
    exact Z0.zeroSubgroup_le_comap_unramifiedZeroPoints E
      (Z0.map_centralizerZero_le_zeroSubgroup ⟨z, hz, rfl⟩)

end ZeroSubgroupDatum

end Langlands.Geometry.Building
