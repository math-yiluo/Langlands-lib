import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
import Langlands.Geometry.Building.KPTorusNormNaturality
import Langlands.Geometry.Building.CentralIsogenyCentralizer
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.CentralSurjection.TorusImage
import Langlands.GroupScheme.SimplyConnected.HomLift

/-! # Zero subgroups under central surjections -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building.Kottwitz

/-- Norm subgroup naturality is independent of the two splitting-field choices. -/
theorem map_torusNormIwahori_le_of_splitting_fields
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
    [FiniteDimensional (UnramifiedClosure F) E] [IsGalois (UnramifiedClosure F) E]
    [FiniteDimensional (UnramifiedClosure F) M] [IsGalois (UnramifiedClosure F) M]
    {T U : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    [IsAffine T.X.left] [IsAffine U.X.left] (f : T ⟶ U)
    (hE : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp))
    (hM : IsSplitTorus (baseChanged (UnramifiedClosure F) M U.toGrp)) :
    (torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T).map
        (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
      torusNormIwahori (UnramifiedClosure F) M (intermediateValuation F M) U := by
  let P := E ⊔ M
  have : FiniteDimensional (UnramifiedClosure F) P := inferInstance
  have : IsGalois (UnramifiedClosure F) P := inferInstance
  rw [← torusNormIwahori_eq_of_le F E P T le_sup_left hE,
    ← torusNormIwahori_eq_of_le F M P U le_sup_right hM]
  exact map_torusNormIwahori_le (UnramifiedClosure F) P
    (intermediateValuation F P) f

/-- Every group homomorphism preserves the image of the simply connected derived cover. -/
theorem map_simplyConnectedImage_le_of_hom
    {k : Type u} [Field k]
    {G H D DH C CH : GroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} {π : C ⟶ D} {dH : DH ⟶ H} {πH : CH ⟶ DH}
    (h : IsSimplyConnectedDerivedCover d π)
    (hH : IsSimplyConnectedDerivedCover dH πH) (f : G ⟶ H) :
    (Building.simplyConnectedImage d π).map (rationalPoints.map f) ≤
      Building.simplyConnectedImage dH πH := by
  let fD := h.isDerivedSubgroup.map hH.isDerivedSubgroup f
  have hDH := hH.isSimplyConnectedCover.isSemisimple.isConnectedReductive
  let : IsAffineHom DH.X.hom := hDH.isAffineHom
  have hsep : IsSeparated DH.X.hom := inferInstance
  let a := SimplyConnectedHomLift.liftHom (π ≫ fD) πH
    hH.isSimplyConnectedCover.isCentralIsogeny
    h.isSimplyConnectedCover.isSimplyConnected
    hH.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive hsep
  have ha : a ≫ πH = π ≫ fD := SimplyConnectedHomLift.liftHom_comp _ _ _ _ _ _
  have hcomp : a ≫ πH ≫ dH = π ≫ d ≫ f := by
    rw [← Category.assoc, ha, Category.assoc, IsDerivedSubgroup.map_comp]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  refine ⟨rationalPoints.map a c, ?_⟩
  have hc := congrArg (fun m : C ⟶ H => c ≫ m.hom.hom) hcomp
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using hc

/-- A commuting map of the chosen maximal tori preserves the two zero subgroups. -/
theorem map_zeroPoints_le_of_torus_square
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G) (EH : UnramifiedZeroDatum F H)
    (f : G ⟶ H) (t : E.T ⟶ EH.T)
    (hsquare : CommGroupScheme.groupHom t ≫ EH.i = E.i ≫ f) :
    E.zeroPoints.map (rationalPoints.map f) ≤ EH.zeroPoints := by
  rw [UnramifiedZeroDatum.zeroPoints, Subgroup.map_sup]
  apply sup_le
  · exact (map_simplyConnectedImage_le_of_hom
      E.isSimplyConnectedDerivedCover EH.isSimplyConnectedDerivedCover f).trans
        EH.simplyConnectedImage_le_zeroPoints
  · have htorus := map_torusNormIwahori_le_of_splitting_fields F E.L EH.L t
      E.isSplitTorus EH.isSplitTorus
    apply le_trans _ EH.map_torusIwahori_le_zeroPoints
    have hpoints : (rationalPoints.map f).comp (rationalPoints.map E.i) =
        (rationalPoints.map EH.i).comp
          (rationalPoints.map (CommGroupScheme.groupHom t)) := by
      apply MonoidHom.ext
      intro x
      simpa only [MonoidHom.comp_apply, rationalPoints.map_apply,
        Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun m : E.T.toGrp ⟶ H => x ≫ m.hom.hom) hsquare.symm
    rw [Subgroup.map_map, hpoints, ← Subgroup.map_map]
    exact Subgroup.map_mono htorus

/-- A central surjection to a quasi-split group carries a maximally split maximal
torus into a maximally split maximal torus. -/
theorem exists_maximallySplitTorus_square_of_centralSurjection
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsQuasiSplit H)
    (p : G ⟶ H) [Surjective p.hom.hom.left] (hp : IsCentral (kernelι p))
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsMaximallySplitMaximalTorus i) :
    ∃ (U : CommGroupScheme (Spec (CommRingCat.of k))) (j : U.toGrp ⟶ H)
      (t : T ⟶ U), IsMaximallySplitMaximalTorus j ∧
        CommGroupScheme.groupHom t ≫ j = i ≫ p := by
  obtain ⟨hi, A, a, fA, ha, hfA⟩ := hi
  obtain ⟨A', a', tA, ha', hsquare, hflat, hsurj, _⟩ :=
    exists_maximalSplitTorus_image hG hH.isConnectedReductive p hp ha
  let : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
  let : Smooth H.X.hom := hH.isConnectedReductive.smooth
  obtain ⟨U, j, hj, fA', hfA'⟩ :=
    exists_maximalTorus_extension_of_finiteType H a' ha'.1.1.isTorus ha'.1.2
  have hrepr := quasiSplitMaximalTorusCentralizer k H hH U A' j a' fA' hj ha' hfA'
  have hcent := range_le_torusCentralizer_of_factor a i fA hfA
  let : Flat (CommGroupScheme.groupHom tA).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom tA).hom.hom.left := hsurj
  have hle : SubgroupFunctor.range (i ≫ p) ≤ torusCentralizer a' := by
    rintro V _ ⟨z, rfl⟩
    change (z ≫ i.hom.hom) ≫ p.hom.hom ∈ (torusCentralizer a').carrier V
    exact TorusCoverTransport.map_mem_torusCentralizer p tA hsquare
      (hcent V ⟨z, rfl⟩)
  exact ⟨U, j, Additive.ofMul (hrepr.factorHom (i ≫ p) hle),
    ⟨hj, A', a', fA', ha', hfA'⟩, hrepr.factorHom_comp _ _⟩

/-- Central surjections preserve the zero subgroups over the unramified closure. -/
theorem map_zeroPoints_le_of_centralSurjection
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G) (EH : UnramifiedZeroDatum F H)
    (p : G ⟶ H) [Surjective p.hom.hom.left] (hp : IsCentral (kernelι p)) :
    E.zeroPoints.map (rationalPoints.map p) ≤ EH.zeroPoints := by
  have hH := EH.isSimplyConnectedDerivedCover.isConnectedReductive
  have hqs : IsQuasiSplit H :=
    unramifiedQuasiSplit_of_henselianDiscrete
      (henselianDiscreteQuasiSplitReduction
        (quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient)) F H hH
  obtain ⟨U, j, t, hj, hsquare⟩ :=
    exists_maximallySplitTorus_square_of_centralSurjection
      E.isSimplyConnectedDerivedCover.isConnectedReductive hqs p hp E.i
        E.isMaximallySplitMaximalTorus
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsClosedImmersion j.hom.hom.left := hj.1.2.1
  let : IsAffine U.X.left := isAffine_of_isAffineHom j.hom.hom.left
  obtain ⟨L, hfin, hgal, hsplit⟩ :=
    exists_finiteGaloisSplittingField_inside (SeparableClosure F) U.toGrp hj.1.1
  let E' : UnramifiedZeroDatum F H := {
    T := U
    i := j
    isMaximallySplitMaximalTorus := hj
    L := L
    finiteDimensional := hfin
    isGalois := hgal
    isSplitTorus := hsplit
    D := EH.D
    C := EH.C
    d := EH.d
    π := EH.π
    isSimplyConnectedDerivedCover := EH.isSimplyConnectedDerivedCover }
  have hle := map_zeroPoints_le_of_torus_square E E' p t hsquare
  rwa [unramifiedZeroPointsIndependence F H E' EH] at hle

end Langlands.Geometry.Building.Kottwitz
