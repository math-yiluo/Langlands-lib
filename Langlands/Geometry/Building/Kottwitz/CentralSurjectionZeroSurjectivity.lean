import Langlands.Geometry.Building.Kottwitz.CentralSurjectionZero
import Langlands.Geometry.Building.KPTorusIwahoriSurjectivityProof
import Langlands.GroupScheme.CentralIsogeny.PerfectComposition
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.Torus.SmoothConnectedKernelCocharacters
import Langlands.GroupScheme.Torus.CommonFiniteGaloisSplitting
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange

/-! # Surjectivity on zero subgroups through torus-kernel central quotients -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building.Kottwitz

/-- A group-scheme map carries the whole source zero subgroup onto the target
zero subgroup, for the specified defining data. -/
def MapsZeroPointsOnto
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G) (EH : UnramifiedZeroDatum F H)
    (p : G ⟶ H) : Prop :=
  E.zeroPoints.map (rationalPoints.map p) = EH.zeroPoints

/-- A central surjection maps the simply connected image onto the target image. -/
theorem map_simplyConnectedImage_eq_of_centralSurjection
    {k : Type u} [Field k]
    {G H D DH C CH : GroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} {π : C ⟶ D} {dH : DH ⟶ H} {πH : CH ⟶ DH}
    (h : IsSimplyConnectedDerivedCover d π)
    (hH : IsSimplyConnectedDerivedCover dH πH)
    (p : G ⟶ H) [Surjective p.hom.hom.left] (hp : IsCentral (kernelι p)) :
    (Building.simplyConnectedImage d π).map (rationalPoints.map p) =
      Building.simplyConnectedImage dH πH := by
  apply le_antisymm (map_simplyConnectedImage_le_of_hom h hH p)
  let pD := h.isDerivedSubgroup.map hH.isDerivedSubgroup p
  have hpD : IsCentralIsogeny pD :=
    h.isDerivedSubgroup.isCentralIsogeny_map hH.isDerivedSubgroup p
      h.isConnectedReductive hH.isConnectedReductive hp
  have hcomp : IsCentralIsogeny (π ≫ pD) :=
    IsCentralIsogeny.comp_of_derivedSubgroup_eq_top
      (semisimplePerfect k C h.isSimplyConnectedCover.isSimplyConnected.isSemisimple)
      h.isSimplyConnectedCover.isCentralIsogeny hpD
  obtain ⟨b, hb, _⟩ := hH.isSimplyConnectedCover.universal C (π ≫ pD)
    h.isSimplyConnectedCover.isSimplyConnected.isSemisimple hcomp
  rintro _ ⟨c, rfl⟩
  refine ⟨rationalPoints.map (π ≫ d) (rationalPoints.map b c),
    ⟨rationalPoints.map b c, rfl⟩, ?_⟩
  have hbc : b ≫ π ≫ d ≫ p = πH ≫ dH := by
    rw [← IsDerivedSubgroup.map_comp h.isDerivedSubgroup hH.isDerivedSubgroup p,
      ← Category.assoc π pD dH, ← Category.assoc b (π ≫ pD) dH, hb]
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun m : CH ⟶ H => c ≫ m.hom.hom) hbc

/-- In a compatible maximal-torus square, a central torus kernel remains a torus kernel. -/
theorem isTorus_kernel_of_central_torus_square
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (p : G ⟶ H) (hp : IsCentral (kernelι p)) (hker : IsTorus (kernel p))
    {T U : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) (t : T ⟶ U)
    (hi : IsMaximalTorus i) (hj : IsClosedSubgroup j)
    (hsquare : CommGroupScheme.groupHom t ≫ j = i ≫ p) :
    IsTorus (kernel (CommGroupScheme.groupHom t)) := by
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hself := maximalTorusCentralizer k G hG T i hi
  have hrepr : (torusCentralizer i).IsRepresentedBy i := ⟨inferInstance, hself.symm⟩
  have hle : SubgroupFunctor.range (kernelι p) ≤ torusCentralizer i := by
    rintro V _ ⟨z, rfl⟩
    exact center_le_torusCentralizer i V (hp V z)
  let r : kernel p ⟶ T.toGrp := hrepr.factorHom (kernelι p) hle
  have hr : r ≫ i = kernelι p := hrepr.factorHom_comp _ _
  have : Mono r.hom.hom := by
    have hmono : Mono (r.hom.hom ≫ i.hom.hom) := by
      rw [← Grp.comp_hom_hom, hr]
      infer_instance
    exact mono_of_mono r.hom.hom i.hom.hom
  have heq : SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom t)) =
      SubgroupFunctor.range r := by
    apply SubgroupFunctor.ext
    intro V
    apply Subgroup.ext
    intro x
    rw [mem_range_kernelι_iff]
    constructor
    · intro hx
      have hxp : (x ≫ i.hom.hom) ≫ p.hom.hom = 1 := by
        rw [Category.assoc, ← Grp.comp_hom_hom, ← hsquare,
          Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
      obtain ⟨z, hz⟩ := (mem_range_kernelι_iff p (x ≫ i.hom.hom)).mpr hxp
      refine ⟨z, ?_⟩
      apply (cancel_mono i.hom.hom).mp
      change (z ≫ r.hom.hom) ≫ i.hom.hom = x ≫ i.hom.hom
      change z ≫ (kernelι p).hom.hom = x ≫ i.hom.hom at hz
      rw [Category.assoc, ← Grp.comp_hom_hom, hr, hz]
    · rintro ⟨z, rfl⟩
      change (z ≫ r.hom.hom) ≫ (CommGroupScheme.groupHom t).hom.hom = 1
      apply (cancel_mono j.hom.hom).mp
      rw [MonObj.one_comp, Category.assoc, ← Grp.comp_hom_hom, hsquare,
        Grp.comp_hom_hom, ← Category.assoc, Category.assoc z,
        ← Grp.comp_hom_hom, hr]
      exact (mem_range_kernelι_iff p _).mp ⟨z, rfl⟩
  exact IsTorus.of_iso (KernelRepresentative.iso (CommGroupScheme.groupHom t) r heq) hker

/-- A central surjection is surjective on a compatible split maximal-torus restriction. -/
theorem flat_surjective_of_split_maximal_torus_square
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (p : G ⟶ H) [Surjective p.hom.hom.left] (hp : IsCentral (kernelι p))
    {T U : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) (t : T ⟶ U)
    (hi : IsMaximalTorus i) (hj : IsClosedSubgroup j)
    (hT : IsSplitTorus T.toGrp) (hU : IsSplitTorus U.toGrp)
    (hsquare : CommGroupScheme.groupHom t ≫ j = i ≫ p) :
    Flat (CommGroupScheme.groupHom t).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom t).hom.hom.left := by
  have hi' : IsMaximalSplitTorus i :=
    ⟨⟨hT, hi.2.1⟩, fun U' j' hj' t' ht' => hi.2.2 U' j' t' hj'.1.isTorus hj'.2 ht'⟩
  let : IsAffineHom U.toGrp.X.hom := hU.isAffineHom
  let I := hT.fppfImage (CommGroupScheme.groupHom t)
  have : IsClosedImmersion I.inclusion.hom.hom.left := I.isSplitSubtorus.2
  have : IsClosedImmersion j.hom.hom.left := hj
  have hsub : IsSplitSubtorus (I.inclusion ≫ j) := by
    refine ⟨I.isSplitSubtorus.1, ?_⟩
    change IsClosedImmersion (I.inclusion.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  have hmax : IsMaximalSplitTorus (I.inclusion ≫ j) := by
    let : Smooth G.X.hom := hG.smooth
    let : Smooth H.X.hom := hH.smooth
    let : IsAffineHom G.X.hom := hG.isAffineHom
    let : IsAffineHom H.X.hom := hH.isAffineHom
    have : Flat p.hom.hom.left := flat_of_surjective p
    have : LocallyOfFiniteType p.hom.hom.left := by
      have : LocallyOfFiniteType (p.hom.hom.left ≫ H.X.hom) := by
        rw [Over.w]
        infer_instance
      exact locallyOfFiniteType_of_comp _ H.X.hom
    let : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
    have hpL : LocallyOfFinitePresentation p.hom.hom.left :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    exact centralSurjectionMaximalSplitTorusImage k G H p hG hH inferInstance
      inferInstance hpL hp T I.torus i (I.inclusion ≫ j) I.projection hi' hsub I.flat
        I.surjective I.locallyOfFinitePresentation (by
          rw [← Category.assoc, I.factorization, hsquare])
  have : IsIso I.inclusion := hmax.2 U j ⟨hU, hj⟩ I.inclusion rfl
  have : IsIso I.inclusion.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso I.inclusion
  have heq : (CommGroupScheme.groupHom t).hom.hom.left =
      (CommGroupScheme.groupHom I.projection).hom.hom.left ≫
        I.inclusion.hom.hom.left := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, I.factorization]
  let : Flat (CommGroupScheme.groupHom I.projection).hom.hom.left := I.flat
  let : Surjective (CommGroupScheme.groupHom I.projection).hom.hom.left := I.surjective
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 2400000 in
/-- The torus restriction of a central torus-kernel surjection is surjective
on integral cocharacters after any simultaneous splitting extension. -/
theorem cocharacter_surjective_of_central_torus_square
    {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (p : G ⟶ H) [Surjective p.hom.hom.left]
    (hp : IsCentral (kernelι p)) (hker : IsTorus (kernel p))
    {T U : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) (t : T ⟶ U)
    (hi : IsMaximalTorus i) (hj : IsClosedSubgroup j)
    (hT : IsSplitTorus (baseChanged k L T.toGrp))
    (hU : IsSplitTorus (baseChanged k L U.toGrp))
    (hsquare : CommGroupScheme.groupHom t ≫ j = i ≫ p) :
    Function.Surjective
      (fun ν : cocharacterLattice ((CommGroupScheme.baseChange (baseMap k L)).obj T) =>
        ν ≫ (CommGroupScheme.baseChange (baseMap k L)).map t) := by
  let b := baseMap k L
  let B := GroupScheme.baseChange b
  let t' := (CommGroupScheme.baseChange b).map t
  have hp' : IsCentral (kernelι (B.map p)) := by
    have hc := (hp.baseChange b).comp (kernelBaseChangeIso b p).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc
  let : Surjective (B.map p).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b p.hom.hom inferInstance
  have hi' : IsMaximalTorus
      (T := (CommGroupScheme.baseChange b).obj T) (B.map i) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq L hi.1 hi.2.1
      (maximalTorusCentralizer k G hG T i hi)
  have hj' : IsClosedSubgroup (B.map j) := hj.baseChange b
  have hsquare' : CommGroupScheme.groupHom t' ≫ B.map j = B.map i ≫ B.map p := by
    change B.map (CommGroupScheme.groupHom t) ≫ B.map j = B.map i ≫ B.map p
    rw [← B.map_comp, hsquare, B.map_comp]
  obtain ⟨hflat, hsurj⟩ := flat_surjective_of_split_maximal_torus_square
    (connectedReductiveFieldExtensionStatement k L G hG)
    (connectedReductiveFieldExtensionStatement k L H hH)
    (B.map p) hp' (B.map i) (B.map j) t' hi' hj' hT hU hsquare'
  let : Flat (CommGroupScheme.groupHom t').hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom t').hom.hom.left := hsurj
  have : Epi (CommGroupScheme.groupHom t').hom.hom.left := Flat.epi_of_flat_of_surjective _
  have : Epi (CommGroupScheme.groupHom t').hom.hom := Over.epi_of_epi_left _
  have : Epi (CommGroupScheme.groupHom t') :=
    (Grp.forget _).epi_of_epi_map
      (inferInstanceAs (Epi (CommGroupScheme.groupHom t').hom.hom))
  have hkt : IsTorus (kernel (CommGroupScheme.groupHom t)) :=
    isTorus_kernel_of_central_torus_square hG p hp hker i j t hi hj hsquare
  have hkt' : IsTorus (kernel (CommGroupScheme.groupHom t')) := by
    change IsTorus (kernel (B.map (CommGroupScheme.groupHom t)))
    exact IsTorus.of_iso (kernelBaseChangeIso b (CommGroupScheme.groupHom t)).symm
      hkt.baseChange
  let : Smooth (kernel (CommGroupScheme.groupHom t')).X.hom := hkt'.smooth
  let : ConnectedSpace (kernel (CommGroupScheme.groupHom t')).X.left :=
    hkt'.connectedSpace
  exact hT.cocharacter_surjective_of_smooth_connected_kernel hU t'

/-- Two actual tori have a simultaneous finite Galois splitting field inside
a prescribed separably closed extension. -/
theorem exists_commonFiniteGaloisSplittingField_inside
    {k : Type u} [Field k]
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    (T U : GroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T) (hU : IsTorus U) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ IsGalois k L ∧
      IsSplitTorus (baseChanged k L T) ∧ IsSplitTorus (baseChanged k L U) := by
  let E := hT.commonFiniteGaloisSplitting hU
  let φ : E.carrier →ₐ[k] Ω := IsSepClosed.lift
  let L := φ.fieldRange
  let e : E.carrier ≃ₐ[k] L := φ.equivFieldRange
  have : FiniteDimensional k L := Module.Finite.equiv e.toLinearEquiv
  have : IsGalois k L := IsGalois.of_algEquiv e
  refine ⟨L, inferInstance, inferInstance, ?_, ?_⟩
  · obtain ⟨I, hI, ⟨s⟩⟩ := E.split_left
    exact ⟨I, hI, TorusExistence.nonempty_splitIso_extension e.toRingHom
      (RingHom.ext e.commutes) T I s⟩
  · obtain ⟨I, hI, ⟨s⟩⟩ := E.split_right
    exact ⟨I, hI, TorusExistence.nonempty_splitIso_extension e.toRingHom
      (RingHom.ext e.commutes) U I s⟩

/-- A compatible torus restriction of a central torus-kernel surjection
maps the actual norm subgroups onto one another. -/
theorem map_torusNormIwahori_eq_of_central_torus_square
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G) (EH : UnramifiedZeroDatum F H)
    (p : G ⟶ H) [Surjective p.hom.hom.left]
    (hp : IsCentral (kernelι p)) (hker : IsTorus (kernel p))
    (t : E.T ⟶ EH.T)
    (hsquare : CommGroupScheme.groupHom t ≫ EH.i = E.i ≫ p) :
    (torusNormIwahori (UnramifiedClosure F) E.L (intermediateValuation F E.L) E.T).map
        (rationalPoints.map (CommGroupScheme.groupHom t)) =
      torusNormIwahori (UnramifiedClosure F) EH.L (intermediateValuation F EH.L) EH.T := by
  obtain ⟨L, hfin, hgal, hT, hU⟩ :=
    exists_commonFiniteGaloisSplittingField_inside (SeparableClosure F) E.T.toGrp
      EH.T.toGrp E.isMaximallySplitMaximalTorus.1.1 EH.isMaximallySplitMaximalTorus.1.1
  let : FiniteDimensional (UnramifiedClosure F) L := hfin
  let : IsGalois (UnramifiedClosure F) L := hgal
  rw [torusNormIwahori_eq_of_splitting_fields F E.L L E.T E.isSplitTorus hT,
    torusNormIwahori_eq_of_splitting_fields F EH.L L EH.T EH.isSplitTorus hU]
  exact torusIwahoriSurjectivity F E.T EH.T t L hT hU
    (cocharacter_surjective_of_central_torus_square L
      E.isSimplyConnectedDerivedCover.isConnectedReductive
      EH.isSimplyConnectedDerivedCover.isConnectedReductive p hp hker E.i EH.i t
      E.isMaximallySplitMaximalTorus.1 EH.isMaximallySplitMaximalTorus.1.2.1
      hT hU hsquare)

/-- A compatible torus restriction of a central torus-kernel surjection
maps the actual zero subgroups onto one another. -/
theorem map_zeroPoints_eq_of_central_torus_square
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G) (EH : UnramifiedZeroDatum F H)
    (p : G ⟶ H) [Surjective p.hom.hom.left]
    (hp : IsCentral (kernelι p)) (hker : IsTorus (kernel p))
    (t : E.T ⟶ EH.T)
    (hsquare : CommGroupScheme.groupHom t ≫ EH.i = E.i ≫ p) :
    MapsZeroPointsOnto E EH p := by
  change E.zeroPoints.map (rationalPoints.map p) = EH.zeroPoints
  have hpoints : (rationalPoints.map p).comp (rationalPoints.map E.i) =
      (rationalPoints.map EH.i).comp
        (rationalPoints.map (CommGroupScheme.groupHom t)) := by
    apply MonoidHom.ext
    intro x
    simpa only [MonoidHom.comp_apply, rationalPoints.map_apply,
      Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun m : E.T.toGrp ⟶ H => x ≫ m.hom.hom) hsquare.symm
  simp only [UnramifiedZeroDatum.zeroPoints, UnramifiedZeroDatum.simplyConnectedImage,
    UnramifiedZeroDatum.torusIwahori, Subgroup.map_sup]
  rw [map_simplyConnectedImage_eq_of_centralSurjection
      E.isSimplyConnectedDerivedCover EH.isSimplyConnectedDerivedCover p hp,
    Subgroup.map_map, hpoints, ← Subgroup.map_map,
    map_torusNormIwahori_eq_of_central_torus_square E EH p hp hker t hsquare]

/-- Central surjections with torus kernel map the zero subgroups over the
unramified closure onto one another, for every defining datum. -/
theorem map_zeroPoints_eq_of_centralSurjection
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F G) (EH : UnramifiedZeroDatum F H)
    (p : G ⟶ H) [Surjective p.hom.hom.left]
    (hp : IsCentral (kernelι p)) (hker : IsTorus (kernel p)) :
    MapsZeroPointsOnto E EH p := by
  change E.zeroPoints.map (rationalPoints.map p) = EH.zeroPoints
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
  have heq := map_zeroPoints_eq_of_central_torus_square E E' p hp hker t hsquare
  change E.zeroPoints.map (rationalPoints.map p) = E'.zeroPoints at heq
  rwa [unramifiedZeroPointsIndependence F H E' EH] at heq

end Langlands.Geometry.Building.Kottwitz
