import Langlands.GroupScheme.SimplyConnected.TypeF4LongRootSubgroupStatement
import Langlands.GroupScheme.Reductive.ToralCentralizerRootSupport
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerReductiveProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerReductive
import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.Reductive.RootDatumRationalBase
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimpleIrreducibleProof
import Langlands.GroupScheme.Reductive.AlmostSimpleGeometricBaseChange
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.LinearAlgebra.CartanF4LongRoots
import Langlands.LinearAlgebra.RootPairingBaseComparison

/-! # The simply connected D₄ subgroup associated to a maximal torus in type F₄ -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.CartanF4LongRoots
open Langlands.LinearAlgebra.RootPairingBaseComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

private theorem split_D4_of_long_roots
    {K : Type u} [Field K]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    {i : T.toGrp ⟶ G} (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    {j : H ⟶ G} {f : T.toGrp ⟶ H} (hf : f ≫ j = i)
    {J A : Type u} [Finite J] [Finite A]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} [P.IsReduced]
    {R : RootDatum A (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf f R)
    (b : P.Base) (e : Fin 4 ≃ b.support)
    (hF4 : ∀ a c, P.pairing (e a) (e c) = CartanMatrix.F₄ a c)
    (hPtop : P.corootSpan ℤ = ⊤)
    (hs : Set.range R.root = P.root '' {r | IsLong P r}) :
    R.corootSpan ℤ = ⊤ ∧ ∃ (d : R.Base) (eD : Fin 4 ≃ d.support),
      ∀ a c, R.pairing (eD a) (eD c) = CartanMatrix.D 4 a c := by
  classical
  have hsubset : roots f ⊆ roots i := by
    rw [← hR.2.1, hs, ← hP.2.1]
    exact Set.image_subset_range _ _
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : Finite (weylImage i) := splitTorusWeylImageFinite K G T hT i hi.2.1
  let E := hP.sameTorusSubgroupEmbedding i f j hf hR hsubset
  let v := simpleLongRoot P b e
  have hv (q : Fin 4) : ∃ a : A, E.index a = v q := by
    change v q ∈ Set.range E.index
    rw [E.range_index_eq _ hs]
    exact isLong_simpleLongRoot P b e hF4 q
  choose w hw using hv
  have hwr (q : Fin 4) : R.root (w q) = P.root (v q) := by rw [← E.root_eq, hw]
  have hwc (q : Fin 4) : R.coroot (w q) = P.coroot (v q) := by rw [← E.coroot_eq, hw]
  have hwcart (a c : Fin 4) : R.pairing (w a) (w c) = CartanMatrix.D 4 a c := by
    rw [← R.root_coroot_eq_pairing, hR.1, hwr, hwc, ← hP.1, P.root_coroot_eq_pairing]
    exact pairing_simpleLongRoot P b e hF4 a c
  have hlin : LinearIndependent ℤ (fun q => R.root (w q)) := by
    simp only [hwr]
    exact linearIndependent_simpleLongRoot P b e hF4
  have hctop : Submodule.span ℤ (Set.range fun q => R.coroot (w q)) = ⊤ := by
    simp only [hwc]
    rw [span_simpleLongCoroot P b e hF4, hPtop]
  have hRtop : R.corootSpan ℤ = ⊤ := by
    apply top_unique
    rw [← hctop]
    exact Submodule.span_mono (by rintro _ ⟨q, rfl⟩; exact Set.mem_range_self (w q))
  refine ⟨hRtop, exists_base_D4_of_spanning R w hlin hwcart ?_ ?_⟩
  · intro r
    simp only [hwr]
    rw [span_simpleLongRoot P b e hF4]
    exact Submodule.subset_span (hs ▸ Set.mem_range_self r)
  · intro r
    rw [hctop]
    exact Submodule.mem_top

private theorem titsIndex_numbering_of_D4_base
    {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (d : TitsIndexData H)
    {T : CommGroupScheme (Spec (CommRingCat.of (SeparableClosure k)))}
    (hT : IsSplitTorus T.toGrp)
    {f : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H}
    (hf : IsMaximalTorus f) {J : Type u} [Finite J]
    {R : RootDatum J (characterLattice T) (cocharacterLattice T)} [R.IsReduced]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H).X.hom]
    [LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H).X.hom]
    (hR : IsRootDatumOf f R) (b : R.Base) (e : Fin 4 ≃ b.support)
    (hD : ∀ a c, R.pairing (e a) (e c) = CartanMatrix.D 4 a c) :
    ∃ eH : d.Vertex ≃ Fin 4, ∀ a c, d.cartan a c = CartanMatrix.D 4 (eH a) (eH c) := by
  classical
  let : Mono f.hom.hom.left := hf.2.1.mono
  let finite := hT.finite_relativeRoots f
  let Q := hR.relativeRootReflectionData.rootPairing hT finite
  let : Q.IsRootSystem := hR.relativeRootReflectionData.rootPairing_isRootSystem hT finite
  let : Q.IsCrystallographic :=
    hR.relativeRootReflectionData.rootPairing_isCrystallographic hT finite
  let : Fintype (relativeRoots f) := finite.fintype
  let bD := hR.rationalBase hT finite b
  let eD := hR.rationalBaseSupportEquiv hT finite b
  let bH := d.splitMaximalTorusBase hT hf hR
  let eH := d.splitMaximalTorusBaseEquiv hT hf hR
  let bHQ := hR.rationalBase hT finite bH
  let eHQ := hR.rationalBaseSupportEquiv hT finite bH
  let eQ := baseEquiv Q bHQ bD
  let η := ((eH.trans eHQ).trans eQ).trans (eD.symm.trans e.symm)
  refine ⟨η, fun a c => ?_⟩
  have hD' (r s : b.support) : b.cartanMatrix r s = CartanMatrix.D 4 (e.symm r) (e.symm s) := by
    change R.pairingIn ℤ r s = _
    rw [show R.pairingIn ℤ r s = R.pairing r s from R.algebraMap_pairingIn ℤ r s]
    simpa using hD (e.symm r) (e.symm s)
  calc
    d.cartan a c = bH.cartanMatrix (eH a) (eH c) :=
      (d.cartanMatrix_splitMaximalTorusBaseEquiv hT hf hR a c).symm
    _ = bHQ.cartanMatrix (eHQ (eH a)) (eHQ (eH c)) :=
      (hR.cartanMatrix_rationalBaseSupportEquiv hT finite bH _ _).symm
    _ = bD.cartanMatrix (eQ (eHQ (eH a))) (eQ (eHQ (eH c))) :=
      (cartanMatrix_baseEquiv Q bHQ bD _ _).symm
    _ = b.cartanMatrix (eD.symm (eQ (eHQ (eH a)))) (eD.symm (eQ (eHQ (eH c)))) := by
      simpa only [eD, bD, Equiv.apply_symm_apply] using
        hR.cartanMatrix_rationalBaseSupportEquiv hT finite b
          (eD.symm (eQ (eHQ (eH a)))) (eD.symm (eQ (eHQ (eH c))))
    _ = _ := hD' _ _

/-- A maximal torus of a simply connected group of type F₄ in characteristic zero
is contained in a closed simply connected absolutely almost-simple subgroup of type D₄. -/
theorem typeF4LongRootSubgroup : TypeF4LongRootSubgroupStatement.{u} := by
  intro k _ _ G _ _ d e hsc _ hF4 T i hi
  classical
  let K := SeparableClosure k
  let b := algebraBaseMap k K
  let F := GroupScheme.baseChange b
  let B := CommGroupScheme.baseChange b
  let T_K := B.obj T
  let G_K := F.obj G
  let i_K : T_K.toGrp ⟶ G_K := F.map i
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have hG := hsc.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  have hscK : IsSimplyConnected G_K := isSimplyConnectedFieldExtension k K G hsc
  have hGK := hscK.isSemisimple.isConnectedReductive
  let : IsAffineHom G_K.X.hom := hGK.isAffineHom
  let : Smooth G_K.X.hom := hGK.smooth
  have hTK : IsSplitTorus T_K.toGrp := GaloisPinningData.isSplitTorus_separableClosure T hi.1
  have hiK : IsMaximalTorus i_K := (maximalTorusBaseChange k K G T i hi.1 hi.2.1).mp hi
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K G_K hGK T_K hTK i_K hiK
  let bP := d.splitMaximalTorusBase hTK hiK hP
  let eP := e.symm.trans (d.splitMaximalTorusBaseEquiv hTK hiK hP)
  have hPcart (a c : Fin 4) : P.pairing (eP a) (eP c) = CartanMatrix.F₄ a c := by
    calc
      _ = bP.cartanMatrix (eP a) (eP c) := (P.algebraMap_pairingIn ℤ _ _).symm
      _ = d.cartan (e.symm a) (e.symm c) :=
        d.cartanMatrix_splitMaximalTorusBaseEquiv hTK hiK hP _ _
      _ = _ := by simpa using hF4 (e.symm a) (e.symm c)
  let L := longRootLattice P
  have hL (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) (hχ : χ ∈ L) :
      characterLattice.galoisRepresentation k K T σ χ ∈ L := by
    let γ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k K i hTK hiK.2.1 hP σ
    have hstable : L.map γ.weightMap ≤ L := by
      apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, rfl⟩
      change γ.weightMap (P.root r) ∈ L
      rw [γ.toHom.root_weightMap_apply P P r]
      exact Submodule.subset_span ⟨γ.indexEquiv r, (isLong_equiv P γ r).mpr hr, rfl⟩
    exact hstable ⟨χ, hχ, rfl⟩
  obtain ⟨N, n, hN, hn⟩ := exists_multiplicativeType_characterKernel T hi.1 L hL
  let a := CommGroupScheme.groupHom n ≫ i
  obtain ⟨C, c, hc, hcc⟩ := fieldCentralizerRepresentability k N G hN.isAffineHom a
  obtain ⟨hCs, hH⟩ := multiplicativeTypeCentralizerReductive k G hG N a hN C c hc hcc
  let : Smooth C.X.hom := hCs
  let : IsAffineHom C.X.hom := hcc.isAffineHom
  let H := identityComponent C
  let l : H ⟶ C := identityComponentι C
  let j : H ⟶ G := l ≫ c
  have hj : IsClosedSubgroup j := (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hcc
  let fC : T.toGrp ⟶ C := hc.factorHom i
    (range_le_torusCentralizer_of_factor a i (CommGroupScheme.groupHom n) rfl)
  have hfC : fC ≫ c = i := hc.factorHom_comp _ _
  let : ConnectedSpace T.X.left := hi.1.connectedSpace
  let f : T.toGrp ⟶ H := IdentityComponent.factor C fC
  have hfl : f ≫ l = fC := IdentityComponent.factor_identityComponentι C fC
  have hf : f ≫ j = i := by rw [show j = l ≫ c from rfl, ← Category.assoc, hfl, hfC]
  let H_K := F.obj H
  let f_K : T_K.toGrp ⟶ H_K := F.map f
  let j_K : H_K ⟶ G_K := F.map j
  have hfi : f_K ≫ j_K = i_K := by rw [← F.map_comp, hf]
  have hfK := IsMaximalTorus.of_comp (hj.baseChange b) (hfi.symm ▸ hiK)
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth H.X.hom := hH.smooth
  have hHK := connectedReductiveFieldExtensionStatement k K H hH
  let : IsAffineHom H_K.X.hom := hHK.isAffineHom
  let : Smooth H_K.X.hom := hHK.smooth
  let : Smooth (F.obj C).X.hom := IdentityComponent.smooth_baseChange C (algebraMap k K)
  let : IsAffineHom (F.obj C).X.hom := IdentityComponent.isAffineHom_baseChange C (algebraMap k K)
  let : IsAffineHom (B.obj N).X.hom := by
    have : IsAffineHom N.X.hom := hN.isAffineHom
    change IsAffineHom (Limits.pullback.snd N.X.hom b)
    infer_instance
  let : IsOpenImmersion (F.map l).hom.hom.left := isOpenImmersion_baseChange_map b l
  have hcK : (torusCentralizer (CommGroupScheme.groupHom (B.map n) ≫ i_K)).IsRepresentedBy
      (F.map c) := by
    change (torusCentralizer (T := B.obj N) (F.map (CommGroupScheme.groupHom n) ≫ F.map i)).IsRepresentedBy _
    rw [← F.map_comp, torusCentralizer_baseChange]
    exact hc.baseChange b
  have hfcK : f_K ≫ F.map l ≫ F.map c = i_K := by
    rw [← F.map_comp, hfi]
  have hroots := roots_of_open_toralCentralizer (B.map n) i_K (F.map l) (F.map c)
    f_K hfcK hTK hcK
  obtain ⟨A, hA, R, hR, hRred⟩ := rootDatumExistence K H_K hHK T_K hTK f_K hfK
  have hsupport : Set.range R.root = P.root '' {r | IsLong P r} := by
    rw [hR.2.1, hroots, ← hP.2.1]
    ext χ
    change (χ ∈ Set.range P.root ∧ B.map n ≫ χ = 0) ↔ χ ∈ P.root '' {r | IsLong P r}
    rw [hn χ]
    constructor
    · rintro ⟨⟨r, rfl⟩, hr⟩
      exact ⟨r, (root_mem_longRootLattice_iff P bP eP hPcart r).mp hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Set.mem_range_self _, Submodule.subset_span ⟨r, hr, rfl⟩⟩
  have hPtop := splitSimplyConnectedCorootSpan K G_K hscK T_K hTK i_K hiK J P hP hred
  obtain ⟨hRtop, bD, eD, hD⟩ := split_D4_of_long_roots hTK hiK hfi hP hR bP eP
    hPcart hPtop hsupport
  have hHssK : IsSemisimple H_K :=
    (splitSemisimpleRootDatum K H_K hHK T_K hTK f_K hfK A R hR).2.mpr
      (by rw [hRtop]; infer_instance)
  have hHscK := splitCorootSpanSimplyConnected K H_K hHssK T_K hTK f_K hfK A R hR hRtop
  have hHsc : IsSimplyConnected H := (isSimplyConnected_fieldExtension_iff (K := K) H).mp hHscK
  let : Mono f_K.hom.hom.left := hfK.2.1.mono
  let finite := hTK.finite_relativeRoots f_K
  let Q := hR.relativeRootReflectionData.rootPairing hTK finite
  let : Q.IsRootSystem := hR.relativeRootReflectionData.rootPairing_isRootSystem hTK finite
  let bQ := hR.rationalBase hTK finite bD
  let eQ := eD.trans (hR.rationalBaseSupportEquiv hTK finite bD)
  have hQcart (a c : Fin 4) : Q.pairing (eQ a) (eQ c) = (CartanMatrix.D 4 a c : ℚ) := by
    have heQ (r : Fin 4) : (eQ r : relativeRoots f_K) = hR.relativeRootEquiv (eD r) := rfl
    rw [heQ, heQ, hR.rationalRootPairing_pairing hTK finite, hD]
  have hHKas : IsAlmostSimple H_K := isAlmostSimple_of_isIrreducible hHssK f_K
    ⟨hTK, hfK.2.1⟩ hfK Q
    (hR.relativeRootReflectionData.rootPairing_root_image hTK finite)
    (isIrreducible_of_D4_base Q bQ eQ hQcart)
  have hHabs : IsAbsolutelyAlmostSimple H := by
    refine ⟨IsAlmostSimple.of_fieldExtension (K := K) hHKas, ?_⟩
    exact (hHKas.baseChange_of_isSepClosed (K := AlgebraicClosure k)).of_iso
      (baseChangeFieldTowerIso k K (AlgebraicClosure k) H)
  obtain ⟨dH⟩ := titsIndexExistence k H hHsc.isSemisimple
  obtain ⟨eH, heH⟩ := titsIndex_numbering_of_D4_base dH hTK hfK hR bD eD hD
  exact ⟨H, j, f, hj, hf, hHsc, hHabs, inferInstance, inferInstance, dH, eH, heH⟩

end Langlands.GroupScheme
