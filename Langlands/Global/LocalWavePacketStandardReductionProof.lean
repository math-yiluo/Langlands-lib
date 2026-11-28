import Langlands.Global.LocalWavePacketTargetConjugation
import Langlands.Global.LocalWavePacketStandardRegularity
import Langlands.Global.LocalWavePacketStandardReduction
import Langlands.Global.AdelicEisensteinRegularityPresentationComparison
import Langlands.Global.AdelicEisensteinRegularityAmbientTransport

/-! # Proof of the reduction of Lapid's §8 limit to standard parabolic subgroups -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

section Standard

/-- `TruncatedStandardWavePacketLimitStatement`, for one maximal split torus and generic
cocharacter, as `TruncatedWavePacketPairLimit` for the standard parabolic subgroups `P_J`,
`P_{J'}` indexed by arbitrary subsets `J, J'` of the simple roots. -/
theorem standardPairLimit_of_statement (hstd : TruncatedStandardWavePacketLimitStatement)
    {F : Type} [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ∃ (K : Subgroup (AdelicGroupPoints F G))
      (hK₀ : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
        IsIwasawaCompact (Standard.parabolicHom i ν J) K) ∧
      ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅)),
        (∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
          IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
            (fun f q => truncation hG hi D hK₀ hρ Tp
              (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) ∧
        ∀ (v₀ : V T), (∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v₀) →
        ∀ (J J' : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
          J' ⊆ simpleRelativeRoots i ν →
        ∀ (hKJ : IsIwasawaCompact (Standard.parabolicHom i ν J) K)
          (hKJ' : IsIwasawaCompact (Standard.parabolicHom i ν J') K)
          (π' : Standard.parabolicScheme i ν J' ⟶ Standard.leviScheme i ν J'),
          Standard.leviToParabolic i ν J' ≫ π' = 𝟙 (Standard.leviScheme i ν J') →
          TruncatedWavePacketPairLimit K
            (fun j f y => truncation hG hi D hK₀ hρ ((j : ℝ) • v₀)
              (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) y.out)
            (Standard.parabolicHom i ν J) (Standard.unipotentToParabolic i ν J)
            (Standard.leviToParabolic i ν J) hKJ (IsStandardRegularParameter D J)
            (Standard.parabolicHom i ν J') (Standard.unipotentToParabolic i ν J')
            (Standard.leviToParabolic i ν J') π' hKJ' (IsStandardRegularParameter D J') := by
  classical
  obtain ⟨K, hKmax, hK₀, hKS, hrest⟩ := hstd F G T i ν hG hi hν
  have hidx (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
      ∃ S : ArthurTruncation.StandardIndex hG hi ν, S.roots = J := by
    refine ⟨⟨(simpleFinset ν hG hi).filter (· ∈ J),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩, ?_⟩
    ext x
    simp only [StandardIndex.roots, Finset.coe_filter, Set.mem_ofPred_eq, mem_simpleFinset]
    exact ⟨fun h => h.2, fun h => ⟨hJ h, h⟩⟩
  refine ⟨K, hK₀, hKmax, fun J hJ => ?_, fun D hρ => ⟨(hrest D hρ hK₀ hKS).1, ?_⟩⟩
  · obtain ⟨S, rfl⟩ := hidx J hJ
    exact hKS S
  · intro v₀ hv₀ J J' hJ hJ' hKJ hKJ' π' hπ'
    obtain ⟨S, rfl⟩ := hidx J hJ
    obtain ⟨S', rfl⟩ := hidx J' hJ'
    intro N d rho hsmooth hcalc hrho μM' _ hμM' n n' e e' β' hβc hβs hβ1 k q v b c Sx E DE hv
      hb hS hc hD hE hEis k' q' v' b' c' Sx' E' DE' hv' hb' hS' hc' hD' hE' hEis' Ω _ w cw hw
      hinj hsurj m ψ coeff DM hψ hDM hcoeff hexp
    exact (hrest D hρ hK₀ hKS).2 rho hsmooth hcalc hrho S S' π' hπ' μM' hμM' e e' β' hβc hβs hβ1
      k q v b c Sx E DE hv hb hS hc hD hE hEis k' q' v' b' c' Sx' E' DE' hv' hb' hS' hc' hD' hE'
      hEis' Ω w cw hw hinj hsurj m ψ coeff DM hψ hDM hcoeff hexp v₀ hv₀

end Standard

section Main

set_option maxHeartbeats 1000000 in
/-- **Reduction of Lapid's §8 limit to standard parabolic subgroups.** The limit for standard
parabolic subgroups of one maximal split torus implies the limit for arbitrary presented
parabolic subgroups. -/
theorem truncatedWavePacketStandardization : TruncatedWavePacketStandardizationStatement := by
  classical
  intro hstd F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU'
    l' _ a' r' _ _ _ hA' hT' π' hG hU hU' hlπ'
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  obtain ⟨K, hK₀, hKmax, hKJ, hlimstd⟩ :=
    standardPairLimit_of_statement hstd G r.data.T r.data.i r.data.ν hG
      r.isCompatible.maximalSplit r.isCompatible.generic
  -- The standard family of the presentation `r`.
  let fam : StandardParabolicFamily F G :=
    StandardParabolicFamily.ofMaximalSplitTorus hG r.data.i r.isCompatible.maximalSplit
      r.data.ν r.isCompatible.generic
  have hKfam (J : Langlands.Global.StandardIndex F G fam.i fam.ν) :
      IsIwasawaCompact (fam.p J) K :=
    hKJ J.val J.property
  have htorus (J : Langlands.Global.StandardIndex F G fam.i fam.ν) :
      restrictToTorus F fam.i fam.ν J.val = fam.torusRestrictReal J := by
    have h : torusToParabolic F fam.i fam.ν J.val = fam.torus J ≫ fam.l J := by
      have : Mono (fam.p J) := by
        let : Mono (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup.mono
        have hpOver : Mono (fam.p J).hom.hom := Over.mono_of_mono_left _
        exact (Grp.forget _).mono_of_mono_map (f := fam.p J) hpOver
      apply (cancel_mono (fam.p J)).mp
      exact (torusToParabolic_comp F fam.i fam.ν J.val).trans (by
        rw [Category.assoc]
        exact (fam.torus_comp J).symm)
    unfold restrictToTorus StandardParabolicFamily.torusRestrictReal
    rw [h]
    rfl
  -- The source: `P` is identified with the standard parabolic `P_I`.
  let I : Langlands.Global.StandardIndex F G fam.i fam.ν :=
    ⟨r.data.J, r.isCompatible.subset_simpleRoots⟩
  have hpI : IsClosedSubgroup (fam.p I) := (fam.isCompatible I).parabolic.isClosedSubgroup
  have : IsClosedImmersion (fam.p I).hom.hom.left := hpI
  have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
  have hrange : SubgroupFunctor.range (fam.p I) = SubgroupFunctor.range p :=
    (fam.isCompatible I).parabolic_eq.trans r.isCompatible.parabolic_eq.symm
  let eI : fam.P I ≅ P := hpI.sourceIsoOfRangeEq hp hrange
  have heI : eI.hom ≫ p = fam.p I := hpI.sourceIsoOfRangeEq_hom_comp hp hrange
  have hUrange : SubgroupFunctor.range (iU ≫ p) =
      SubgroupFunctor.range (fam.iU I ≫ fam.p I) :=
    range_comp_unipotentRadical_eq_of_iso eI heI hU.1 (fam.isUnipotentRadical I).1
  have hLrange : SubgroupFunctor.range (fam.l I ≫ fam.p I) = SubgroupFunctor.range (l ≫ p) :=
    (fam.isCompatible I).levi_eq.trans r.isCompatible.levi_eq.symm
  have hMI : IsClosedSubgroup (fam.l I ≫ fam.p I) :=
    (fam.isCompatible I).levi.isClosedSubgroup.comp hpI
  have hM : IsClosedSubgroup (l ≫ p) := r.isCompatible.levi.isClosedSubgroup.comp hp
  let δI : fam.M I ≅ M := hMI.sourceIsoOfRangeEq hM hLrange
  have hδI : δI.hom ≫ l = fam.l I ≫ eI.hom := by
    let : Mono p.hom.hom.left := hp.mono
    have hpOver : Mono p.hom.hom := Over.mono_of_mono_left _
    let : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hpOver
    apply (cancel_mono p).mp
    rw [Category.assoc, Category.assoc, heI]
    exact hMI.sourceIsoOfRangeEq_hom_comp hM hLrange
  have hK_p : IsIwasawaCompact p K := (hKfam I).of_range_eq hrange
  have hjP : eI.symm.hom ≫ fam.p I = p := by
    rw [Iso.symm_hom, ← heI, Iso.inv_hom_id_assoc]
  have hδI' : δI.symm.hom ≫ fam.l I = l ≫ eI.symm.hom := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hδI, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  -- The target: `P'` is conjugate to a standard parabolic `P_{I'}`.
  obtain ⟨I', s, eQ, κ, heQ, hκ, hVrange⟩ :=
    fam.exists_standardConjugate p' iU' l' r'.isCompatible.parabolic hU' r'.isCompatible.levi
  let J₁ : Set (characterLattice r.data.T) := I.val
  let J₂ : Set (characterLattice r.data.T) := I'.val
  have hJ₁ : J₁ ⊆ simpleRelativeRoots r.data.i r.data.ν := I.property
  have hJ₂ : J₂ ⊆ simpleRelativeRoots r.data.i r.data.ν := I'.property
  let π₀ : fam.P I' ⟶ fam.M I' := eQ.hom ≫ π' ≫ κ.inv
  have hπ₀ : fam.l I' ≫ π₀ = 𝟙 (fam.M I') := by
    simp only [π₀, ← Category.assoc, ← hκ]
    simp only [Category.assoc, reassoc_of% hlπ', Iso.hom_inv_id]
  have hIsoE : IsIso (G.innerIso s⁻¹).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (G.innerIso s⁻¹))).hom)
  have : IsClosedImmersion (Standard.parabolicHom r.data.i r.data.ν J₂ ≫ (G.innerIso s⁻¹).hom).hom.hom.left := by
    change IsClosedImmersion ((Standard.parabolicHom r.data.i r.data.ν J₂).hom.hom.left ≫
      (G.innerIso s⁻¹).hom.hom.hom.left)
    infer_instance
  have : IsClosedImmersion (Standard.unipotentToParabolic r.data.i r.data.ν J₂ ≫
      Standard.parabolicHom r.data.i r.data.ν J₂ ≫ (G.innerIso s⁻¹).hom).hom.hom.left := by
    have h : IsClosedSubgroup ((Standard.unipotentToParabolic r.data.i r.data.ν J₂ ≫
        Standard.parabolicHom r.data.i r.data.ν J₂) ≫ (G.innerIso s⁻¹).hom) :=
      IsClosedSubgroup.comp_iso (i := Standard.unipotentToParabolic r.data.i r.data.ν J₂ ≫
        Standard.parabolicHom r.data.i r.data.ν J₂)
        (inferInstance : IsClosedImmersion (Standard.unipotentToParabolic r.data.i r.data.ν J₂ ≫
          Standard.parabolicHom r.data.i r.data.ν J₂).hom.hom.left) _
    rw [Category.assoc] at h
    exact h
  have hK'' : IsIwasawaCompact (fam.p I' ≫ (G.innerIso s⁻¹).hom) K :=
    (hKfam I').of_conjugate_map (fun x => map_conjugate_target s⁻¹ x)
  have hjQ : eQ.symm.hom ≫ fam.p I' ≫ (G.innerIso s⁻¹).hom = p' := by
    rw [Iso.symm_hom, ← heQ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, G.innerIso_inv_hom, Iso.hom_inv_id,
      Category.comp_id]
  have hrange'' : SubgroupFunctor.range (fam.p I' ≫ (G.innerIso s⁻¹).hom) = SubgroupFunctor.range p' :=
    le_antisymm
      (SubgroupFunctor.range_le_of_factor eQ.hom (by rw [← hjQ, Iso.symm_hom, Iso.hom_inv_id_assoc]))
      (SubgroupFunctor.range_le_of_factor eQ.symm.hom hjQ)
  have hK_p' : IsIwasawaCompact p' K := hK''.of_range_eq hrange''
  have hV : SubgroupFunctor.range (fam.iU I' ≫ fam.p I' ≫ (G.innerIso s⁻¹).hom) =
      SubgroupFunctor.range (iU' ≫ p') :=
    range_comp_unipotentRadical_eq_of_iso eQ.symm hjQ (fam.isUnipotentRadical I').1 hU'.1
  have hκ' : κ.symm.hom ≫ fam.l I' = l' ≫ eQ.symm.hom := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hκ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hπ' : π' ≫ κ.symm.hom = eQ.symm.hom ≫ π₀ := by
    simp only [π₀, Iso.symm_hom, Iso.inv_hom_id_assoc]
  -- Regularity of the conjugated target presentation.
  let r'' := r'.compAmbientIso (G.innerIso s)
  let : Mono r''.data.i.hom.hom.left := r''.isCompatible.maximalSplit.isSplitSubtorus.mono
  let : Fintype (relativeWeylGroup r''.data.i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup r''.data.i r''.isCompatible.maximalSplit)
  let : Mono (CommGroupScheme.groupHom r''.data.f).hom.hom.left :=
    inferInstanceAs (Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left)
  have hAI := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
  have hAI' := (fam.isCompatible I').splitComponent.isCentralSplitTorus.1.1
  have hsrc (D₀ : RelativeRootReflectionData r.data.i) (R₁ : ℝ) : ∃ R : ℝ, ∀ lam,
      IsStandardRegularParameter D₀ J₁ R lam →
        r.IsRegularParameter hA hT R₁ (parameterRestrictIsoEquiv eI.symm lam) := by
    have hmonoF : ∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left := by
      intro J
      let := (fam.isCompatible J).splitComponent.1.isSplitSubtorus.mono
      let := (fam.isCompatible J).levi.isClosedSubgroup.mono
      let := (fam.isCompatible J).parabolic.isClosedSubgroup.mono
      have : Mono (fam.a J ≫ fam.l J ≫ fam.p J).hom.hom.left := by
        change Mono ((fam.a J).hom.hom.left ≫ (fam.l J).hom.hom.left ≫ (fam.p J).hom.hom.left)
        infer_instance
      exact mono_of_mono_fac
        (congrArg (fun z => z.hom.hom.left) (fam.isCompatible J).factor_comp)
    have : Mono fam.i.hom.hom.left := ‹Mono r.data.i.hom.hom.left›
    have : Fintype (relativeWeylGroup fam.i) := ‹Fintype (relativeWeylGroup r.data.i)›
    obtain ⟨R', hR'⟩ := rootPresentationRegularityComparison F G P M (fam.P I) (fam.M I) A
      (fam.A I) p l a r (fam.p I) (fam.l I) (fam.a I) (fam.rootPresentation I) hA hT hAI hT hG
      eI.hom heI hrange.symm hLrange.symm R₁
    obtain ⟨R, hR⟩ := fam.exists_isRegularParameter_of_coroot_lt D₀ I hAI hT R'
    refine ⟨R, fun lam hlam => hR' _ ?_⟩
    have hlam' : parameterRestrict eI.hom (parameterRestrictIsoEquiv eI.symm lam) = lam :=
      (parameterRestrictIsoEquiv eI).apply_symm_apply lam
    rw [hlam']
    exact hR lam fun α hα hαJ => by
      rw [← htorus I]
      exact hlam α hα hαJ
  have htgt (D₀ : RelativeRootReflectionData r.data.i) (R₁ : ℝ) : ∃ R : ℝ, ∀ lam,
      IsStandardRegularParameter D₀ J₂ R lam →
        r'.IsRegularParameter hA' hT' R₁ (parameterRestrictIsoEquiv eQ.symm lam) := by
    have hmonoF : ∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left := by
      intro J
      let := (fam.isCompatible J).splitComponent.1.isSplitSubtorus.mono
      let := (fam.isCompatible J).levi.isClosedSubgroup.mono
      let := (fam.isCompatible J).parabolic.isClosedSubgroup.mono
      have : Mono (fam.a J ≫ fam.l J ≫ fam.p J).hom.hom.left := by
        change Mono ((fam.a J).hom.hom.left ≫ (fam.l J).hom.hom.left ≫ (fam.p J).hom.hom.left)
        infer_instance
      exact mono_of_mono_fac
        (congrArg (fun z => z.hom.hom.left) (fam.isCompatible J).factor_comp)
    have : Mono fam.i.hom.hom.left := ‹Mono r.data.i.hom.hom.left›
    have : Fintype (relativeWeylGroup fam.i) := ‹Fintype (relativeWeylGroup r.data.i)›
    have hrange₁ : SubgroupFunctor.range (p' ≫ (G.innerIso s).hom) =
        SubgroupFunctor.range (fam.p I') :=
      le_antisymm
        (SubgroupFunctor.range_le_of_factor eQ.inv (by rw [← heQ, Iso.inv_hom_id_assoc]))
        (SubgroupFunctor.range_le_of_factor eQ.hom heQ)
    have h1 : κ.hom ≫ l' ≫ p' ≫ (G.innerIso s).hom = fam.l I' ≫ fam.p I' := by
      rw [← heQ, ← Category.assoc, hκ, Category.assoc]
    have hLrange₁ : SubgroupFunctor.range (l' ≫ p' ≫ (G.innerIso s).hom) =
        SubgroupFunctor.range (fam.l I' ≫ fam.p I') :=
      le_antisymm
        (SubgroupFunctor.range_le_of_factor κ.inv (by rw [← h1, Iso.inv_hom_id_assoc]))
        (SubgroupFunctor.range_le_of_factor κ.hom h1)
    obtain ⟨R', hR'⟩ := rootPresentationRegularityComparison F G P' M' (fam.P I') (fam.M I') A'
      (fam.A I') (p' ≫ (G.innerIso s).hom) l' a' r'' (fam.p I') (fam.l I') (fam.a I')
      (fam.rootPresentation I') hA' hT' hAI' hT hG eQ.hom heQ hrange₁ hLrange₁ R₁
    obtain ⟨R, hR⟩ := fam.exists_isRegularParameter_of_coroot_lt D₀ I' hAI' hT R'
    refine ⟨R, fun lam hlam => ?_⟩
    have hlam' : parameterRestrict eQ.hom (parameterRestrictIsoEquiv eQ.symm lam) = lam :=
      (parameterRestrictIsoEquiv eQ).apply_symm_apply lam
    have h2 := hR' (parameterRestrictIsoEquiv eQ.symm lam) (by
      rw [hlam']
      exact hR lam fun α hα hαJ => by
        rw [← htorus I']
        exact hlam α hα hαJ)
    exact (eisensteinRegularityAmbientTransport F G G P' M' A' p' l' a' r' (G.innerIso s) hA' hT'
      R₁ _).mp h2
  refine ⟨K, hK_p, hK_p', hK₀, hKmax, fun D₀ hρ₀ => (hlimstd D₀ hρ₀).1, ?_⟩
  intro N d rho hsmooth hcalc hrho μM' _ hμM' n n' e e' β' hβc hβs hβ1 k q v b c S Ed D hv hb hS
    hc hD hE hEis k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' hEis' T _ w cw hw hinj hsurj m ψ
    coeff DM hψ hDM hcoeff hexp D₀ hρ₀ v₀ hv₀
  have H0 : TruncatedWavePacketPairLimit K _ (Standard.parabolicHom r.data.i r.data.ν J₁)
      (Standard.unipotentToParabolic r.data.i r.data.ν J₁)
      (Standard.leviToParabolic r.data.i r.data.ν J₁) (hKJ J₁ hJ₁)
      (IsStandardRegularParameter D₀ J₁) (Standard.parabolicHom r.data.i r.data.ν J₂)
      (Standard.unipotentToParabolic r.data.i r.data.ν J₂)
      (Standard.leviToParabolic r.data.i r.data.ν J₂) π₀ (hKJ J₂ hJ₂)
      (IsStandardRegularParameter D₀ J₂) :=
    (hlimstd D₀ hρ₀).2 v₀ hv₀ J₁ J₂ hJ₁ hJ₂ (hKJ J₁ hJ₁) (hKJ J₂ hJ₂) π₀ hπ₀
  have H1 : TruncatedWavePacketPairLimit K _ (Standard.parabolicHom r.data.i r.data.ν J₁)
      (Standard.unipotentToParabolic r.data.i r.data.ν J₁)
      (Standard.leviToParabolic r.data.i r.data.ν J₁) (hKJ J₁ hJ₁)
      (fun R lam => r.IsRegularParameter hA hT R (parameterRestrictIsoEquiv eI.symm lam))
      (Standard.parabolicHom r.data.i r.data.ν J₂)
      (Standard.unipotentToParabolic r.data.i r.data.ν J₂)
      (Standard.leviToParabolic r.data.i r.data.ν J₂) π₀ (hKJ J₂ hJ₂)
      (fun R lam => r'.IsRegularParameter hA' hT' R (parameterRestrictIsoEquiv eQ.symm lam)) :=
    TruncatedWavePacketPairLimit.mono_reg (hsrc D₀) (htgt D₀) H0
  have H2 : TruncatedWavePacketPairLimit K _ p iU l hK_p (r.IsRegularParameter hA hT)
      (Standard.parabolicHom r.data.i r.data.ν J₂)
      (Standard.unipotentToParabolic r.data.i r.data.ν J₂)
      (Standard.leviToParabolic r.data.i r.data.ν J₂) π₀ (hKJ J₂ hJ₂)
      (fun R lam => r'.IsRegularParameter hA' hT' R (parameterRestrictIsoEquiv eQ.symm lam)) :=
    TruncatedWavePacketPairLimit.of_iso_source (hKJ J₁ hJ₁) hK_p (hKJ J₂ hJ₂) eI.symm hjP
      δI.symm hδI' hUrange.symm H1
  have r₂ : ParabolicRootPresentation (Standard.parabolicHom r.data.i r.data.ν J₂)
      (Standard.leviToParabolic r.data.i r.data.ν J₂) (fam.a I') := fam.rootPresentation I'
  have hRad₂ : LeviSubgroup.IsGeometricUnipotentRadical
      (Standard.unipotentToParabolic r.data.i r.data.ν J₂) := fam.isUnipotentRadical I'
  have hK₂'' : IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν J₂ ≫
      (G.innerIso s⁻¹).hom) K := hK''
  have H3 : TruncatedWavePacketPairLimit K _ p iU l hK_p (r.IsRegularParameter hA hT)
      (Standard.parabolicHom r.data.i r.data.ν J₂ ≫ (G.innerIso s⁻¹).hom)
      (Standard.unipotentToParabolic r.data.i r.data.ν J₂)
      (Standard.leviToParabolic r.data.i r.data.ν J₂) π₀ hK₂''
      (fun R lam => r'.IsRegularParameter hA' hT' R (parameterRestrictIsoEquiv eQ.symm lam)) :=
    TruncatedWavePacketPairLimit.of_conj_target s⁻¹ hG hU.1.isUnipotent r₂ hRad₂ hK_p
      (hKJ J₂ hJ₂) hK₂'' H2
  let jQ₂ : P' ≅ Standard.parabolicScheme r.data.i r.data.ν J₂ := eQ.symm
  have hjQ₂ : jQ₂.hom ≫ Standard.parabolicHom r.data.i r.data.ν J₂ ≫ (G.innerIso s⁻¹).hom = p' :=
    hjQ
  let κ₂ : M' ≅ Standard.leviScheme r.data.i r.data.ν J₂ := κ.symm
  have hκ₂ : κ₂.hom ≫ Standard.leviToParabolic r.data.i r.data.ν J₂ = l' ≫ jQ₂.hom := hκ'
  let π₂ : Standard.parabolicScheme r.data.i r.data.ν J₂ ⟶ Standard.leviScheme r.data.i r.data.ν J₂ :=
    π₀
  have hπ₂ : π' ≫ κ₂.hom = jQ₂.hom ≫ π₂ := hπ'
  have hV₂ : SubgroupFunctor.range (Standard.unipotentToParabolic r.data.i r.data.ν J₂ ≫
      Standard.parabolicHom r.data.i r.data.ν J₂ ≫ (G.innerIso s⁻¹).hom) =
      SubgroupFunctor.range (iU' ≫ p') := hV
  have H4 : TruncatedWavePacketPairLimit K _ p iU l hK_p (r.IsRegularParameter hA hT) p' iU' l' π'
      hK_p' (r'.IsRegularParameter hA' hT') :=
    TruncatedWavePacketPairLimit.of_iso_target hK_p hK₂'' hK_p' jQ₂ hjQ₂ κ₂ hκ₂ hπ₂ hV₂ H3
  exact H4 rho hsmooth hcalc hrho μM' hμM' e e' β' hβc hβs hβ1 k q v b c S Ed D hv hb hS hc hD hE
    hEis k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' hEis' T w cw hw hinj hsurj m ψ coeff DM
    hψ hDM hcoeff hexp

end Main

end Langlands.Global
