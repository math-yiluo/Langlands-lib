import Langlands.GroupScheme.SimplyConnected.TypeD4KernelLeafTitsClass
import Langlands.GroupScheme.SimplyConnected.LocalRankOneResidualIndices
import Langlands.GroupScheme.SimplyConnected.StarVertexFieldEmbeddings
import Langlands.GroupScheme.SimplyConnected.NormOneTitsNormalization
import Langlands.GroupScheme.SimplyConnected.TitsObstructionRootVanishing
import Langlands.GroupScheme.Reductive.ScalarExtensionTitsClass
import Langlands.GroupScheme.Reductive.SplitLeviBaseChange
import Langlands.GroupScheme.Reductive.TitsTransfer
import Langlands.ClassFieldTheory.Local.BrauerLocalCorestriction
import Langlands.ClassFieldTheory.Local.LocalDivisionBrauerOrder
import Langlands.Algebra.DivisionBrauerClass

/-! # Exclusion of centrally marked local inner and trialitarian D4 indices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Brauer Langlands.CentralSimple Langlands.BrauerCorestriction
open Langlands.ClassFieldTheory.Local Langlands.LocalField

namespace Langlands.GroupScheme

private theorem invariant_corestriction_degreeTwoClass
    (k E D : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E] [DivisionRing D] [Algebra E D] [FiniteDimensional E D]
    [Algebra.IsCentral E D] (hdegree : reducedDegree E D = 2) :
    localBrauerInvariant k (corHom k E (classOf (divisionAlgebra E D))) =
      rationalClass (1 / 2 : ℚ) := by
  let := FiniteExtension.normedField k E
  let := FiniteExtension.valuativeRel k E
  let := FiniteExtension.isLocalField k E
  let := spectralFiniteExtension_valuativeExtension k E
  have hcont := spectralFiniteExtension_algebraMap_continuous k E
  have hdim : Module.finrank E D = 2 * 2 := by
    rw [finrank_eq_reducedDegree_mul_self, hdegree]
  rw [localBrauerInvariant_corestriction k E hcont]
  exact localBrauerInvariant_division_degree_two E D hdim

private theorem exists_normOneFundamentalClass
    {E L : Type u} [Field E] [Field L] [Algebra E L] [IsGalois E L] [IsSepClosed L]
    {H : GroupScheme (Spec (CommRingCat.of E))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] (Q : GaloisPinningData E L H)
    (hspan : Q.rootDatum.corootSpan ℤ = ⊤)
    (hmodel : HasCentralDivisionNormOnePresentation H 2) :
    ∃ (b : Q.base.support) (D : Type u) (_ : DivisionRing D) (_ : Algebra E D)
      (_ : FiniteDimensional E D) (_ : Algebra.IsCentral E D), reducedDegree E D = 2 ∧
      let μ := Langlands.RootDatum.fundamentalWeightBasis Q.rootDatum Q.base hspan b
      ∀ (hdom : Q.toSplitPinning.IsDominantWeight μ) (hfix : Q.IsStarFixedWeight μ),
        Q.dominantTitsClass μ hdom hfix = classOf (divisionAlgebra E D) := by
  obtain ⟨D, _, _, _, _, hdegree, ⟨eModel⟩⟩ := hmodel
  let A := divisionAlgebra E D
  let model : H ≅ CentralSimpleUnits.normOne E A := eModel
  have hsize : 2 ≤ reducedDegree E A := hdegree.ge
  let chart := sepClosedExtensionChart E A L
  obtain ⟨e, _, _, hfirst, _⟩ := CentralSimpleUnits.normOneTitsNormalization Q A model chart hsize
  let b := e.symm ⟨0, by omega⟩
  refine ⟨b, D, inferInstance, inferInstance, inferInstance, inferInstance, hdegree, ?_⟩
  intro μ hdom hfix
  rw [← Q.titsObstructionValue_of_isDominantWeight hspan hfix hdom]
  exact hfirst

end Langlands.GroupScheme

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G)
  (q : d.Vertex ≃ Fin 4) (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

local instance obstructionKernelSmooth : Smooth p.kernel.X.hom :=
  p.index.isSemisimple.isConnectedReductive.smooth

local instance obstructionGeometricKernelSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
      p.kernel).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd p.kernel.X.hom _)
  infer_instance

private theorem geometricSimplyConnected (h : IsSimplyConnected G) :
    IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
      p.kernel) :=
  isSimplyConnectedFieldExtension k (SeparableClosure k) p.kernel (p.isSimplyConnected h)

private abbrev geometricProduct := (p.geometricSimplyConnected hsc).almostSimpleProduct

private abbrev geometricFactor (a : p.index.Vertex) :=
  p.index.geometricFactorIndex (p.geometricProduct hsc)
    (p.geometricSimplyConnected hsc).isSemisimple a

include hq in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem descendedComponentNormOneModel (a : p.index.Vertex) :
    HasCentralDivisionNormOnePresentation
      ((p.geometricProduct hsc).factorStabilizerDescent (p.geometricFactor hsc a)).1 2 := by
  simpa only [descendedComponentFactor, componentFactorOfPinningComparison,
    SimplyConnectedAlmostSimpleProduct.orbitWeilFactor,
    SimplyConnectedWeilFactor.componentFactor] using
    p.descendedComponentFactor_divisionModel_D4 hsc q hq a

include hq in
private theorem exists_descendedComponentWeightClass (a : p.index.Vertex) :
    type_of% (exists_normOneFundamentalClass
      (p.descendedComponentProjection hsc a).comparison.pinning
      (p.descendedComponentProjection_corootSpan_eq_top hsc a)
      (p.descendedComponentNormOneModel hsc q hq a)) :=
  exists_normOneFundamentalClass
    (p.descendedComponentProjection hsc a).comparison.pinning
    (p.descendedComponentProjection_corootSpan_eq_top hsc a)
    (p.descendedComponentNormOneModel hsc q hq a)

private theorem kernelLeafObstructionValue_eq_of_scalarExtension
    (a : p.index.Vertex) {E : IntermediateField k (SeparableClosure k)}
    {S : GaloisPinningData.ScalarExtension (E := E) p.index.pinning}
    {hdomS : S.pinning.toSplitPinning.IsDominantWeight
      (p.transportedKernelFundamentalWeight hsc S a)}
    {hfixS : S.pinning.IsStarFixedWeight (p.transportedKernelFundamentalWeight hsc S a)}
    {x : BrauerGroup.{u, u} E}
    (hS : S.pinning.dominantTitsClass (p.transportedKernelFundamentalWeight hsc S a) hdomS hfixS = x)
    (hfix : (p.index.pinning.baseChange E).IsStarFixedWeight
      (p.index.pinning.weightTransport E (p.index.absoluteFundamentalCharacter
        (p.isSimplyConnected hsc) a))) :
    (p.index.pinning.baseChange E).titsObstructionValue
      ((p.index.pinning.baseChange E).corootSpan_eq_top_of_simplyConnected
        (isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hsc)))
      (p.index.pinning.weightTransport E
        (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a)) hfix = x := by
  let P := p.index.pinning.baseChangeScalarExtension E
  let ω := p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a
  have hdomP : P.pinning.toSplitPinning.IsDominantWeight (P.rootEquiv.weightEquiv ω) :=
    p.transportedKernelFundamentalWeight_dominant hsc P a
  have hfixP : P.pinning.IsStarFixedWeight (P.rootEquiv.weightEquiv ω) := hfix
  have hspanP := P.pinning.corootSpan_eq_top_of_simplyConnected
    (isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hsc))
  have h := P.dominantTitsClass_transport S ω hdomP hdomS hfixP hfixS
  exact (P.pinning.titsObstructionValue_of_isDominantWeight hspanP hfixP hdomP).trans
    (h.symm.trans hS)

include hq in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kernelLeafObstruction_eq_degreeTwoClass
    (a : p.index.Vertex) (E : IntermediateField k (SeparableClosure k))
    (hE : E = p.componentField hsc a)
    (hfix : (p.index.pinning.baseChange E).IsStarFixedWeight
      (p.index.pinning.weightTransport E (p.index.absoluteFundamentalCharacter
        (p.isSimplyConnected hsc) a))) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra E D) (_ : FiniteDimensional E D)
      (_ : Algebra.IsCentral E D), reducedDegree E D = 2 ∧
      (p.index.pinning.baseChange E).titsObstructionValue
        ((p.index.pinning.baseChange E).corootSpan_eq_top_of_simplyConnected
          (isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hsc)))
        (p.index.pinning.weightTransport E
          (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a)) hfix =
        classOf (divisionAlgebra E D) := by
  subst E
  obtain ⟨b, D, instD, instAlg, instFin, instCentral, hdegree, hclass⟩ :=
    p.exists_descendedComponentWeightClass hsc q hq a
  obtain ⟨hbDom, hbFix, hcompare⟩ :=
    p.transportedKernelFundamentalWeight_titsClass_descendedComponent_D4 hsc q hq a b
  have hrelative := hcompare.trans (hclass hbDom hbFix)
  exact ⟨D, instD, instAlg, instFin, instCentral, hdegree,
    p.kernelLeafObstructionValue_eq_of_scalarExtension hsc a hrelative hfix⟩

include p hq in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientLeafObstruction_eq_degreeTwoClass
    (v : d.zeroVertices) (E : IntermediateField k (SeparableClosure k))
    (hE : E = d.starVertexField v.val)
    (hfix : (d.pinning.baseChange E).IsStarFixedWeight
      (d.pinning.weightTransport E (d.absoluteFundamentalCharacter hsc v.val))) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra E D) (_ : FiniteDimensional E D)
      (_ : Algebra.IsCentral E D), reducedDegree E D = 2 ∧
      (d.pinning.baseChange E).titsObstructionValue
        ((d.pinning.baseChange E).corootSpan_eq_top_of_simplyConnected
          (isSimplyConnectedFieldExtension k E G hsc))
        (d.pinning.weightTransport E (d.absoluteFundamentalCharacter hsc v.val)) hfix =
        classOf (divisionAlgebra E D) := by
  let a := p.comparison.vertexEquiv.symm v
  have hv : p.comparison.vertexEquiv a = v := p.comparison.vertexEquiv.apply_symm_apply v
  have hfield : E = p.componentField hsc a := by
    rw [p.componentField_eq_starVertexField_D4 hsc q hq a, hv]
    exact hE
  let GE := d.pinning.baseChange E
  let PE := p.index.pinning.baseChange E
  let hPE := isSimplyConnectedFieldExtension k E p.kernel (p.isSimplyConnected hsc)
  let hspan := PE.corootSpan_eq_top_of_simplyConnected hPE
  let ω := d.absoluteFundamentalCharacter hsc v.val
  let lam : GE.starFixedWeights := ⟨d.pinning.weightTransport E ω,
    (GE.mem_starFixedWeights _).mpr hfix⟩
  let μ := (p.leviComparison.baseChange E).starFixedRestriction hspan lam
  let η := p.index.pinning.weightTransport E
    (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a)
  have hω := p.comparison.weightRestriction_fundamentalWeight_zero
    (d.pinning_corootSpan_eq_top hsc) (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc)) v
  have hμ : μ.val = η :=
    (p.baseChange_starFixedRestriction_val hsc E lam ω rfl).trans
      (congrArg (p.index.pinning.weightTransport E) hω)
  have hμFix := PE.isStarFixedWeight_of_mem_starFixedWeights μ.property
  have hηFix : PE.IsStarFixedWeight η := hμ ▸ hμFix
  obtain ⟨D, instD, instAlg, instFin, instCentral, hdegree, hclass⟩ :=
    p.kernelLeafObstruction_eq_degreeTwoClass hsc q hq a E hfield hηFix
  exact ⟨D, instD, instAlg, instFin, instCentral, hdegree,
    (p.baseChange_titsObstruction_eq hsc E lam).trans
      ((PE.titsObstructionValue_congr hspan hμ hμFix hηFix).trans hclass)⟩

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (hsc : IsSimplyConnected G)

private def orbitFixedWeight (a : d.Vertex) : d.pinning.starFixedWeights :=
  ⟨d.absoluteOrbitWeight hsc a,
    (d.pinning.mem_starFixedWeights _).mpr (fun σ => d.absoluteOrbitWeight_star hsc σ a)⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem invariant_orbitFixedWeight_eq_half
    (q : d.Vertex ≃ Fin 4) (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (a : d.Vertex) (ha : q a ≠ 1) :
    localBrauerInvariant k (d.pinning.titsObstruction hsc (d.orbitFixedWeight hsc a)) =
      rationalClass (1 / 2 : ℚ) := by
  classical
  let E := d.starVertexField a
  let N := d.starVertexNormalClosure a
  let : Fintype (E →ₐ[k] N) :=
    Fintype.ofEquiv ↥(d.starOrbitVertices a) (d.starVertexEmbeddingOrbitEquiv a).symm
  have hcard : Fintype.card (E →ₐ[k] N) = Module.finrank k E := by
    rw [Fintype.card_eq_nat_card]
    exact d.natCard_starVertexEmbeddings a
  have hpos : 0 < Module.finrank k E := Module.finrank_pos
  let n := Module.finrank k E - 1
  let e : (E →ₐ[k] N) ≃ Fin (n + 1) := Fintype.equivFinOfCardEq
    (hcard.trans (Nat.sub_add_cancel hpos).symm)
  let lifts := d.starVertexEmbeddingLift a
  let ω := d.absoluteFundamentalCharacter hsc a
  have hlifts : ∀ f x, lifts f (algebraMap E (SeparableClosure k) x) =
      algebraMap N (SeparableClosure k) (f x) :=
    d.starVertexEmbeddingLift_apply a
  have hfix : (d.pinning.baseChange E).IsStarFixedWeight (d.pinning.weightTransport E ω) :=
    (d.pinning.forall_fixingSubgroup_starAction_iff E ω).mp
      (d.absoluteFundamentalCharacter_mem_fixedWeights hsc a)
  let v : d.zeroVertices := ⟨a, (zeroVertices_iff_D4_leaf q hq a).mpr ha⟩
  obtain ⟨D, _, _, _, _, hdegree, hclass⟩ :=
    d.anisotropicKernelIndex.ambientLeafObstruction_eq_degreeTwoClass hsc q hq v E rfl hfix
  let hspan := d.pinning.corootSpan_eq_top_of_simplyConnected hsc
  let hspanE := (d.pinning.baseChange E).corootSpan_eq_top_of_simplyConnected
    (isSimplyConnectedFieldExtension k E G hsc)
  have hsum : d.pinning.embeddingConjSum e lifts ω = d.absoluteOrbitWeight hsc a := by
    rw [GaloisPinningData.embeddingConjSum_eq]
    calc
      _ = ∑ f : E →ₐ[k] N, (d.pinning.starAction (lifts f)).val.weightEquiv ω :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ = _ := d.sum_starVertexEmbeddings_eq_absoluteOrbitWeight hsc a
  have hcorestriction : d.pinning.titsObstruction hsc (d.orbitFixedWeight hsc a) =
      corHom k E (classOf (divisionAlgebra E D)) := by
    have hsumFix := d.pinning.isStarFixedWeight_sum_conj
      (E := E) (N := N) (lam := ω) e lifts hlifts hfix
    have htransfer := d.pinning.titsObstructionValue_embeddingConjSum
      (E := E) (N := N) (lam := ω) hspan (d.natCard_starVertexEmbeddings a)
      hspanE e lifts hlifts hfix
    exact (d.pinning.titsObstructionValue_congr hspan hsum.symm
      (fun σ => d.absoluteOrbitWeight_star hsc σ a) hsumFix).trans
      (htransfer.trans (congrArg (corHom k E) hclass))
  rw [hcorestriction]
  exact invariant_corestriction_degreeTwoClass k E D hdegree

include hsc in
/-- A centrally marked D4 index over a nonarchimedean local field cannot
have trivial full star action or have no globally fixed leaf. -/
theorem not_hasRankOneD4InnerOrNoFixedLeafIndex : ¬ d.HasRankOneD4InnerOrNoFixedLeafIndex := by
  rintro ⟨q, hq, hstar | hno⟩
  · let a := q.symm 0
    let b := q.symm 2
    let c := q.symm 3
    have ha : q a ≠ 1 := by simp [a]
    have hb : q b ≠ 1 := by simp [b]
    have hc : q c ≠ 1 := by simp [c]
    let total := d.orbitFixedWeight hsc a + d.orbitFixedWeight hsc b + d.orbitFixedWeight hsc c
    have hsum : total.val = Langlands.RootDatum.d4LeafWeightSum d.pinning.rootDatum
        d.pinning.base (d.pinning_corootSpan_eq_top hsc) q := by
      change d.absoluteOrbitWeight hsc a + d.absoluteOrbitWeight hsc b +
        d.absoluteOrbitWeight hsc c = _
      rw [d.absoluteOrbitWeight_eq_of_fixed hsc a (hstar · a),
        d.absoluteOrbitWeight_eq_of_fixed hsc b (hstar · b),
        d.absoluteOrbitWeight_eq_of_fixed hsc c (hstar · c)]
      rfl
    have hroot : total.val ∈ d.pinning.rootDatum.rootSpan ℤ := by
      rw [hsum]
      exact Langlands.RootDatum.d4LeafWeightSum_mem_rootSpan d.pinning.rootDatum
        d.pinning.base (d.pinning_corootSpan_eq_top hsc) q hq.1
    have hzero := d.pinning.titsObstruction_eq_zero_of_mem_rootSpan_unconditional hsc total hroot
    have h := congrArg (localBrauerInvariant k) hzero
    change localBrauerInvariant k (d.pinning.titsObstruction hsc
      (d.orbitFixedWeight hsc a + d.orbitFixedWeight hsc b + d.orbitFixedWeight hsc c)) =
      localBrauerInvariant k 0 at h
    simp only [map_add, map_zero, d.invariant_orbitFixedWeight_eq_half hsc q hq a ha,
      d.invariant_orbitFixedWeight_eq_half hsc q hq b hb,
      d.invariant_orbitFixedWeight_eq_half hsc q hq c hc] at h
    have htwo : rationalClass (1 / 2 : ℚ) + rationalClass (1 / 2 : ℚ) = 0 := by
      rw [← map_add, show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℤ) : ℚ) by norm_num,
        UnramifiedBaseChange.rationalClass_intCast]
    rw [htwo, zero_add] at h
    exact Langlands.ClassFieldTheory.Global.rationalClass_half_ne_zero h
  · let a := q.symm 0
    have ha : q a ≠ 1 := by simp [a]
    have hroot := d.absoluteOrbitWeight_D4_mem_rootSpan_of_no_fixed_leaf
      hsc q hq.1 hno a ha
    have hzero := d.pinning.titsObstruction_eq_zero_of_mem_rootSpan_unconditional
      hsc (d.orbitFixedWeight hsc a) hroot
    have h := d.invariant_orbitFixedWeight_eq_half hsc q hq a ha
    rw [hzero, map_zero] at h
    exact Langlands.ClassFieldTheory.Global.rationalClass_half_ne_zero h.symm

end Langlands.GroupScheme.TitsIndexData
