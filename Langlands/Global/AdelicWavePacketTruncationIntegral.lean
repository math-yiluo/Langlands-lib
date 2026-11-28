import Langlands.Global.ArthurTruncationLocalBoundedness
import Mathlib.MeasureTheory.Integral.Prod

/-! # Arthur truncation of compact spectral integrals -/

noncomputable section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces EisensteinConstantTerm Idempotence

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "Z[" n "]" => (Fin n → ℝ)

section ConstantTerm

variable {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "L" => SubgroupFunctor.range j
local notation "Uₐ" => AdelicSubgroupPoints.adelicPoints F G L
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G L
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G L
local notation "η" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G L

private theorem subgroupConstantTerm_compactSpectralIntegral
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    {n : ℕ} (mu : Measure Z[n]) [IsLocallyFiniteMeasure mu]
    {C : Set Z[n]} (hC : IsCompact C) {φ : Z[n] → A → ℂ}
    (hφ : Continuous (Function.uncurry φ))
    (hinv : ∀ a, ∀ r ∈ rationalSubgroup F G, ∀ x, φ a (r * x) = φ a x)
    (hzero : ∀ a ∉ C, ∀ x, φ a x = 0) :
    Continuous (fun p : Z[n] × A => subgroupConstantTerm F j (φ p.1) p.2) ∧
    ∀ g : A, subgroupConstantTerm F j (fun x => ∫ a, φ a x ∂mu) g =
      ∫ a, subgroupConstantTerm F j (φ a) g ∂mu := by
  let : IsClosed (Uₐ : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hs hc hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G L
  let : IsProbabilityMeasure η :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G L
  let J (p : Z[n] × A) : Q → ℂ := LeftCosetSpace.lift Γ
    (fun n : Uₐ => φ p.1 ((n : A) * p.2)) (fun r n => by
      rw [Subgroup.coe_mul, mul_assoc]
      apply hinv
      exact rationalImage_le_rationalSubgroup j ((mem_rationalSubgroup_range_iff j _).mp r.property))
  have hJ : Continuous (Function.uncurry J) := by
    rw [← (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).continuous_comp_iff]
    change Continuous (fun p : (Z[n] × A) × Uₐ => φ p.1.1 ((p.2 : A) * p.1.2))
    exact hφ.comp (continuous_fst.fst.prodMk ((continuous_subtype_val.comp continuous_snd).mul
      continuous_fst.snd))
  have hout (a : Z[n]) (g : A) (q : Q) : J (a, g) q = φ a ((q.out : Uₐ).val * g) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hct (a : Z[n]) (g : A) : subgroupConstantTerm F j (φ a) g = ∫ q, J (a, g) q ∂η := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hout a g q).symm)
  constructor
  · simpa only [hct, Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous («μ» := η) hJ isCompact_univ)
  · intro g
    let I (a : Z[n]) (q : Q) := J (a, g) q
    let : IsFiniteMeasure (mu.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
    have hI : Continuous (Function.uncurry I) :=
      hJ.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
    have hint : Integrable (Function.uncurry I) ((mu.restrict C).prod η) := by
      rw [← Measure.restrict_univ («μ» := η), Measure.prod_restrict]
      exact hI.continuousOn.integrableOn_compact' (hC.prod isCompact_univ)
        (hC.measurableSet.prod MeasurableSet.univ)
    have hIzero (a : Z[n]) (ha : a ∉ C) (q : Q) : I a q = 0 :=
      (hout a g q).trans (hzero a ha _)
    change (∫ q : Q, ∫ a, φ a ((q.out : Uₐ).val * g) ∂mu ∂η) = _
    calc
      _ = ∫ q : Q, ∫ a in C, I a q ∂mu ∂η := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun q => ?_
        simp only [I, hout]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => hzero a ha _).symm
      _ = ∫ a in C, ∫ q : Q, I a q ∂η ∂mu := (integral_integral_swap hint).symm
      _ = ∫ a, subgroupConstantTerm F j (φ a) g ∂mu := by
        simp only [hct]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => by
          change (∫ q : Q, I a q ∂η) = 0
          simp only [hIzero a ha, integral_zero]

end ConstantTerm

/-- A compact spectral integral commutes with Arthur truncation. The pointwise truncated
family is continuous in the spectral variable and jointly measurable in both variables. -/
def WavePacketTruncationIntegralStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (_hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (Tp : V T)
    {n : ℕ} (mu : Measure Z[n]) [IsLocallyFiniteMeasure mu]
    {C : Set Z[n]} (_hC : IsCompact C) {φ : Z[n] → AdelicGroupPoints F G → ℂ},
    Continuous (Function.uncurry φ) →
    (∀ a, ∀ r ∈ rationalSubgroup F G, ∀ x, φ a (r * x) = φ a x) →
    (∀ a ∉ C, ∀ x, φ a x = 0) →
    let L (a : Z[n]) := truncation hG hi D hK hρ Tp (φ a)
    Measurable (Function.uncurry L) ∧
    ∀ x : AdelicGroupPoints F G,
      Continuous (fun a => L a x) ∧ (∀ a ∉ C, L a x = 0) ∧
      truncation hG hi D hK hρ Tp (fun y => ∫ a, φ a y ∂mu) x = ∫ a, L a x ∂mu

/-- Descend to each compact unipotent quotient and apply Fubini. The active cosets at a
fixed adelic argument are finite and independent of the spectral variable. -/
theorem wavePacketTruncationIntegral : WavePacketTruncationIntegralStatement.{u} := by
  classical
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ Tp n mu _ C hC φ hφ hinv hzero L
  let roots := simpleFinset ν hG hi
  let Θ (x : AdelicGroupPoints F G) : ℂ := ∫ a, φ a x ∂mu
  let sign (S : Finset (characterLattice T)) : ℂ := (-1) ^ (roots.card - S.card)
  let Q (S : Finset (characterLattice T)) :=
    ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T)))
  let r (S : Finset (characterLattice T)) (c : Q S) : AdelicGroupPoints F G :=
    (c.out : rationalSubgroup F G).val
  let kernel (S : Finset (characterLattice T)) (f : AdelicGroupPoints F G → ℂ)
      (x : AdelicGroupPoints F G) := cutoffKernel hG hi D hK hρ (S : Set (characterLattice T)) Tp f x
  let series (S : Finset (characterLattice T)) (f : AdelicGroupPoints F G → ℂ)
      (x : AdelicGroupPoints F G) := ∑' c : Q S, kernel S f (r S c * x)
  have hsub (S : Finset (characterLattice T)) (hS : S ∈ roots.powerset) :
      (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun _ ha => (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hS ha)
  have hct (S : Finset (characterLattice T)) (hS : S ∈ roots.powerset) :
      Continuous (fun p : Z[n] × AdelicGroupPoints F G =>
        constantTerm F i ν (S : Set (characterLattice T)) (φ p.1) p.2) ∧
      ∀ g : AdelicGroupPoints F G, constantTerm F i ν (S : Set (characterLattice T)) Θ g =
        ∫ a, constantTerm F i ν (S : Set (characterLattice T)) (φ a) g ∂mu := by
    have hU := (Standard.parabolicStructure i ν hG hi hν _ (hsub S hS)).2.2.1.1
    exact subgroupConstantTerm_compactSpectralIntegral (Standard.unipotentHom i ν S)
      hU.smooth hU.connectedSpace hU.isUnipotent mu hC hφ hinv hzero
  constructor
  · change Measurable (fun p : Z[n] × AdelicGroupPoints F G =>
      ∑ S ∈ roots.powerset, sign S * series S (φ p.1) p.2)
    refine Finset.measurable_fun_sum _ fun S hS => measurable_const.mul ?_
    change Measurable (fun p : Z[n] × AdelicGroupPoints F G =>
      ∑' c : Q S, kernel S (φ p.1) (r S c * p.2))
    have hm : Measurable (kernel S (fun _ => 1)) :=
      cutoffKernel_measurable hG hi hν D hK hρ S Tp _ ⟨measurable_const,
        fun _ _ => ⟨1, fun _ _ => by simp⟩, fun _ _ _ => rfl⟩
    have hone (x : AdelicGroupPoints F G) : constantTerm F i ν S (fun _ => 1) x = 1 := by
      let j := Standard.unipotentHom i ν (S : Set (characterLattice T))
      let U := SubgroupFunctor.range j
      let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
        AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
      have hU := (Standard.parabolicStructure i ν hG hi hν _ (hsub S hS)).2.2.1.1
      let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U) :=
        AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j
          hU.smooth hU.connectedSpace hU.isUnipotent
      let eta := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
      let : IsProbabilityMeasure eta :=
        AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
      change (∫ _ : AdelicSubgroupPoints.RationalQuotient F G U, (1 : ℂ) ∂eta) = 1
      simp [integral_const, Measure.real_def]
    apply Measurable.tsum
    intro c
    have hp : Continuous (fun p : Z[n] × AdelicGroupPoints F G => (p.1, r S c * p.2)) :=
      continuous_fst.prodMk (continuous_snd.const_mul _)
    have heq (p : Z[n] × AdelicGroupPoints F G) :
        kernel S (φ p.1) (r S c * p.2) =
          constantTerm F i ν S (φ p.1) (r S c * p.2) * kernel S (fun _ => 1) (r S c * p.2) := by
      unfold kernel cutoffKernel
      rw [hone, one_mul]
    simp only [heq]
    exact ((hct S hS).1.comp hp).measurable.mul (hm.comp hp.snd.measurable)
  · intro x
    have hseries (S : Finset (characterLattice T)) (hS : S ∈ roots.powerset) :
        Continuous (fun a => series S (φ a) x) ∧ (∀ a ∉ C, series S (φ a) x = 0) ∧
        series S Θ x = ∫ a, series S (φ a) x ∂mu := by
      let w (c : Q S) := ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T))
        (simpleRelativeRoots i ν) (height hi hK hρ (r S c * x) - Tp)
      have hfin : {c : Q S | w c ≠ 0}.Finite :=
        truncationFiniteness F G T i ν hG hi hν D K hK hρ S hS Tp x
      have hsum (f : AdelicGroupPoints F G → ℂ) :
          series S f x = ∑ c ∈ hfin.toFinset, kernel S f (r S c * x) := by
        apply tsum_eq_sum
        intro c hc
        have hw : w c = 0 := by
          simpa only [hfin.mem_toFinset, Set.mem_ofPred_eq, ne_eq, not_not] using hc
        change constantTerm F i ν (S : Set (characterLattice T)) f (r S c * x) * (w c : ℂ) = 0
        rw [hw, Int.cast_zero, mul_zero]
      have hkc (c : Q S) : Continuous (fun a => kernel S (φ a) (r S c * x)) :=
        ((hct S hS).1.comp (continuous_id.prodMk continuous_const)).mul_const _
      have hk0 (c : Q S) (a : Z[n]) (ha : a ∉ C) : kernel S (φ a) (r S c * x) = 0 := by
        simp only [kernel, cutoffKernel, constantTerm, subgroupConstantTerm, hzero a ha,
          integral_zero, zero_mul]
      refine ⟨?_, ?_, ?_⟩
      · simp only [hsum]
        exact continuous_finsetSum _ fun c _ => hkc c
      · intro a ha
        rw [hsum]
        exact Finset.sum_eq_zero fun c _ => hk0 c a ha
      · simp only [hsum]
        rw [integral_finsetSum _ (fun c _ =>
          ((hkc c).continuousOn.integrableOn_compact hC).integrable_of_forall_notMem_eq_zero (hk0 c))]
        refine Finset.sum_congr rfl fun c _ => ?_
        change constantTerm F i ν (S : Set (characterLattice T)) Θ (r S c * x) * (w c : ℂ) =
          ∫ a, constantTerm F i ν (S : Set (characterLattice T)) (φ a) (r S c * x) * (w c : ℂ) ∂mu
        rw [integral_mul_const, (hct S hS).2]
    change Continuous (fun a => ∑ S ∈ roots.powerset, sign S * series S (φ a) x) ∧
      (∀ a ∉ C, ∑ S ∈ roots.powerset, sign S * series S (φ a) x = 0) ∧
      (∑ S ∈ roots.powerset, sign S * series S Θ x) =
        ∫ a, ∑ S ∈ roots.powerset, sign S * series S (φ a) x ∂mu
    refine ⟨continuous_finsetSum _ fun S hS => (hseries S hS).1.const_mul _, ?_, ?_⟩
    · intro a ha
      exact Finset.sum_eq_zero fun S hS => by rw [(hseries S hS).2.1 a ha, mul_zero]
    · rw [integral_finsetSum _ (fun S hS =>
        (((hseries S hS).1.continuousOn.integrableOn_compact hC).integrable_of_forall_notMem_eq_zero
          (hseries S hS).2.1).const_mul (sign S))]
      exact Finset.sum_congr rfl fun S hS => by rw [integral_const_mul, (hseries S hS).2.2]

end Langlands.Global.ArthurTruncation
