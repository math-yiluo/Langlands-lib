import Langlands.Shimura.PEL.HarrisIntegralSourceResidues
import Langlands.Shimura.PEL.HarrisPolarizedWeilTower

/-! # Cofinality of the actual Harris principal congruence subgroups -/

noncomputable section

open Filter Topology
open scoped TensorProduct BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.Global

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ

private theorem exists_integralAdele_multiples_mem (h : RationalProfiniteIntegerAdeleComparison)
    {U : Set Af} (hU : U ∈ 𝓝 (0 : Af)) :
    ∃ m : ℕ+, ∀ r : Rf, m.val • (r : Af) ∈ U := by
  classical
  let e := Classical.choose h
  have hc : Continuous (fun x : ProfiniteIntegerRing => (e x : Af)) :=
    continuous_subtype_val.comp (Classical.choose_spec h).1
  have he0 : (e 0 : Af) = 0 := by rw [map_zero]; rfl
  have hpre : (fun x : ProfiniteIntegerRing => (e x : Af)) ⁻¹' U ∈ 𝓝 0 :=
    hc.continuousAt.preimage_mem_nhds (he0.symm ▸ hU)
  rw [show 𝓝 (0 : ProfiniteIntegerRing) =
    Filter.comap (fun x : ProfiniteIntegerRing => x.val) (𝓝 0) from nhds_subtype_eq_comap] at hpre
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hpre
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, hI, V, hV, hVW⟩ := hW
  let k := ∏ i ∈ hI.toFinset, (i : ℕ)
  have hk : 0 < k := Finset.prod_pos (fun i _ => i.property)
  refine ⟨⟨k, hk⟩, fun r => ?_⟩
  let a : ProfiniteIntegerRing := (k : ProfiniteIntegerRing) * e.symm r
  have ha : a.val ∈ I.pi V := by
    intro i hi
    have hz : (k : ZMod i.val) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr
      (Finset.dvd_prod_of_mem (fun i : ℕ+ => i.val) (hI.mem_toFinset.mpr hi))
    change ProfiniteIntegerRing.reduction i a ∈ V i
    have hr : ProfiniteIntegerRing.reduction i a = 0 := by
      simp only [a, map_mul, map_natCast, hz, zero_mul]
    rw [hr]
    exact mem_of_mem_nhds (hV i)
  have hmem : (e a : Af) ∈ U := hWU (hVW ha)
  have hra : (e a : Af) = k • (r : Af) := by
    change ((e ((k : ProfiniteIntegerRing) * e.symm r) : Rf) : Af) = _
    rw [map_mul, map_natCast, e.apply_symm_apply]
    change ((Rf).subtype ((k : Rf) * r)) = _
    rw [map_mul, map_natCast, nsmul_eq_mul]
    rfl
  exact hra ▸ hmem

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "Vf" => Af ⊗[ℚ] A
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "Ixs" => Fin (Module.finrank ℤ (D.harrisHodgePELIntegralLattice C))
local notation "psi" => D.harrisHodgePELForm C
local notation "G" => ScalarExtensionSimilitudePoints A A Af psi
local notation "K" => harrisIntegralAdeleCongruence D C
local notation "opG" => ScalarExtensionSimilitudePoints.operator (D := A) (V := A) (R := Af) (ψ := psi)
local notation "multG" => ScalarExtensionSimilitudePoints.multiplier (D := A) (V := A) (R := Af) (ψ := psi)
local instance congruenceBasisIntegralScalars : Module Rf Vf := Module.compHom _ (Rf).subtype
local instance congruenceBasisTopology : TopologicalSpace Vf := moduleTopology Af Vf
local instance congruenceBasisContinuousAdd : ContinuousAdd Vf :=
  IsModuleTopology.toContinuousAdd Af Vf

private theorem exists_integralSource_multiples_mem (h : RationalProfiniteIntegerAdeleComparison)
    {W : Set Vf} (hW : W ∈ 𝓝 (0 : Vf)) :
    ∃ m : ℕ+, (fun y : Vf => m.val • y) '' (Λf : Set Vf) ⊆ W := by
  classical
  let b := harrisIntegralSourceAdelicBasis D C
  let e := b.equivFun.symm
  have hc : Continuous e := by
    change Continuous (fun r : Ixs → Af => e r)
    simp only [e, Module.Basis.equivFun_symm_apply]
    exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)
  have he : e ⁻¹' W ∈ 𝓝 (0 : Ixs → Af) :=
    hc.continuousAt.preimage_mem_nhds ((map_zero e).symm ▸ hW)
  rw [nhds_pi, Filter.mem_pi] at he
  obtain ⟨I, _, U, hU, hUW⟩ := he
  have ht : (⋂ i, U i) ∈ 𝓝 (0 : Af) := Filter.iInter_mem.mpr hU
  obtain ⟨m, hm⟩ := exists_integralAdele_multiples_mem h ht
  refine ⟨m, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  let r := harrisIntegralSourceCoordinates D C ⟨y, hy⟩
  have hr : e (fun i => (r i : Af)) = y := b.equivFun.symm_apply_apply y
  have hv : (fun i => m.val • (r i : Af)) ∈ I.pi U := fun i _ =>
    Set.mem_iInter.mp (hm (r i)) i
  have hd : e (fun i => m.val • (r i : Af)) = m.val • y :=
    (map_nsmul e (m.val) (fun i => (r i : Af))).trans (congrArg (m.val • ·) hr)
  change m.val • y ∈ W
  exact hd ▸ hUW hv

/-- Congruence kernel inclusion follows the divisibility ordering on positive moduli. -/
theorem harrisIntegralAdeleCongruence_le_of_dvd {m k : ℕ} (h : m ∣ k) : K k ≤ K m := by
  obtain ⟨d, rfl⟩ := h
  intro g hg
  obtain ⟨hs, hh⟩ := (mem_harrisIntegralAdeleCongruence D C _ g).mp hg
  apply (mem_harrisIntegralAdeleCongruence D C _ g).mpr
  refine ⟨hs, fun v hv => ?_⟩
  obtain ⟨w, hw, he⟩ := hh v hv
  exact ⟨d • w, (Λf).toAddSubgroup.nsmul_mem hw d, (mul_smul m d w).symm.trans he⟩

/-- The filter generated by all positive-modulus principal congruence subgroups. -/
def harrisIntegralAdeleCongruenceFilter : Filter G :=
  ⨅ m : ℕ+, 𝓟 (K m.val : Set G)

local notation "KFilter" => harrisIntegralAdeleCongruenceFilter D C

private theorem congruenceFilter_basis : (KFilter).HasBasis (fun _ : ℕ+ => True)
    (fun m => (K m.val : Set G)) := by
  apply Filter.hasBasis_iInf_principal
  intro m k
  exact ⟨m * k, harrisIntegralAdeleCongruence_le_of_dvd D C (dvd_mul_right m.val k.val),
    harrisIntegralAdeleCongruence_le_of_dvd D C (dvd_mul_left k.val m.val)⟩

set_option maxHeartbeats 1600000 in
/-- The congruence subgroups form the identity neighbourhood basis in the
actual Harris scalar-extension similitude group. -/
theorem harrisIntegralAdeleCongruenceFilter_eq_nhds
    (h : RationalProfiniteIntegerAdeleComparison) : KFilter = 𝓝 (1 : G) := by
  let Filt := KFilter
  let b := harrisIntegralSourceAdelicBasis D C
  have hb (i : Ixs) : b i ∈ Λf := by
    change harrisIntegralSourceAdelicBasis D C i ∈ Λf
    rw [harrisIntegralSourceAdelicBasis, Module.Basis.baseChange_apply,
      Module.Basis.extendOfIsLattice_apply]
    exact D.harrisHodgePELIntegralAdeleSpan_tmul C _
  have hK (m : ℕ+) : (K m.val : Set G) ∈ Filt :=
    (congruenceFilter_basis D C).mem_iff.mpr ⟨m, trivial, Set.Subset.rfl⟩
  have hi : Tendsto (fun g : G => g⁻¹) Filt Filt := by
    refine Filter.tendsto_def.mpr fun W hW => ?_
    obtain ⟨m, _, hm⟩ := (congruenceFilter_basis D C).mem_iff.mp hW
    exact Filter.mem_of_superset (hK m) (fun g hg => hm ((K m.val).inv_mem hg))
  have hsmall (v : Vf) (hv : v ∈ Λf) :
      Tendsto (fun g : G => opG g v - v) Filt (𝓝 0) := by
    refine Filter.tendsto_def.mpr fun W hW => ?_
    obtain ⟨m, hm⟩ := exists_integralSource_multiples_mem D C h hW
    exact Filter.mem_of_superset (hK m) (fun g hg => hm
      (((mem_harrisIntegralAdeleCongruence D C m.val g).mp hg).2 v hv))
  have hvec (v : Vf) (hv : v ∈ Λf) : Tendsto (fun g : G => opG g v) Filt (𝓝 v) := by
    have hl := (hsmall v hv).add (tendsto_const_nhds (x := v))
    simpa only [zero_add, sub_add_cancel] using hl
  have hop (v : Vf) : Tendsto (fun g : G => opG g v) Filt (𝓝 v) := by
    have hs (i : Ixs) : Tendsto (fun g : G => b.repr v i • opG g (b i)) Filt
        (𝓝 (b.repr v i • b i)) := tendsto_const_nhds.smul (hvec (b i) (hb i))
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hs i)
    rw [b.sum_repr v] at ht
    refine ht.congr (fun g => ?_)
    calc
      (∑ i, b.repr v i • opG g (b i)) = ∑ i, opG g (b.repr v i • b i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact ((opG g).map_smul (b.repr v i) (b i)).symm
      _ = opG g (∑ i, b.repr v i • b i) := (map_sum (opG g) _ _).symm
      _ = opG g v := congrArg (opG g) (b.sum_repr v)
  have hsymm (v : Vf) : Tendsto (fun g : G => g.val.1.symm v) Filt (𝓝 v) :=
    (hop v).comp hi
  let : IsSimpleRing A := D.simple
  let : Module.Finite ℚ A := (hodgeRationalPELConditions D C).finite_module
  let phi := (psi).baseChange Af
  obtain ⟨v, w, hφ⟩ := (hodgeRationalPELConditions D C).baseChange_attains_one Af
  have hbil : Continuous (fun a : Vf × Vf => phi a.1 a.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left phi
  have hmult : Tendsto (fun g : G => (multG g : Af)) Filt (𝓝 1) := by
    have hpair : Tendsto (fun g : G => (opG g v, opG g w)) Filt (𝓝 (v, w)) :=
      (hop v).prodMk_nhds (hop w)
    have hform : Tendsto (fun a : Vf × Vf => phi a.1 a.2) (𝓝 (v, w)) (𝓝 (phi v w)) :=
      hbil.continuousAt
    have hlim : Tendsto (fun g : G => phi (opG g v) (opG g w)) Filt (𝓝 (phi v w)) :=
      Filter.Tendsto.comp (f := fun g : G => (opG g v, opG g w))
        (g := fun a : Vf × Vf => phi a.1 a.2) hform hpair
    change phi v w = 1 at hφ
    rw [hφ] at hlim
    refine hlim.congr (fun g => ?_)
    have hg : phi (opG g v) (opG g w) = (multG g : Af) * phi v w := g.property v w
    rwa [hφ, mul_one] at hg
  have hmultInv : Tendsto (fun g : G => Units.val ((multG g)⁻¹)) Filt (𝓝 1) := by
    exact (hmult.comp hi).congr (fun g => congrArg Units.val (map_inv multG g))
  have hmulU : Tendsto (fun g : G => multG g) Filt (𝓝 1) := by
    apply Units.isInducing_embedProduct.tendsto_nhds_iff.mpr
    have hOpp : Tendsto (fun g : G => MulOpposite.op (Units.val ((multG g)⁻¹))) Filt
        (𝓝 (MulOpposite.op (1 : Af))) :=
      (MulOpposite.continuous_op.continuousAt (x := (1 : Af))).tendsto.comp hmultInv
    exact hmult.prodMk_nhds hOpp
  have ht : Tendsto (fun g : G => g) Filt (𝓝 1) := by
    apply (ScalarExtensionSimilitudePoints.isInducing_coordinates (D := A) (V := A)
      (R := Af) (ψ := psi)).tendsto_nhds_iff.mpr
    exact ((tendsto_pi_nhds.mpr hop).prodMk_nhds (tendsto_pi_nhds.mpr hsymm)).prodMk_nhds hmulU
  apply le_antisymm
  · exact tendsto_id'.mp ht
  · refine le_iInf (fun m => ?_)
    exact le_principal_iff.mpr ((harrisIntegralAdeleCongruence_isOpen D C m.val m.property.ne').mem_nhds
      (Subgroup.one_mem _))

/-- Every open Harris Hodge level contains a principal congruence subgroup. -/
theorem exists_harrisIntegralAdeleCongruence_le
    (h : RationalProfiniteIntegerAdeleComparison) (U : OpenSubgroup G) :
    ∃ m : ℕ+, K m.val ≤ U.toSubgroup := by
  have hg : (U : Set G) ∈ KFilter := by
    rw [harrisIntegralAdeleCongruenceFilter_eq_nhds D C h]
    exact U.isOpen.mem_nhds U.one_mem
  obtain ⟨m, _, hm⟩ := (congruenceFilter_basis D C).mem_iff.mp hg
  exact ⟨m, hm⟩

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
