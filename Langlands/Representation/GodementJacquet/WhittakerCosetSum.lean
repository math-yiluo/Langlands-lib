import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.PrincipalLevelDominance

/-!
# Finite coset sums over a compact subgroup

A compact subgroup `K` of a topological group is a finite disjoint union of left
cosets of an open subgroup `K₀ ≤ K`. Hence the Haar integral over `K` of a
function that is invariant under right translation by `K₀` is a finite sum of
values times the mass of `K₀`. For `GL_(n+1)` of a `p`-adic field, every
full-matrix test function is invariant under right translation by some open
subgroup. See the paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet.CosetSum

open MeasureTheory Topology HarmonicAnalysis
open scoped ENNReal Pointwise

universe uF uG

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact subgroup is the disjoint union of finitely many left cosets of an
open subgroup contained in it. -/
theorem exists_finset_leftCosets (K K₀ : Subgroup G) (hK : IsCompact (K : Set G))
    (hK₀ : IsOpen (K₀ : Set G)) (hle : K₀ ≤ K) :
    ∃ S : Finset G, (S : Set G) ⊆ K ∧
      (S : Set G).PairwiseDisjoint (fun k => k • (K₀ : Set G)) ∧
      (K : Set G) = ⋃ k ∈ S, k • (K₀ : Set G) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let H : Subgroup K := K₀.subgroupOf K
  have hH : IsOpen (H : Set K) := Subgroup.subgroupOf_isOpen K K₀ hK₀
  have : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hmemS : ∀ x, x ∈ (Finset.univ.image fun q : K ⧸ H => ((Quotient.out q : K) : G)) ↔
      ∃ q : K ⧸ H, ((Quotient.out q : K) : G) = x := by
    intro x
    simp
  refine ⟨Finset.univ.image fun q : K ⧸ H => ((Quotient.out q : K) : G), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, rfl⟩ := (hmemS x).1 hx
    exact (Quotient.out q).2
  · intro x hx y hy hxy
    obtain ⟨q, rfl⟩ := (hmemS x).1 hx
    obtain ⟨q', rfl⟩ := (hmemS y).1 hy
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    apply hxy
    have hmem : (Quotient.out q : K)⁻¹ * Quotient.out q' ∈ H := by
      rw [Subgroup.mem_subgroupOf]
      have e : (((Quotient.out q : K)⁻¹ * Quotient.out q' : K) : G) = a * b⁻¹ := by
        have hab' : ((Quotient.out q' : K) : G) * b = ((Quotient.out q : K) : G) * a := hab
        push_cast
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hab', mul_inv_cancel_right]
      rw [e]
      exact K₀.mul_mem ha (K₀.inv_mem hb)
    have hq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.mpr hmem
    rw [hq]
  · ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H ⟨x, hx⟩
      refine ⟨((Quotient.out (QuotientGroup.mk ⟨x, hx⟩ : K ⧸ H) : K) : G),
        (hmemS _).2 ⟨_, rfl⟩, ?_⟩
      refine Set.mem_smul_set.2 ⟨((h : K) : G)⁻¹, K₀.inv_mem (Subgroup.mem_subgroupOf.1 h.2), ?_⟩
      rw [hh, smul_eq_mul]
      push_cast
      rw [mul_inv_cancel_right]
    · rintro ⟨k, hk, hx⟩
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
      obtain ⟨q, rfl⟩ := (hmemS k).1 hk
      exact K.mul_mem (Quotient.out q).2 (hle hy)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

/-- **Finite coset sums.** For a compact subgroup `K` and an open subgroup
`K₀ ≤ K`, there are finitely many points `k ∈ K` such that the integral over
`K` of every function invariant under right translation by `K₀` (on `K`) is the
sum of its values at these points times the mass of `K₀`, both for lower
Lebesgue integrals and for Bochner integrals of complex functions. -/
theorem exists_cosetSum (K K₀ : Subgroup G) (hK : IsCompact (K : Set G))
    (hK₀ : IsOpen (K₀ : Set G)) (hle : K₀ ≤ K) :
    ∃ S : Finset G, (S : Set G) ⊆ K ∧
      (∀ f : G → ℝ≥0∞, (∀ k ∈ K, ∀ k₀ ∈ K₀, f (k * k₀) = f k) →
        ∫⁻ x in (K : Set G), f x ∂μ = ∑ k ∈ S, μ (K₀ : Set G) * f k) ∧
      (∀ f : G → ℂ, (∀ k ∈ K, ∀ k₀ ∈ K₀, f (k * k₀) = f k) →
        ∫ x in (K : Set G), f x ∂μ = ∑ k ∈ S, (μ.real (K₀ : Set G) : ℂ) * f k) := by
  obtain ⟨S, hSK, hd, hU⟩ := exists_finset_leftCosets K K₀ hK hK₀ hle
  have hm : ∀ k ∈ S, MeasurableSet (k • (K₀ : Set G)) :=
    fun k _ => (hK₀.leftCoset k).measurableSet
  have hcoset : ∀ k ∈ S, ∀ x ∈ k • (K₀ : Set G), ∃ k₀ ∈ K₀, x = k * k₀ := by
    intro k _ x hx
    obtain ⟨k₀, hk₀, rfl⟩ := Set.mem_smul_set.1 hx
    exact ⟨k₀, hk₀, rfl⟩
  have hK₀fin : μ (K₀ : Set G) ≠ ⊤ :=
    (measure_mono (show (K₀ : Set G) ⊆ K from hle)).trans_lt hK.measure_lt_top |>.ne
  refine ⟨S, hSK, fun f hf => ?_, fun f hf => ?_⟩
  · rw [hU, lintegral_biUnion_finset hd hm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hc : Set.EqOn f (fun _ => f k) (k • (K₀ : Set G)) := by
      intro x hx
      obtain ⟨k₀, hk₀, rfl⟩ := hcoset k hk x hx
      exact hf k (hSK hk) k₀ hk₀
    rw [setLIntegral_congr_fun (hm k hk) hc, setLIntegral_const, measure_smul, mul_comm]
  · have hc : ∀ k ∈ S, Set.EqOn f (fun _ => f k) (k • (K₀ : Set G)) := by
      intro k hk x hx
      obtain ⟨k₀, hk₀, rfl⟩ := hcoset k hk x hx
      exact hf k (hSK hk) k₀ hk₀
    have hint : ∀ k ∈ S, IntegrableOn f (k • (K₀ : Set G)) μ := by
      intro k hk
      refine (integrableOn_congr_fun (hc k hk) (hm k hk)).2 ?_
      exact integrableOn_const (by rw [measure_smul]; exact hK₀fin)
    rw [hU, integral_biUnion_finset S hm hd hint]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [setIntegral_congr_fun (hm k hk) (hc k hk), setIntegral_const, Measure.real,
      measure_smul, Complex.real_smul]
    rfl

end Generic

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance cosetSumTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance cosetSumValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance cosetSumLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

variable {n : ℕ}

/-- A full-matrix test function is invariant under right multiplication by every
element of some neighborhood of the identity. -/
theorem exists_nhds_matrixTest_rightInvariant (Φ : MatrixTestFunction n F.Carrier) :
    ∃ U ∈ 𝓝 (1 : Langlands.GeneralLinear (n + 1) F.Carrier),
      ∀ g ∈ U, ∀ M, Φ (M * g.val) = Φ M := by
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let X := Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier
  have hcont : Continuous fun z : G × X => z.2 * z.1.val :=
    continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst)
  have hlc : IsLocallyConstant fun z : G × X => Φ (z.2 * z.1.val) - Φ z.2 :=
    IsLocallyConstant.comp₂ ((SchwartzBruhat.locallyConstant Φ).comp_continuous hcont)
      ((SchwartzBruhat.locallyConstant Φ).comp_continuous continuous_snd) (· - ·)
  have hsub : ({1} : Set G) ×ˢ tsupport (Φ : X → ℂ) ⊆
      {z : G × X | Φ (z.2 * z.1.val) - Φ z.2 = 0} := by
    rintro ⟨g, M⟩ ⟨hg, -⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show Φ (M * (1 : G).val) - Φ M = 0
    rw [Units.val_one, Matrix.mul_one, sub_self]
  obtain ⟨u, v, hu, -, h1u, hSv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (SchwartzBruhat.hasCompactSupport Φ).isCompact (hlc.isOpen_fiber 0) hsub
  have hun : u ∈ 𝓝 (1 : G) := hu.mem_nhds (h1u rfl)
  have key : ∀ h ∈ u, ∀ N ∈ tsupport (Φ : X → ℂ), Φ (N * h.val) = Φ N := by
    intro h hh N hN
    have hm : Φ (N * h.val) - Φ N = 0 := huv (Set.mk_mem_prod hh (hSv hN))
    exact sub_eq_zero.mp hm
  refine ⟨u ∩ u⁻¹, Filter.inter_mem hun (inv_mem_nhds_one G hun), ?_⟩
  rintro g ⟨hgu, hgu'⟩ M
  by_cases hM : M ∈ tsupport (Φ : X → ℂ)
  · exact key g hgu M hM
  by_cases hgM : M * g.val ∈ tsupport (Φ : X → ℂ)
  · have hinv := key g⁻¹ (Set.mem_inv.mp hgu') _ hgM
    have e : M * g.val * (g⁻¹ : G).val = M := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [e] at hinv
    exact hinv.symm
  · rw [image_eq_zero_of_notMem_tsupport hM, image_eq_zero_of_notMem_tsupport hgM]

/-- The integral subgroup `GL_(n+1)(O)` is compact. -/
theorem isCompact_integralSubgroup :
    IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
  Langlands.GeneralLinear.isCompact_integralRange F.Carrier (n + 1)

/-- The integral subgroup `GL_(n+1)(O)` is open. -/
theorem isOpen_integralSubgroup :
    IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
  Conductor.isOpen_integralSubgroup _ _
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier))

/-- An open subgroup of `GL_(n+1)(O)` under which a full-matrix test function and
a function on the group, right invariant under some open subgroup, are both
right invariant. -/
theorem exists_openSubgroup_rightInvariant (Φ : MatrixTestFunction n F.Carrier)
    (W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hW : ∀ g, ∀ k ∈ L, W (g * k) = W g) :
    ∃ K₀ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      (K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier)) ≤
        Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n ∧
      ∀ k ∈ K₀, (∀ M, Φ (M * k.val) = Φ M) ∧ ∀ g, W (g * k) = W g := by
  obtain ⟨U, hU, hΦ⟩ := exists_nhds_matrixTest_rightInvariant F Φ
  let T := F.canonicalTopologicalData
  have hK : (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∈ 𝓝 1 :=
    (isOpen_integralSubgroup F).mem_nhds (one_mem _)
  have hL : (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∈ 𝓝 1 :=
    L.isOpen.mem_nhds (one_mem L)
  obtain ⟨K₀, -, hK₀⟩ := T.generalLinearCompactOpen (n + 1) _
    (Filter.inter_mem (Filter.inter_mem hU hL) hK)
  exact ⟨K₀, fun k hk => (hK₀ hk).2, fun k hk => ⟨hΦ k (hK₀ hk).1.1,
    fun g => hW g k (hK₀ hk).1.2⟩⟩

end Padic

end Langlands.GodementJacquet.CosetSum
