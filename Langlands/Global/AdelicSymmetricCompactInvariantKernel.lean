import Langlands.Analysis.CompactManifoldIntegrableWeight
import Langlands.Global.AdelicRightConvolutionDifferentiation
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Group.Integral

/-! # Symmetric adelic test kernels central under an infinite compact subgroup -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set Topology TopologicalSpace Filter
open scoped CategoryTheory.MonObj Classical Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints

private theorem exists_conjugationNeighborhood {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] (K : Subgroup X) (hK : IsCompact (K : Set X))
    {V : Set X} (hVo : IsOpen V) (hV₁ : 1 ∈ V) :
    ∃ W ∈ 𝓝 (1 : X), ∀ k ∈ K, ∀ x ∈ W, k * x * k⁻¹ ∈ V := by
  let S : Set (X × X) := {p | p.1 * p.2 * p.1⁻¹ ∈ V}
  have hS : IsOpen S := hVo.preimage ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hP : S ∈ (𝓝ˢ (K : Set X)) ×ˢ 𝓝 (1 : X) := hK.mem_nhdsSet_prod_of_forall fun k _ => by
    rw [← nhds_prod_eq]
    exact hS.mem_nhds (show k * 1 * k⁻¹ ∈ V by simpa using hV₁)
  obtain ⟨O, hO, W, hW, hS'⟩ := Filter.mem_prod_iff.mp hP
  refine ⟨W, hW, fun k hk x hx => ?_⟩
  change (k, x) ∈ S
  exact hS' ⟨mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hO k hk), hx⟩

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G

/-- The identity has real nonnegative smooth adelic kernels of mass one inside
any neighborhood, symmetric under inversion and invariant under conjugation by
any prescribed compact subgroup of the infinite adelic group. -/
def AdelicSymmetricCompactInvariantKernelStatement : Prop :=
  ∀ {d : ℕ}, SmoothOfRelativeDimension d G.X.hom →
  ∀ (K : Subgroup A∞), IsCompact (K : Set A∞) →
  ∀ U : Set A, U ∈ 𝓝 (1 : A) →
    ∃ h : A → ℝ, IsAdelicTestFunction F G (fun x => (h x : ℂ)) ∧
      tsupport h ⊆ U ∧ (∀ x, 0 ≤ h x) ∧ (∫ x, h x ∂(Measure.haar : Measure A)) = 1 ∧
      (∀ x, h x⁻¹ = h x) ∧
      (∀ k ∈ K, ∀ x, h ((ofInfinite F G k)⁻¹ * x * ofInfinite F G k) = h x)

theorem adelicSymmetricCompactInvariantKernel :
    AdelicSymmetricCompactInvariantKernelStatement (F := F) (G := G) := by
  intro d hsmooth K hK U hU
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let I := 𝓘(ℝ, smoothModel F d)
  have hU' : (split F G).symm ⁻¹' U ∈ 𝓝 ((1 : A∞), (1 : A_f)) := by
    apply (split F G).symm.continuous.continuousAt.preimage_mem_nhds
    change U ∈ 𝓝 ((split F G).symm 1)
    rwa [map_one]
  obtain ⟨V, W, hVo, hV₁, hWo, hW₁, hVW⟩ := mem_nhds_prod_iff'.mp hU'
  obtain ⟨S, hS, hSV⟩ := exists_conjugationNeighborhood K hK hVo hV₁
  have hS' : S ∩ Inv.inv ⁻¹' S ∈ 𝓝 (1 : A∞) :=
    inter_mem hS (continuous_inv.continuousAt.preimage_mem_nhds (by simpa only [inv_one] using hS))
  obtain ⟨O, hOS, hOo, hO₁⟩ := mem_nhds_iff.mp hS'
  obtain ⟨L, hL, hL₁, hLO⟩ := exists_compact_subset hOo hO₁
  obtain ⟨b, hbSupp, hbSmooth, hbNonneg⟩ := isOpen_interior.exists_contMDiff_support_eq
    (n := (⊤ : ℕ∞)) I (s := interior L)
  let g (x : A∞) : ℝ := b x + b x⁻¹
  have hgSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g :=
    hbSmooth.add (hbSmooth.comp (contMDiff_inv I ∞))
  have hgNonneg (x : A∞) : 0 ≤ g x := add_nonneg (hbNonneg _) (hbNonneg _)
  have hb₁ : 0 < b 1 := lt_of_le_of_ne (hbNonneg _) (by simpa [← hbSupp] using hL₁ : b 1 ≠ 0).symm
  have hg₁ : 0 < g 1 := by simpa [g] using add_pos hb₁ hb₁
  have hgInv (x : A∞) : g x⁻¹ = g x := by simp [g, add_comm]
  let Ls : Set A∞ := L ∪ Inv.inv '' L
  have hLs : IsCompact Ls := hL.union (hL.image continuous_inv)
  have hLsS : Ls ⊆ S := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact (hOS (hLO hx)).1
    · exact (hOS (hLO hy)).2
  have hgZero {x : A∞} (hx : x ∉ Ls) : g x = 0 := by
    have hbZ {y : A∞} (hy : y ∉ L) : b y = 0 := by
      by_contra hby
      exact hy (interior_subset (hbSupp ▸ hby))
    have hxi : x⁻¹ ∉ L := fun hi => hx (Or.inr ⟨x⁻¹, hi, inv_inv x⟩)
    simp [g, hbZ (fun h => hx (Or.inl h)), hbZ hxi]
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let νK : Measure K := Measure.haarMeasure (⊤ : PositiveCompacts K)
  let : νK.IsHaarMeasure := by dsimp [νK]; infer_instance
  let : IsProbabilityMeasure νK := ⟨by
    change Measure.haarMeasure (⊤ : PositiveCompacts K) Set.univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts K)))⟩
  let w (x : A∞) : ℝ := ∫ k : K, g (k.val⁻¹ * x * k.val) ∂νK
  let j : C(K, A∞) := ⟨Subtype.val, continuous_subtype_val⟩
  let φ (p : A∞ × A∞) : ℂ := (g (p.2⁻¹ * p.1 * p.2) : ℂ)
  have hφ : ContMDiff (I.prod I) 𝓘(ℝ, ℂ) ∞ φ := by
    apply Complex.ofRealCLM.contDiff.contMDiff.comp
    exact hgSmooth.comp (((contMDiff_snd.inv).mul contMDiff_fst).mul contMDiff_snd)
  have hwSmooth : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x => (w x : ℂ)) := by
    have h := (Langlands.Analysis.compactManifoldIntegrableWeight K (smoothModel F d) A∞
      (smoothModel F d) A∞ ℂ νK (fun _ => 1) measurable_const (integrable_const _) j φ hφ).2.1
    simpa only [w, φ, j, ContinuousMap.coe_mk, one_smul, integral_complex_ofReal] using h
  have hwC : Continuous w := by
    have hc := Complex.continuous_re.comp hwSmooth.continuous
    change Continuous (fun x => ((w x : ℂ)).re) at hc
    simpa only [Complex.ofReal_re] using hc
  have hwNonneg (x : A∞) : 0 ≤ w x := integral_nonneg fun k => hgNonneg _
  have hw₁ : 0 < w 1 := by simpa [w] using hg₁
  have hwInv (x : A∞) : w x⁻¹ = w x := by
    unfold w
    apply integral_congr_ae (Eventually.of_forall fun k => ?_)
    rw [← hgInv (k.val⁻¹ * x * k.val)]
    simp [mul_assoc]
  have hwConj (k : A∞) (hk : k ∈ K) (x : A∞) : w (k⁻¹ * x * k) = w x := by
    have he := integral_mul_left_eq_self («μ» := νK) (fun l : K => g (l.val⁻¹ * x * l.val)) (⟨k, hk⟩ : K)
    simpa [w, mul_assoc] using he
  let P : Set A∞ := (fun p : A∞ × A∞ => p.1 * p.2 * p.1⁻¹) '' ((K : Set A∞) ×ˢ Ls)
  have hP : IsCompact P := (hK.prod hLs).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hPV : P ⊆ V := by rintro _ ⟨⟨k, x⟩, hx, rfl⟩; exact hSV k hx.1 x (hLsS hx.2)
  have hwZero {x : A∞} (hx : x ∉ P) : w x = 0 := by
    unfold w
    rw [show (fun k : K => g (k.val⁻¹ * x * k.val)) = 0 from funext fun k => hgZero fun hy =>
      hx ⟨(k.val, k.val⁻¹ * x * k.val), ⟨k.property, hy⟩, by simp [mul_assoc]⟩]
    exact integral_zero K ℝ
  obtain ⟨J, hJc, hJW⟩ := ((finiteAdelicGroupCompactOpenBasis F G).2.mem_iff).mp (hWo.mem_nhds hW₁)
  let c : A_f → ℝ := (J : Set A_f).indicator fun _ => 1
  have hc : Continuous c := J.isClopen.continuous_indicator continuous_const
  have hcNonneg (x : A_f) : 0 ≤ c x := indicator_nonneg (fun _ _ => zero_le_one) x
  have hcInv (x : A_f) : c x⁻¹ = c x := by
    have he : x⁻¹ ∈ J ↔ x ∈ J := J.toSubgroup.inv_mem_iff
    simp [c, indicator_apply, he]
  have hcR (l : A_f) (hl : l ∈ J) (x : A_f) : c (x * l) = c x := by
    have he : x * l ∈ J ↔ x ∈ J := J.toSubgroup.mul_mem_cancel_right hl
    simp [c, indicator_apply, he]
  have hcL (l : A_f) (hl : l ∈ J) (x : A_f) : c (l * x) = c x := by
    have he : l * x ∈ J ↔ x ∈ J := J.toSubgroup.mul_mem_cancel_left hl
    simp [c, indicator_apply, he]
  let f (x : A) := w (infinite F G x) * c (finite F G x)
  have hfC : Continuous f := (hwC.comp (infinite F G).continuous).mul (hc.comp (finite F G).continuous)
  have hfNonneg (x : A) : 0 ≤ f x := mul_nonneg (hwNonneg _) (hcNonneg _)
  have hf₁ : 0 < f 1 := by simpa [f, c, J.one_mem] using hw₁
  have hB : IsCompact ((split F G).symm '' (P ×ˢ (J : Set A_f))) :=
    (hP.prod hJc).image (split F G).symm.continuous
  have hfSupp : tsupport f ⊆ (split F G).symm '' (P ×ˢ (J : Set A_f)) := by
    apply closure_minimal _ hB.isClosed
    intro x hx
    refine ⟨(infinite F G x, finite F G x), ⟨?_, ?_⟩, (split F G).symm_apply_apply x⟩
    · by_contra hx'
      exact hx (by simp [f, hwZero hx'])
    · by_contra hx'
      exact hx (by simp [f, c, indicator_of_notMem hx'])
  have hfS : HasCompactSupport f := hB.of_isClosed_subset (isClosed_tsupport f) hfSupp
  let m := ∫ x, f x ∂(Measure.haar : Measure A)
  have hm : 0 < m := hfC.integral_pos_of_hasCompactSupport_nonneg_nonzero hfS hfNonneg hf₁.ne'
  let h (x : A) : ℝ := m⁻¹ * f x
  have hhS : HasCompactSupport h := hfS.mul_left
  refine ⟨h, ⟨⟨Complex.continuous_ofReal.comp (continuous_const.mul hfC),
    ?_, J.toSubgroup, J.isOpen, ?_⟩, hhS.comp_left Complex.ofReal_zero, J.toSubgroup, J.isOpen, ?_⟩,
    ?_, fun x => mul_nonneg (inv_nonneg.mpr hm.le) (hfNonneg x), ?_, ?_, ?_⟩
  · intro y
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    change ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun a => (h (pair F G a y) : ℂ))
    have hhDiff : ContDiff ℝ ∞ (fun z : ℂ => ((m⁻¹ : ℝ) : ℂ) * (z * (c y : ℂ))) :=
      contDiff_const.mul (contDiff_id.mul contDiff_const)
    simp only [h, f, infinite_pair, finite_pair, Complex.ofReal_mul]
    exact hhDiff.contMDiff.comp hwSmooth
  · intro l hl x
    change (h (x * ofFinite F G l) : ℂ) = (h x : ℂ)
    simp only [h, f, map_mul, infinite_ofFinite, mul_one, finite_ofFinite, hcR l hl]
  · intro l hl x
    change (h (ofFinite F G l * x) : ℂ) = (h x : ℂ)
    simp only [h, f, map_mul, infinite_ofFinite, one_mul, finite_ofFinite, hcL l hl]
  · have hhf : tsupport h ⊆ tsupport f := tsupport_mul_subset_right
    exact hhf.trans (hfSupp.trans (by
      rintro _ ⟨y, hy, rfl⟩; exact hVW ⟨hPV hy.1, hJW hy.2⟩))
  · rw [show (fun x => h x) = (fun x => m⁻¹ * f x) from rfl, integral_const_mul]
    exact inv_mul_cancel₀ hm.ne'
  · intro x
    simp only [h, f, map_inv, hwInv, hcInv]
  · intro k hk x
    simp only [h, f, map_mul, map_inv, infinite_ofInfinite, finite_ofInfinite,
      inv_one, one_mul, mul_one, hwConj k hk]

end Langlands.Global.AdelicGroupPoints
