import Langlands.Geometry.Building.KPOptimalPoints
import Langlands.Geometry.Building.AffineDerivativeRootPairing
import Mathlib.Topology.Algebra.Order.Archimedean

/-! # Rational coordinates for affine roots (KP §13.4) -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.AffineRootSystem

open Module Set

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

private def shift (ψ : A →ᵃ[ℝ] ℝ) (t : ℝ) : A →ᵃ[ℝ] ℝ :=
  ψ + AffineMap.const ℝ A t

@[simp] private theorem shift_apply (ψ : A →ᵃ[ℝ] ℝ) (t : ℝ) (x : A) :
    shift ψ t x = ψ x + t := rfl

@[simp] private theorem shift_linear (ψ : A →ᵃ[ℝ] ℝ) (t : ℝ) :
    (shift ψ t).linear = ψ.linear := by simp [shift]

private theorem shift_shift (ψ : A →ᵃ[ℝ] ℝ) (s t : ℝ) :
    shift (shift ψ s) t = shift ψ (s + t) := by
  ext x
  simp only [shift_apply, add_assoc]

/-- The translations preserving one derivative fibre in both directions. -/
private def fibreShiftGroup (Ψ : Set (A →ᵃ[ℝ] ℝ)) (a : Module.Dual ℝ V) : AddSubgroup ℝ where
  carrier := {t | ∀ ψ ∈ Ψ, ψ.linear = a → shift ψ t ∈ Ψ ∧ shift ψ (-t) ∈ Ψ}
  zero_mem' := by
    have hzero (ψ : A →ᵃ[ℝ] ℝ) : shift ψ 0 = ψ := AffineMap.ext fun _ => add_zero _
    intro ψ hψ _
    simpa only [neg_zero, hzero] using And.intro hψ hψ
  add_mem' := by
    intro s t hs ht ψ hψ hlin
    have hp := hs ψ hψ hlin
    constructor
    · rw [← shift_shift]
      exact (ht _ hp.1 ((shift_linear _ _).trans hlin)).1
    · rw [neg_add_rev, add_comm (-t) (-s), ← shift_shift]
      exact (ht _ hp.2 ((shift_linear _ _).trans hlin)).2
  neg_mem' := by
    intro t ht ψ hψ hlin
    exact ⟨(ht ψ hψ hlin).2, by simpa only [neg_neg] using (ht ψ hψ hlin).1⟩

private theorem exists_zmultiples_fibreShiftGroup (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    ∃ d, fibreShiftGroup Ψ ψ.linear = AddSubgroup.zmultiples d := by
  let H := fibreShiftGroup Ψ ψ.linear
  let T : Set ℝ := Ioo (-1 : ℝ) 1 ∩ (H : Set ℝ)
  have hmap : MapsTo (shift ψ) T
      {η | η ∈ Ψ ∧ η.linear = ψ.linear ∧ ∀ x : A, |η x - ψ x| ≤ 1} := by
    rintro t ⟨ht, hH⟩
    refine ⟨(hH ψ hψ rfl).1, shift_linear _ _, fun x => ?_⟩
    rw [shift_apply, add_sub_cancel_left]
    exact abs_le.2 ⟨ht.1.le, ht.2.le⟩
  have hinj : InjOn (shift ψ) T := by
    intro t _ t' _ htt'
    obtain ⟨x⟩ : Nonempty A := inferInstance
    have h := congrArg (fun f : A →ᵃ[ℝ] ℝ => f x) htt'
    exact add_left_cancel h
  have hfin : T.Finite :=
    Set.Finite.of_finite_image ((hΨ.finite_bounded ψ hψ 1).subset hmap.image_subset) hinj
  have hd : ¬ Dense (H : Set ℝ) := by
    intro hd
    have hsub := hd.open_subset_closure_inter (t := Ioo (-1 : ℝ) 1) isOpen_Ioo
    change Ioo (-1 : ℝ) 1 ⊆ closure T at hsub
    rw [hfin.isClosed.closure_eq] at hsub
    exact (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).not_finite (hfin.subset hsub)
  obtain ⟨d, hd⟩ := H.dense_or_cyclic.resolve_left hd
  exact ⟨d, hd.trans (AddSubgroup.zmultiples_eq_closure d).symm⟩

private theorem reflect_in_fibre (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {ψ φ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (hφ : φ ∈ Ψ) (hlin : φ.linear = ψ.linear) :
    (2 : ℝ) • ψ - φ ∈ Ψ ∧ ((2 : ℝ) • ψ - φ).linear = ψ.linear := by
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
  have h := hΨ.neg_mem (hv.2 φ hφ)
  rw [hlin, hv.1, neg_sub] at h
  refine ⟨h, ?_⟩
  rw [AffineMap.sub_linear, AffineMap.smul_linear, hlin, two_smul, add_sub_cancel_right]

private theorem shift_double_sub_mem (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {ψ η φ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (hη : η ∈ Ψ) (hφ : φ ∈ Ψ)
    (hηlin : η.linear = ψ.linear) (hφlin : φ.linear = ψ.linear) (o : A) :
    shift φ (2 * (η o - ψ o)) ∈ Ψ := by
  obtain ⟨h, hlin⟩ := reflect_in_fibre hΨ hψ hφ hφlin
  have hr := (reflect_in_fibre hΨ hη h (hlin.trans hηlin.symm)).1
  convert hr using 1
  ext x
  have hconst := apply_eq_apply_of_linear_eq_zero (f := η - ψ)
      (by rw [AffineMap.sub_linear, hηlin, sub_self]) x o
  change η x - ψ x = η o - ψ o at hconst
  change φ x + 2 * (η o - ψ o) = 2 * η x - (2 * ψ x - φ x)
  linarith

/-- In a derivative fibre, the difference of any two roots is a rational constant, provided
`Ψ` has a positive rational period. -/
theorem IsAffineRootSystemWithRankZero.sub_apply_mem_range_rat_of_linear_eq
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {r : ℝ} (hr : r ∈ rationalRootPeriods Ψ)
    {ψ η : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) (hη : η ∈ Ψ) (hlin : η.linear = ψ.linear) (o : A) :
    η o - ψ o ∈ Set.range ((↑) : ℚ → ℝ) := by
  let H := fibreShiftGroup Ψ ψ.linear
  have hrH : r ∈ H := by
    intro φ hφ _
    refine ⟨hr.2.2 _ hφ, ?_⟩
    simpa only [shift, Int.cast_neg, Int.cast_one, neg_one_mul] using
      hΨ.add_intCast_mul_mem hr.2.2 hφ (-1)
  have hsH : 2 * (η o - ψ o) ∈ H := by
    intro φ hφ hφlin
    refine ⟨shift_double_sub_mem hΨ hψ hη hφ hlin hφlin o, ?_⟩
    convert shift_double_sub_mem hΨ hη hψ hφ hlin.symm (hφlin.trans hlin.symm) o using 2
    ring
  obtain ⟨d, hH⟩ := exists_zmultiples_fibreShiftGroup hΨ hψ
  change H = AddSubgroup.zmultiples d at hH
  rw [hH] at hrH hsH
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hrH
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hsH
  simp only [zsmul_eq_mul] at hm hn
  obtain ⟨q, hq⟩ := hr.2.1
  have hm0 : (m : ℝ) ≠ 0 := by
    intro hm0
    rw [hm0, zero_mul] at hm
    exact hr.1.ne' hm.symm
  refine ⟨(n : ℚ) * q / (2 * (m : ℚ)), ?_⟩
  push_cast
  rw [hq, div_eq_iff (mul_ne_zero two_ne_zero hm0)]
  calc
    (n : ℝ) * r = (m : ℝ) * (2 * (η o - ψ o)) := by rw [← hm, ← hn]; ring
    _ = (η o - ψ o) * (2 * (m : ℝ)) := by ring

/-- A special point is rational when the roots have a positive rational period. -/
theorem IsAffineRootSystemWithRankZero.isRationalPoint_of_isSpecialPoint
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {r : ℝ} (hr : r ∈ rationalRootPeriods Ψ)
    {o : A} (ho : IsSpecialPoint Ψ o) : IsRationalPoint Ψ o := by
  intro ψ hψ
  obtain ⟨η, hη, hker⟩ := (isSpecialPoint_iff_ker hΨ.linear_ne_zero o).1 ho ψ hψ
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot η hη.1
  let χ := -(ψ - ψ.linear v • η)
  have hχ : χ ∈ Ψ := hΨ.neg_mem (hv.2 ψ hψ)
  have hχlin : χ.linear = ψ.linear := by
    ext w
    have hw : w - (η.linear w / 2) • v ∈ LinearMap.ker η.linear := by
      simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hv.1]
      ring
    rw [← hker] at hw
    have h := LinearMap.mem_ker.mp hw
    simp only [map_sub, map_smul, smul_eq_mul] at h
    change -(ψ.linear w - ψ.linear v * η.linear w) = ψ.linear w
    linarith
  have hχo : χ o = -ψ o := by
    change -(ψ o - ψ.linear v * η o) = -ψ o
    rw [hη.2, mul_zero, sub_zero]
  obtain ⟨q, hq⟩ := hΨ.sub_apply_mem_range_rat_of_linear_eq hr hχ hψ hχlin.symm o
  rw [hχo] at hq
  refine ⟨q / 2, ?_⟩
  push_cast
  linarith

/-- An affine frame with rational origin and integral derivative coordinates for all roots. -/
structure RationalRootFrame (Ψ : Set (A →ᵃ[ℝ] ℝ)) where
  origin : A
  basis : Basis (Fin (finrank ℝ V)) ℝ V
  origin_rational : IsRationalPoint Ψ origin
  integral_derivative : ∀ (ψ : Ψ) i, ψ.val.linear (basis i) ∈ Set.range ((↑) : ℤ → ℝ)

/-- Construct a rational root frame from a special point and a basis chosen from the coroots. -/
def IsAffineRootSystemWithRankZero.rationalRootFrame (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {r : ℝ} (hr : r ∈ rationalRootPeriods Ψ) : RationalRootFrame Ψ := by
  classical
  letI := hΨ.finite_derivativeRoots.fintype
  let T := Set.range hΨ.derivativePairing.coroot
  have hT : Submodule.span ℝ T = ⊤ := RootPairing.IsRootSystem.span_coroot_eq_top
  letI : Module.Finite ℝ V := Module.Finite.of_fg_top
    (hT ▸ Submodule.fg_span (Set.finite_range hΨ.derivativePairing.coroot))
  let J := (linearIndepOn_empty ℝ (@id V)).extend (Set.empty_subset T)
  let b : Basis J ℝ V := Basis.ofSpan hT.ge
  letI : Finite J := Module.Finite.finite_basis b
  letI : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let o := hΨ.exists_isSpecialPoint.choose
  refine ⟨o, b.reindex e, hΨ.isRationalPoint_of_isSpecialPoint hr
    hΨ.exists_isSpecialPoint.choose_spec, ?_⟩
  intro ψ i
  rw [Basis.reindex_apply]
  obtain ⟨a, ha⟩ := Basis.ofSpan_subset hT.ge (Set.mem_range_self (e.symm i))
  rw [← ha, hΨ.derivativePairing_coroot]
  obtain ⟨m, hm⟩ := hΨ.coroot_integral _ ψ.property _ (hΨ.derivativeRootLift_mem a) _
    (hΨ.isCoroot_derivativeCoroot a)
  exact ⟨m, hm.symm⟩

namespace RationalRootFrame

variable (R : RationalRootFrame Ψ)

/-- From real coordinate vectors to points of the apartment. -/
def fromCoordinates : (Fin (finrank ℝ V) → ℝ) ≃ᵃ[ℝ] A :=
  R.basis.equivFun.symm.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ R.origin)

/-- The rational constant term of a root in this frame. -/
def rootConstant (ψ : Ψ) : ℚ := (R.origin_rational ψ.val ψ.property).choose

/-- The integral coefficients, viewed as rational, of a root in this frame. -/
def rootCoefficient (ψ : Ψ) (i : Fin (finrank ℝ V)) : ℚ :=
  (R.integral_derivative ψ i).choose

@[simp] theorem cast_rootConstant (ψ : Ψ) : (R.rootConstant ψ : ℝ) = ψ.val R.origin :=
  (R.origin_rational ψ.val ψ.property).choose_spec

@[simp] theorem cast_rootCoefficient (ψ : Ψ) (i : Fin (finrank ℝ V)) :
    (R.rootCoefficient ψ i : ℝ) = ψ.val.linear (R.basis i) := by
  simpa only [rootCoefficient, Rat.cast_intCast] using (R.integral_derivative ψ i).choose_spec

/-- Each root is an affine functional with rational coefficients in these coordinates. -/
theorem apply_fromCoordinates (ψ : Ψ) (x : Fin (finrank ℝ V) → ℝ) :
    ψ.val (R.fromCoordinates x) = (R.rootConstant ψ : ℝ) +
      ∑ i, (R.rootCoefficient ψ i : ℝ) * x i := by
  change ψ.val (R.basis.equivFun.symm x +ᵥ R.origin) = _
  rw [AffineMap.map_vadd, vadd_eq_add, Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, cast_rootCoefficient, cast_rootConstant]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Points with rational coordinates are rational in the sense of KP Definition 13.4.1. -/
theorem isRationalPoint_fromCoordinates (x : Fin (finrank ℝ V) → ℚ) :
    IsRationalPoint Ψ (R.fromCoordinates (fun i => (x i : ℝ))) := by
  intro ψ hψ
  let a : Ψ := ⟨ψ, hψ⟩
  refine ⟨R.rootConstant a + ∑ i, R.rootCoefficient a i * x i, ?_⟩
  push_cast
  exact (R.apply_fromCoordinates a _).symm

end RationalRootFrame

end Langlands.Geometry.Building.AffineRootSystem

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Rational affine-root coordinates for the supplied valuation apartment. -/
def rationalRootFrame (B : ValuationBuildingData G) : AffineRootSystem.RationalRootFrame B.affineRoots :=
  B.isAffineRootSystemWithRankZero_affineRoots.rationalRootFrame B.two_mem_rationalRootPeriods_affineRoots

end Langlands.Geometry.Building.ValuationBuildingData
