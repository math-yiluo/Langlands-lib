import Langlands.Global.RankinSelberg.DualExpansionUnipotent
import Langlands.Global.RankinSelberg.DualExpansionCosets

/-! # Rational rectangular points and the rectangle periods -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (sqZeroUnit sqZeroUnit_val)

variable (F : Type u) [Field F] [NumberField F]

local instance dualRectSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualRectSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {F} {m K : ℕ}

section RationalPoints

theorem topLeftMat_xcMat_mul {R : Type*} [CommRing R] (x x' : Fin K × Fin m → R) :
    topLeftMat (xcMat m K x 0) * topLeftMat (xcMat m K x' 0) = 0 := by
  refine mul_eq_zero_of_support _ _ (fun l : Fin (m + K) => (l : ℕ) < m)
    (fun l : Fin (m + K) => m ≤ (l : ℕ)) (fun a l h => ?_) (fun l b h => ?_)
    (fun l h1 h2 => by omega)
  · have := xcMat_support_left x 0 _ _ h
    simp only [Fin.val_castSucc] at this
    omega
  · exact (xcMat_support_right x' 0 _ _ h).1

/-- The rational corner element `1 + topLeft(xcMat ρ 0)` of `GL_(m+K)(F)`. -/
def xcRat (ρ : Fin K × Fin m → F) : RationalGL F (m + K) :=
  sqZeroUnit (topLeftMat (xcMat m K ρ 0)) (topLeftMat_xcMat_mul ρ ρ)

/-- A rational rectangle point is a padded rational corner element. -/
theorem xcPoint_rat_eq_padRational (ρ : Fin K × Fin m → F) :
    xcPoint F (fun p => algebraMap F (Adeles F) (ρ p)) 0 =
      padRational F (Nat.le_succ (m + K)) (xcRat ρ) := by
  apply point_ext
  rw [pointMatrix_xcPoint, pointMatrix_padRational, padGL_rational]
  ext a b
  simp only [Matrix.add_apply, xcMat, Pi.zero_apply, AdelicGL.rational_apply, padGL_apply,
    xcRat, sqZeroUnit_val, topLeftMat, Matrix.submatrix_apply, Fin.val_castSucc,
    Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/-- The column vector `c` on the rows `m, …, m+K-1`, extended by zeros. -/
def extC {R : Type*} [Zero R] (c : Fin K → R) : Fin (m + K) → R := fun a =>
  if h : m ≤ (a : ℕ) then c ⟨(a : ℕ) - m, by omega⟩ else 0

/-- A pure column point is a last-column point. -/
theorem xcPoint_zero_eq_lastColPoint (c : Fin K → Adeles F) :
    xcPoint F (m := m) 0 c = lastColPoint F (extC c) := by
  apply point_ext
  rw [pointMatrix_xcPoint, pointMatrix_lastColPoint]
  ext a b
  simp only [Matrix.add_apply, xcMat, lastColMat, extC, Pi.zero_apply]
  split_ifs <;> first | (exfalso; omega) | rfl

theorem lrGL_rational (M : RationalGL F K) :
    lrGL m K (AdelicGL.rational F K M) = AdelicGL.rational F (m + K) (lrGL m K M) := by
  apply Units.ext
  ext a b
  change lrMatrix m K _ a b = _
  rw [AdelicGL.rational_apply]
  change _ = algebraMap F (Adeles F) (lrMatrix m K (M : Matrix (Fin K) (Fin K) F) a b)
  rw [lrMatrix_apply, lrMatrix_apply]
  split_ifs <;> simp [AdelicGL.rational_apply]

/-- The middle-block image of a rational point is a padded rational corner element. -/
theorem midPoint_rat_eq_padRational (M : RationalGL F K) :
    midPoint F (m := m) ((GeneralLinearGroupPoints.adelicEquiv F K).symm (AdelicGL.rational F K M)) =
      padRational F (Nat.le_succ (m + K)) (lrGL m K M) := by
  unfold midPoint padRational pad
  simp only [MulEquiv.apply_symm_apply, lrGL_rational, padGL_rational]

end RationalPoints

section Invariance

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {W : Points F (m + K + 1) → ℂ}

theorem extC_rat (σ : Fin K → F) :
    extC (m := m) (fun i => algebraMap F (Adeles F) (σ i)) =
      fun a => algebraMap F (Adeles F) (extC (m := m) σ a) := by
  funext a
  simp only [extC]
  split_ifs <;> simp

theorem xcPoint_rat_split (ρ : Fin K × Fin m → F) (σ : Fin K → F) :
    xcPoint F (fun p => algebraMap F (Adeles F) (ρ p)) (fun i => algebraMap F (Adeles F) (σ i)) =
      lastColPoint F (fun a => algebraMap F (Adeles F) (extC (m := m) σ a)) *
        padRational F (Nat.le_succ (m + K)) (xcRat ρ) := by
  rw [← xcPoint_rat_eq_padRational, ← extC_rat, ← xcPoint_zero_eq_lastColPoint, xcPoint_mul,
    zero_add, add_zero]

include hψF

theorem DualData.cornerSum_xcPoint_rat_mul (hW : DualData F m ψ K W) (ρ : Fin K × Fin m → F)
    (σ : Fin K → F) (g : Points F (m + K + 1)) :
    cornerSum F m K W (xcPoint F (fun p => algebraMap F (Adeles F) (ρ p))
      (fun i => algebraMap F (Adeles F) (σ i)) * g) = cornerSum F m K W g := by
  rw [xcPoint_rat_split, mul_assoc, hW.cornerSum_lastColPoint_mul hψF,
    hW.cornerSum_padRational_mul hψF]

theorem DualData.cornerNormSum_xcPoint_rat_mul (hW : DualData F m ψ K W)
    (ρ : Fin K × Fin m → F) (σ : Fin K → F) (g : Points F (m + K + 1)) :
    cornerNormSum F m K W (xcPoint F (fun p => algebraMap F (Adeles F) (ρ p))
      (fun i => algebraMap F (Adeles F) (σ i)) * g) = cornerNormSum F m K W g := by
  rw [xcPoint_rat_split, mul_assoc, hW.cornerNormSum_lastColPoint_mul hψF,
    hW.cornerNormSum_padRational_mul hψF]

theorem DualData.cornerSum_midPoint_rat_mul (hW : DualData F m ψ K W) {u : unipotentAdelic F K}
    (hu : u ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K))
    (g : Points F (m + K + 1)) :
    cornerSum F m K W (midPoint F (u : Points F K) * g) = cornerSum F m K W g := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff u).mp hu
  rw [hM, midPoint_rat_eq_padRational, hW.cornerSum_padRational_mul hψF]

theorem DualData.cornerNormSum_midPoint_rat_mul (hW : DualData F m ψ K W)
    {u : unipotentAdelic F K}
    (hu : u ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K))
    (g : Points F (m + K + 1)) :
    cornerNormSum F m K W (midPoint F (u : Points F K) * g) = cornerNormSum F m K W g := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff u).mp hu
  rw [hM, midPoint_rat_eq_padRational, hW.cornerNormSum_padRational_mul hψF]

end Invariance

section Definitions

variable (F) (m K) [CompactSpace (AdeleQuotient F)]

/-- The rectangle period
`∫_{(𝔸/F)^{K×m}} ∫_{(𝔸/F)^K} ψ(c_(K-1)) G(x̂ ĉ g) dc dx`. -/
def rectPeriod (ψ : AddChar (Adeles F) ℂ) (G : Points F (m + K + 1) → ℂ)
    (g : Points F (m + K + 1)) : ℂ :=
  Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) fun x =>
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) fun c =>
      ψ (lastEntry c) * G (xcPoint F x c * g)

/-- The period over `V(F) \ V(𝔸)` of the corner sum, `V = (X ⊕ C) ⋊ N_K`. -/
def dualPeriod (ψ : AddChar (Adeles F) ℂ) (W : Points F (m + K + 1) → ℂ)
    (y : Points F (m + K + 1)) : ℂ :=
  unipotentPeriod F K fun u =>
    ψ (superSum F (u : Points F K)) *
      rectPeriod F m K ψ (cornerSum F m K W) (midPoint F (u : Points F K) * y)

end Definitions

section Continuity

theorem continuous_xcMat :
    Continuous fun p : (Fin K × Fin m → Adeles F) × (Fin K → Adeles F) => xcMat m K p.1 p.2 := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [xcMat]
  split_ifs
  · exact (continuous_apply _).comp continuous_fst
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const
  · exact continuous_const

theorem continuous_xcPoint :
    Continuous fun p : (Fin K × Fin m → Adeles F) × (Fin K → Adeles F) => xcPoint F p.1 p.2 := by
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K + 1)).symm.continuous.comp ?_
  exact Units.continuous_iff.mpr ⟨continuous_const.add continuous_xcMat,
    continuous_const.sub continuous_xcMat⟩

theorem continuous_xcPoint_left (c : Fin K → Adeles F) :
    Continuous fun x : Fin K × Fin m → Adeles F => xcPoint F x c := by
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K + 1)).symm.continuous.comp ?_
  have h : Continuous fun x : Fin K × Fin m → Adeles F => xcMat m K x c :=
    continuous_xcMat.comp (continuous_id.prodMk continuous_const)
  exact Units.continuous_iff.mpr ⟨continuous_const.add h, continuous_const.sub h⟩

theorem continuous_xcPoint_right (x : Fin K × Fin m → Adeles F) :
    Continuous fun c : Fin K → Adeles F => xcPoint F x c := by
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K + 1)).symm.continuous.comp ?_
  have h : Continuous fun c : Fin K → Adeles F => xcMat m K x c :=
    continuous_xcMat.comp (continuous_const.prodMk continuous_id)
  exact Units.continuous_iff.mpr ⟨continuous_const.add h, continuous_const.sub h⟩

theorem continuous_lrMatrix :
    Continuous (lrMatrix (R := Adeles F) m K) := by
  change Continuous fun A : Matrix (Fin K) (Fin K) (Adeles F) =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (Adeles F)) 0 0 A)
  exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
    continuous_id).matrix_reindex _ _

theorem continuous_midPoint : Continuous (midPoint F (m := m) (K := K)) := by
  unfold midPoint
  refine (continuous_pad F _).comp ?_
  refine (GeneralLinearGroupPoints.adelicHomeomorph F (m + K)).symm.continuous.comp ?_
  exact (Units.continuous_map (f := (lrMatrix m K : Matrix (Fin K) (Fin K) (Adeles F) →*
    Matrix (Fin (m + K)) (Fin (m + K)) (Adeles F))) continuous_lrMatrix).comp
    (GeneralLinearGroupPoints.adelicHomeomorph F K).continuous

end Continuity

section Bound

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {W : Points F (m + K + 1) → ℂ}
include hψF

omit hψF in
theorem midPoint_inv_conj (v : Points F K) (x : Fin K × Fin m → Adeles F) (c : Fin K → Adeles F) :
    xcPoint F x c * midPoint F v⁻¹ =
      midPoint F v⁻¹ * xcPoint F (rowMulRect F (pointMatrix F v) x)
        (Matrix.mulVec (pointMatrix F v) c) := by
  have h := midPoint_mul_xcPoint F (m := m) v x c
  have h1 : midPoint F (m := m) v⁻¹ * midPoint F v = 1 := by
    rw [← midPoint_mul, inv_mul_cancel, midPoint_one]
  calc xcPoint F x c * midPoint F v⁻¹
      = midPoint F v⁻¹ * (midPoint F v * xcPoint F x c) * midPoint F v⁻¹ := by
        rw [← mul_assoc (midPoint F v⁻¹), h1, one_mul]
    _ = midPoint F v⁻¹ * xcPoint F (rowMulRect F (pointMatrix F v) x)
          (Matrix.mulVec (pointMatrix F v) c) := by
        rw [h, mul_assoc, mul_assoc, ← midPoint_mul, mul_inv_cancel, midPoint_one, mul_one]

/-- The corner sums of norms are bounded on `V(𝔸) y`, where `V = (X ⊕ C) ⋊ N_K`. -/
theorem DualData.exists_bound [CompactSpace (AdeleQuotient F)] (hW : DualData F m ψ K W)
    (y : Points F (m + K + 1)) :
    ∃ C : ℝ, ∀ (x : Fin K × Fin m → Adeles F) (c : Fin K → Adeles F) (u : unipotentAdelic F K),
      cornerNormSum F m K W (xcPoint F x c * midPoint F (u : Points F K) * y) ≤ C := by
  classical
  obtain ⟨Ω, hΩc, hΩu, hred⟩ := PrimitiveAdelicHeight.exists_isCompact_unitriangular_reduction F K
  obtain ⟨D, hDc, hD⟩ := AdelicGroupPoints.exists_isCompact_algebraMap_add_mem F
  let f : Ω → Points F K := fun M => (GeneralLinearGroupPoints.adelicEquiv F K).symm
    (unitriangularUnit (M : Matrix (Fin K) (Fin K) (Adeles F)) (hΩu M M.property))
  have hf : Continuous f := (GeneralLinearGroupPoints.adelicHomeomorph F K).symm.continuous.comp
    (Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩)
  have : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩc
  let S : Set ((Fin K × Fin m → Adeles F) × (Fin K → Adeles F) × Points F K) :=
    (Set.pi Set.univ fun _ => D) ×ˢ (Set.pi Set.univ fun _ => D) ×ˢ Set.range f
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => hDc).prod ((isCompact_univ_pi fun _ => hDc).prod
      (isCompact_range hf))
  have hcont : Continuous fun t : (Fin K × Fin m → Adeles F) × (Fin K → Adeles F) × Points F K =>
      cornerNormSum F m K W (xcPoint F t.1 t.2.1 * midPoint F t.2.2 * y) :=
    hW.continuous_cornerNormSum.comp (((continuous_xcPoint.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
        ((continuous_midPoint).comp (continuous_snd.comp continuous_snd))).mul continuous_const)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x c u => ?_⟩
  -- reduce `u` into the compact set
  obtain ⟨μ₀, hμ₀, hμ₀Ω⟩ := hred _ (isUnitriangular_of_mem_unipotentAdelic F u)
  set M₀ : RationalGL F K := unitriangularUnit μ₀ hμ₀
  have hg₀ : (GeneralLinearGroupPoints.adelicEquiv F K).symm (AdelicGL.rational F K M₀) ∈
      unipotentAdelic F K := by
    rw [mem_unipotentAdelic_iff, MulEquiv.apply_symm_apply]
    exact hμ₀.map _
  set g₀ : unipotentAdelic F K := ⟨_, hg₀⟩
  have hg₀rat : g₀ ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K) :=
    (mem_rationalSubgroup_unipotent_iff g₀).mpr ⟨M₀, rfl⟩
  set k := g₀ * u
  have hk : (k : Points F K) = f ⟨_, hμ₀Ω⟩ := by
    apply point_ext
    simp only [f, pointMatrix, MulEquiv.apply_symm_apply]
    change pointMatrix F ((g₀ : Points F K) * (u : Points F K)) = _
    rw [pointMatrix_mul, show pointMatrix F (g₀ : Points F K) = μ₀.map (algebraMap F (Adeles F))
      from pointMatrix_symm_rational M₀]
    rfl
  have hu : (u : Points F K) = ((g₀⁻¹ : unipotentAdelic F K) : Points F K) * (k : Points F K) := by
    simp [k]
  -- the corner sum is unchanged by the rational part of `u`
  rw [hu, midPoint_mul, ← mul_assoc, Subgroup.coe_inv, midPoint_inv_conj, ← Subgroup.coe_inv,
    mul_assoc, mul_assoc, hW.cornerNormSum_midPoint_rat_mul hψF (inv_mem hg₀rat)]
  set x' := rowMulRect F (pointMatrix F (g₀ : Points F K)) x
  set c' := Matrix.mulVec (pointMatrix F (g₀ : Points F K)) c
  -- reduce the rectangle coordinates into the box
  choose ρ hρ using fun p : Fin K × Fin m => hD (x' p)
  choose σ hσ using fun i : Fin K => hD (c' i)
  rw [← hW.cornerNormSum_xcPoint_rat_mul hψF ρ σ, ← mul_assoc, xcPoint_mul]
  have hmem : ((fun p => algebraMap F (Adeles F) (ρ p)) + x', (fun i => algebraMap F (Adeles F)
      (σ i)) + c', (k : Points F K)) ∈ S :=
    ⟨fun p _ => hρ p, fun i _ => hσ i, ⟨_, hk.symm⟩⟩
  have := hC _ hmem
  simpa [Real.norm_eq_abs, mul_assoc] using le_trans (le_abs_self _) this

end Bound

end Langlands.Global.RankinSelbergGlobal.Unfolding
