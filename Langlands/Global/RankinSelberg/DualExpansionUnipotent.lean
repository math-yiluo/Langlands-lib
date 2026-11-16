import Langlands.Global.RankinSelberg.DualExpansionData
import Langlands.Global.RankinSelberg.DualExpansionLattice
import Langlands.Global.RankinSelberg.ProjectionPeriod

/-! # The last-column decomposition `N_(K+1) = 𝔸^K ⋊ N_K` -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (sqZeroUnit sqZeroUnit_val ratVec ratVec_apply)

variable (F : Type u) [Field F] [NumberField F]

local instance dualUnipSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualUnipSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Rational

variable {F}

/-- A point of `N_n(𝔸)` is rational exactly when it is the image of a rational matrix. -/
theorem mem_rationalSubgroup_unipotent_iff {n : ℕ} (h : unipotentAdelic F n) :
    h ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) ↔
      ∃ M : RationalGL F n, (h : Points F n) =
        (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.rational F n M) := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨GeneralLinearGroupPoints.rationalEquiv F n q.val, ?_⟩
    apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
    rw [MulEquiv.apply_symm_apply]
    exact GeneralLinearGroupPoints.adelicEquiv_rational F n q.val
  · rintro ⟨M, hM⟩
    have hrat : (h : Points F n) ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
      refine ⟨(GeneralLinearGroupPoints.rationalEquiv F n).symm M, ?_⟩
      apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
      rw [hM, MulEquiv.apply_symm_apply, GeneralLinearGroupPoints.adelicEquiv_rational,
        MulEquiv.apply_symm_apply]
    have himg := (mem_unipotentRationalImage_iff_mem_inf F n _).mpr ⟨hrat, h.property⟩
    obtain ⟨l, hl⟩ := (mem_unipotentRationalImage_iff F n _).mp himg
    have : (l : unipotentAdelic F n) = h := Subtype.ext hl
    rw [← this]
    exact l.property

end Rational

section Homs

variable {F} {K : ℕ}

theorem lastColMat_add {R : Type*} [CommRing R] (c d : Fin K → R) :
    lastColMat (c + d) = lastColMat c + lastColMat d := by
  ext a b
  simp only [lastColMat, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem lastColMat_zero {R : Type*} [CommRing R] : lastColMat (0 : Fin K → R) = 0 := by
  ext a b
  simp only [lastColMat, Pi.zero_apply, Matrix.zero_apply]
  split_ifs <;> rfl

theorem pointMatrix_one {n : ℕ} : pointMatrix F (1 : Points F n) = 1 := by
  simp [pointMatrix]

theorem lastColPoint_add (c d : Fin K → Adeles F) :
    lastColPoint F (c + d) = lastColPoint F c * lastColPoint F d := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_lastColPoint, pointMatrix_lastColPoint, pointMatrix_lastColPoint,
    add_mul, one_mul, mul_add, mul_one, lastColMat_mul, add_zero, lastColMat_add]
  abel

theorem lastColPoint_zero : lastColPoint F (0 : Fin K → Adeles F) = 1 := by
  apply point_ext
  rw [pointMatrix_lastColPoint, lastColMat_zero, add_zero, pointMatrix_one]

variable (F K) in
/-- The last-column homomorphism `𝔸^K → N_(K+1)(𝔸)`. -/
def colHom : ColGroup F (Fin K) →* unipotentAdelic F (K + 1) where
  toFun c := ⟨lastColPoint F (Multiplicative.toAdd c), lastColPoint_mem_unipotentAdelic _⟩
  map_one' := Subtype.ext lastColPoint_zero
  map_mul' c d := Subtype.ext (by
    change lastColPoint F (Multiplicative.toAdd (c * d)) = _
    rw [toAdd_mul, lastColPoint_add]
    rfl)

theorem coe_colHom (c : ColGroup F (Fin K)) :
    ((colHom F K c : unipotentAdelic F (K + 1)) : Points F (K + 1)) =
      lastColPoint F (Multiplicative.toAdd c) := rfl

variable (F K) in
/-- The padding homomorphism `N_K(𝔸) → N_(K+1)(𝔸)`. -/
def padHom : unipotentAdelic F K →* unipotentAdelic F (K + 1) where
  toFun := padUnipotent F (Nat.le_succ K)
  map_one' := Subtype.ext (by
    apply point_ext
    simp only [padUnipotent, pointMatrix, adelicEquiv_pad, OneMemClass.coe_one, map_one,
      Units.val_one])
  map_mul' u v := Subtype.ext (pad_mul F _ _ _)

theorem coe_padHom (u : unipotentAdelic F K) :
    ((padHom F K u : unipotentAdelic F (K + 1)) : Points F (K + 1)) =
      pad F (Nat.le_succ K) (u : Points F K) := rfl

/-- The top-left `K × K` block. -/
def topLeftMat {R : Type*} (A : Matrix (Fin (K + 1)) (Fin (K + 1)) R) : Matrix (Fin K) (Fin K) R :=
  A.submatrix Fin.castSucc Fin.castSucc

theorem isUnitriangular_topLeftMat {R : Type*} [CommRing R]
    {A : Matrix (Fin (K + 1)) (Fin (K + 1)) R} (hA : PrimitiveAdelicHeight.IsUnitriangular A) :
    PrimitiveAdelicHeight.IsUnitriangular (topLeftMat A) :=
  ⟨fun _ _ hij => hA.1 (Fin.castSucc_lt_castSucc_iff.mpr hij), fun _ => hA.2 _⟩

theorem topLeftMat_mul {R : Type*} [CommRing R] (A B : Matrix (Fin (K + 1)) (Fin (K + 1)) R)
    (hB : B.IsUpperTriangular) : topLeftMat (A * B) = topLeftMat A * topLeftMat B := by
  ext i j
  simp only [topLeftMat, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc]
  have h0 : B (Fin.last K) j.castSucc = 0 := hB (Fin.castSucc_lt_last j)
  simp only [h0, mul_zero, add_zero]

/-- The top-left block of a point of `N_(K+1)(𝔸)`. -/
def topLeftPoint (h : unipotentAdelic F (K + 1)) : unipotentAdelic F K :=
  ⟨(GeneralLinearGroupPoints.adelicEquiv F K).symm
      (unitriangularUnit (topLeftMat (pointMatrix F (h : Points F (K + 1))))
        (isUnitriangular_topLeftMat (isUnitriangular_of_mem_unipotentAdelic F h))), by
    rw [mem_unipotentAdelic_iff, MulEquiv.apply_symm_apply]
    exact isUnitriangular_topLeftMat (isUnitriangular_of_mem_unipotentAdelic F h)⟩

theorem pointMatrix_topLeftPoint (h : unipotentAdelic F (K + 1)) :
    pointMatrix F ((topLeftPoint h : unipotentAdelic F K) : Points F K) =
      topLeftMat (pointMatrix F (h : Points F (K + 1))) := by
  simp only [topLeftPoint, pointMatrix, MulEquiv.apply_symm_apply]
  rfl

variable (F K) in
/-- The top-left block homomorphism `N_(K+1)(𝔸) → N_K(𝔸)`. -/
def topLeftHom : unipotentAdelic F (K + 1) →* unipotentAdelic F K where
  toFun := topLeftPoint
  map_one' := Subtype.ext (by
    apply point_ext
    rw [pointMatrix_topLeftPoint]
    simp only [OneMemClass.coe_one, pointMatrix_one]
    ext i j
    simp [topLeftMat, Matrix.one_apply, Fin.castSucc_inj])
  map_mul' g h := Subtype.ext (by
    apply point_ext
    rw [pointMatrix_topLeftPoint, Subgroup.coe_mul, pointMatrix_mul, topLeftMat_mul _ _
      (isUnitriangular_of_mem_unipotentAdelic F h).1, Subgroup.coe_mul, pointMatrix_mul,
      pointMatrix_topLeftPoint, pointMatrix_topLeftPoint])

theorem topLeftHom_padHom (u : unipotentAdelic F K) : topLeftHom F K (padHom F K u) = u := by
  apply Subtype.ext
  apply point_ext
  change pointMatrix F ((topLeftPoint (padHom F K u) : unipotentAdelic F K) : Points F K) = _
  rw [pointMatrix_topLeftPoint, coe_padHom]
  ext i j
  simp only [topLeftMat, Matrix.submatrix_apply, pointMatrix, adelicEquiv_pad, padGL_apply,
    Fin.val_castSucc, Fin.is_lt, dite_true, Fin.eta]

theorem topLeftHom_colHom (c : ColGroup F (Fin K)) : topLeftHom F K (colHom F K c) = 1 := by
  apply Subtype.ext
  apply point_ext
  change pointMatrix F ((topLeftPoint (colHom F K c) : unipotentAdelic F K) : Points F K) = _
  rw [pointMatrix_topLeftPoint, coe_colHom, pointMatrix_lastColPoint, OneMemClass.coe_one,
    pointMatrix_one]
  ext i j
  simp only [topLeftMat, Matrix.submatrix_apply, Matrix.add_apply, lastColMat, Fin.val_castSucc,
    Matrix.one_apply, Fin.castSucc_inj]
  rw [dite_eq_right (fun h => by have := j.isLt; omega), add_zero]

theorem exists_colHom_eq (h : unipotentAdelic F (K + 1)) (hh : topLeftHom F K h = 1) :
    ∃ c, colHom F K c = h := by
  refine ⟨Multiplicative.ofAdd fun i => pointMatrix F (h : Points F (K + 1)) i.castSucc
    (Fin.last K), ?_⟩
  have htl : topLeftMat (pointMatrix F (h : Points F (K + 1))) = 1 := by
    have := congrArg (fun x : unipotentAdelic F K => pointMatrix F (x : Points F K)) hh
    change pointMatrix F ((topLeftPoint h : unipotentAdelic F K) : Points F K) = _ at this
    rw [pointMatrix_topLeftPoint, OneMemClass.coe_one, pointMatrix_one] at this
    exact this
  have hu := isUnitriangular_of_mem_unipotentAdelic F h
  apply Subtype.ext
  apply point_ext
  rw [coe_colHom, pointMatrix_lastColPoint]
  ext a b
  refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [Matrix.add_apply, lastColMat, Fin.val_last, lt_irrefl, false_and, dite_false,
      add_zero, Matrix.one_apply_eq]
    exact (hu.2 _).symm
  · simp only [Matrix.add_apply, lastColMat, Fin.val_last, Fin.val_castSucc, lt_irrefl,
      false_and, dite_false, add_zero]
    rw [Matrix.one_apply_ne (fun h' => by
      have := congrArg Fin.val h'; simp at this; omega)]
    exact (hu.1 (Fin.castSucc_lt_last b')).symm
  · simp only [Matrix.add_apply, lastColMat, Fin.val_last, Fin.val_castSucc, Fin.is_lt, true_and,
      dite_true, toAdd_ofAdd]
    rw [Matrix.one_apply_ne (fun h' => by
      have := congrArg Fin.val h'; simp at this; omega), zero_add]
  · have := congrFun (congrFun htl a') b'
    simp only [topLeftMat, Matrix.submatrix_apply] at this
    simp only [Matrix.add_apply, lastColMat, Fin.val_castSucc]
    rw [dite_eq_right (fun h' => by have := b'.isLt; omega), add_zero, this]
    simp [Matrix.one_apply, Fin.castSucc_inj]

end Homs

section Topology

variable {F} {K : ℕ}

local instance dualUnipLocallyCompact (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

theorem continuous_pointMatrix {n : ℕ} : Continuous (pointMatrix F (n := n)) :=
  Units.continuous_val.comp (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous

theorem continuous_padHom : Continuous (padHom F K) :=
  continuous_induced_rng.mpr ((continuous_pad F _).comp continuous_subtype_val)

theorem continuous_topLeftHom : Continuous (topLeftHom F K) := by
  refine continuous_induced_rng.mpr ?_
  have hM : Continuous fun h : unipotentAdelic F (K + 1) =>
      topLeftMat (pointMatrix F (h : Points F (K + 1))) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_pointMatrix (F := F)).comp continuous_subtype_val).matrix_elem _ _
  have hU : Continuous fun h : unipotentAdelic F (K + 1) =>
      unitriangularUnit (topLeftMat (pointMatrix F (h : Points F (K + 1))))
        (isUnitriangular_topLeftMat (isUnitriangular_of_mem_unipotentAdelic F h)) :=
    Units.continuous_iff.mpr ⟨hM, hM.matrix_adjugate⟩
  exact (GeneralLinearGroupPoints.adelicHomeomorph F K).symm.continuous.comp hU

/-- The last column of a point of `N_(K+1)(𝔸)`. -/
def lastColOf (h : unipotentAdelic F (K + 1)) : ColGroup F (Fin K) :=
  Multiplicative.ofAdd fun i => pointMatrix F (h : Points F (K + 1)) i.castSucc (Fin.last K)

theorem lastColOf_colHom (c : ColGroup F (Fin K)) : lastColOf (colHom F K c) = c := by
  simp only [lastColOf, coe_colHom, pointMatrix_lastColPoint, Matrix.add_apply, lastColMat,
    Fin.val_castSucc, Fin.val_last, Fin.is_lt, true_and, dite_true, Fin.eta]
  have : ∀ i : Fin K, (1 : Matrix (Fin (K + 1)) (Fin (K + 1)) (Adeles F)) i.castSucc
      (Fin.last K) = 0 := fun i => Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne
  simp only [this, zero_add, ofAdd_toAdd]

theorem isEmbedding_colHom : IsEmbedding (colHom F K) := by
  refine Function.LeftInverse.isEmbedding (f := lastColOf) lastColOf_colHom ?_ ?_
  · exact continuous_ofAdd.comp (continuous_pi fun i =>
      ((continuous_pointMatrix (F := F)).comp continuous_subtype_val).matrix_elem _ _)
  · exact continuous_induced_rng.mpr ((GeneralLinearGroupPoints.adelicHomeomorph F
      (K + 1)).symm.continuous.comp (Units.continuous_iff.mpr ⟨by
        exact continuous_const.add (continuous_pi fun a => continuous_pi fun b => by
          simp only [lastColMat]
          split_ifs
          · exact (continuous_apply _).comp continuous_toAdd
          · exact continuous_const), by
        exact continuous_const.sub (continuous_pi fun a => continuous_pi fun b => by
          simp only [lastColMat]
          split_ifs
          · exact (continuous_apply _).comp continuous_toAdd
          · exact continuous_const)⟩))

end Topology

section Lattices

variable {F} {K : ℕ}

theorem pointMatrix_symm_rational {n : ℕ} (M : RationalGL F n) :
    pointMatrix F ((GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.rational F n M)) =
      (M : Matrix (Fin n) (Fin n) F).map (algebraMap F (Adeles F)) := by
  simp only [pointMatrix, MulEquiv.apply_symm_apply]
  ext i j
  rfl

theorem padHom_mem_rational {u : unipotentAdelic F K}
    (hu : u ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K)) :
    padHom F K u ∈
      AdelicSubgroupPoints.rationalSubgroup F (Scheme F (K + 1)) (upperUnipotent F (K + 1)) := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff u).mp hu
  refine (mem_rationalSubgroup_unipotent_iff _).mpr ⟨padGL (Nat.le_succ K) M, ?_⟩
  rw [coe_padHom, hM]
  unfold pad
  rw [MulEquiv.apply_symm_apply, padGL_rational]

theorem topLeftHom_mem_rational {h : unipotentAdelic F (K + 1)}
    (hh : h ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (K + 1))
      (upperUnipotent F (K + 1))) :
    topLeftHom F K h ∈
      AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K) := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff h).mp hh
  have hmat : pointMatrix F (h : Points F (K + 1)) =
      (M : Matrix (Fin (K + 1)) (Fin (K + 1)) F).map (algebraMap F (Adeles F)) := by
    rw [hM, pointMatrix_symm_rational]
  have hMu : PrimitiveAdelicHeight.IsUnitriangular (M : Matrix (Fin (K + 1)) (Fin (K + 1)) F) := by
    rw [← isUnitriangular_map_iff, ← hmat]
    exact isUnitriangular_of_mem_unipotentAdelic F h
  refine (mem_rationalSubgroup_unipotent_iff _).mpr
    ⟨unitriangularUnit (topLeftMat (M : Matrix (Fin (K + 1)) (Fin (K + 1)) F))
      (isUnitriangular_topLeftMat hMu), ?_⟩
  apply point_ext
  change pointMatrix F ((topLeftPoint h : unipotentAdelic F K) : Points F K) = _
  rw [pointMatrix_topLeftPoint, pointMatrix_symm_rational, hmat]
  ext i j
  rfl

theorem colHom_mem_rational_iff (c : ColGroup F (Fin K)) :
    colHom F K c ∈
        AdelicSubgroupPoints.rationalSubgroup F (Scheme F (K + 1)) (upperUnipotent F (K + 1)) ↔
      c ∈ ratLattice F (Fin K) := by
  constructor
  · intro hc
    obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff _).mp hc
    have hmat := congrArg (pointMatrix F) hM
    rw [coe_colHom, pointMatrix_lastColPoint, pointMatrix_symm_rational] at hmat
    refine ⟨fun i => (M : Matrix (Fin (K + 1)) (Fin (K + 1)) F) i.castSucc (Fin.last K), ?_⟩
    funext i
    have := congrFun (congrFun hmat i.castSucc) (Fin.last K)
    simp only [Matrix.add_apply, lastColMat, Fin.val_castSucc, Fin.val_last, Fin.is_lt, true_and,
      dite_true, Fin.eta, Matrix.map_apply] at this
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, zero_add] at this
    rw [ratVec_apply, ← this]
  · rintro ⟨k, hk⟩
    refine (mem_rationalSubgroup_unipotent_iff _).mpr
      ⟨sqZeroUnit (lastColMat k) (lastColMat_mul k k), ?_⟩
    apply point_ext
    rw [coe_colHom, pointMatrix_lastColPoint, pointMatrix_symm_rational, hk]
    ext a b
    simp only [Matrix.add_apply, Matrix.map_apply, sqZeroUnit_val, lastColMat, ratVec_apply,
      map_add, Matrix.one_apply]
    split_ifs <;> simp

end Lattices

section Period

variable [CompactSpace (AdeleQuotient F)]

local instance dualUnipPeriodLocallyCompact (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- The normalized period over `N_K(F) \ N_K(𝔸)`. -/
def unipotentPeriod (K : ℕ) (f : unipotentAdelic F K → ℂ) : ℂ :=
  ((Measure.haar : Measure (unipotentAdelic F K)) (unipotentFundamentalDomain F K)).toReal⁻¹ •
    ∫ u in unipotentFundamentalDomain F K, f u ∂Measure.haar

variable {F} {K : ℕ}

/-- **Last-column decomposition of unipotent periods**: the period over `N_(K+1)(F) \ N_(K+1)(𝔸)`
is the period over `N_K` of the torus integral over the last column. -/
theorem unipotentPeriod_succ (φ : unipotentAdelic F (K + 1) → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ g ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F (K + 1))
      (upperUnipotent F (K + 1)), ∀ h, φ (g * h) = φ h) :
    unipotentPeriod F (K + 1) φ = unipotentPeriod F K (fun u =>
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K)
      (fun c => φ (colHom F K (Multiplicative.ofAdd c) * padHom F K u))) := by
  have hcpt1 := compactSpace_unipotentRationalQuotient F (K + 1)
  have hcpt0 := compactSpace_unipotentRationalQuotient F K
  have h := LeftCosetSpace.Semidirect.normalizedPeriod_eq_iterated_of_compact (colHom F K)
    (padHom F K) (topLeftHom F K) topLeftHom_padHom exists_colHom_eq topLeftHom_colHom
    isEmbedding_colHom continuous_padHom continuous_topLeftHom
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F (K + 1)) (upperUnipotent F (K + 1)))
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F _ _)
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K))
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F _ _)
    (fun m hm => padHom_mem_rational hm) (fun h hh => topLeftHom_mem_rational hh)
    (ratLattice F (Fin K)) (isDiscrete_ratLattice F (Fin K)) colHom_mem_rational_iff φ hφ hφΓ
  refine h.trans ?_
  unfold unipotentPeriod
  congr 1
  refine setIntegral_congr_fun (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
    fun u _ => ?_
  refine normalizedPeriod_ratLattice F (Fin K) _
    (hφ.comp (isEmbedding_colHom.continuous.mul continuous_const)) ?_
  intro p hp x
  simp only [map_mul, mul_assoc]
  exact hφΓ _ ((colHom_mem_rational_iff p).mpr hp) _

end Period

section PeriodAnalysis

open scoped Langlands.Automorphic.CuspidalWhittaker

variable [CompactSpace (AdeleQuotient F)] {F} {K : ℕ}

local instance dualUnipAnalysisLocallyCompact (n : ℕ) : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

omit [CompactSpace (AdeleQuotient F)] in
theorem haar_unipotentFundamentalDomain_lt_top :
    (Measure.haar : Measure (unipotentAdelic F K)) (unipotentFundamentalDomain F K) < ⊤ := by
  have := compactSpace_unipotentRationalQuotient F K
  rw [haar_unipotentFundamentalDomain]
  exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero _ _ _))

instance isFiniteMeasure_restrict_unipotentFundamentalDomain :
    IsFiniteMeasure ((Measure.haar : Measure (unipotentAdelic F K)).restrict
      (unipotentFundamentalDomain F K)) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact haar_unipotentFundamentalDomain_lt_top⟩

/-- **Fubini for unipotent periods and torus integrals**. -/
theorem unipotentPeriod_torusIntegral_comm {T : Type} [Fintype T]
    (f : unipotentAdelic F K → (T → Adeles F) → ℂ) (hf : Continuous (Function.uncurry f))
    (hp : ∀ u, Langlands.Automorphic.CuspidalWhittaker.IsPeriodic (f u)) {B : ℝ}
    (hB : ∀ u y, ‖f u y‖ ≤ B) :
    unipotentPeriod F K (fun u => Langlands.Automorphic.CuspidalWhittaker.torusIntegral T (f u)) =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral T
        (fun y => unipotentPeriod F K (fun u => f u y)) := by
  unfold unipotentPeriod Langlands.Automorphic.CuspidalWhittaker.torusIntegral
  rw [integral_smul]
  congr 1
  have hq : IsOpenQuotientMap (Prod.map (id : unipotentAdelic F K → unipotentAdelic F K)
      (Langlands.Automorphic.CuspidalWhittaker.torusMk : (T → Adeles F) → T → AdeleQuotient F)) :=
    IsOpenQuotientMap.id.prodMap Langlands.Automorphic.CuspidalWhittaker.isOpenQuotientMap_torusMk
  have hg : Continuous (Function.uncurry fun (u : unipotentAdelic F K)
      (t : T → AdeleQuotient F) =>
        f u (Langlands.Automorphic.CuspidalWhittaker.torusLift t)) := by
    rw [hq.isQuotientMap.continuous_iff]
    convert hf using 1
    funext p
    exact (hp p.1).lift_mk p.2
  refine integral_integral_swap ?_
  refine Integrable.of_bound hg.aestronglyMeasurable B (Filter.Eventually.of_forall fun p => ?_)
  exact hB _ _

omit [CompactSpace (AdeleQuotient F)] in
/-- **Exchanging unipotent periods with bounded sums**. -/
theorem unipotentPeriod_tsum {Q : Type*} [Countable Q] (f : Q → unipotentAdelic F K → ℂ)
    (hc : ∀ q, Continuous (f q)) (hs : ∀ u, Summable fun q => ‖f q u‖) {B : ℝ}
    (hB : ∀ u, ∑' q, ‖f q u‖ ≤ B) :
    unipotentPeriod F K (fun u => ∑' q, f q u) = ∑' q, unipotentPeriod F K (f q) := by
  unfold unipotentPeriod
  have hfin : ∑' q, ∫⁻ u in unipotentFundamentalDomain F K, ‖f q u‖ₑ ∂Measure.haar ≠ ⊤ := by
    rw [← lintegral_tsum (fun q => (hc q).enorm.aemeasurable)]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in unipotentFundamentalDomain F K, ENNReal.ofReal B
      ∂Measure.haar) ?_ (lintegral_mono fun u => ?_)
    · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top haar_unipotentFundamentalDomain_lt_top.ne
    · simp only [← ofReal_norm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg _) (hs _)]
      exact ENNReal.ofReal_le_ofReal (hB _)
  rw [integral_tsum (fun q => (hc q).aestronglyMeasurable) hfin]
  simp only [Complex.real_smul]
  rw [tsum_mul_left]

end PeriodAnalysis

end Langlands.Global.RankinSelbergGlobal.Unfolding
