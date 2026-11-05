import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiagonalContraction
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.CompactMatrixIntegrality
import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Langlands.GroupScheme.Rational.MatrixEntryBoundedCompactness
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-! # Heights on opposite unipotent points are bounded by a line displacement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Topology
open Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz

section BlockUnipotentInverse

variable {F : Type*} [NormedField F] {n : Type} [Fintype n] [DecidableEq n] {e : n → ℤ}

/-- The entries of `(g - 1) ^ k` vanish at `(i, j)` unless `e i + k ≤ e j`. -/
theorem sub_one_pow_apply_eq_zero {g : GL n F} (hg : g ∈ blockUnipotentSubgroup F (-e)) :
    ∀ (k : ℕ) (i j : n), e j < e i + k → (((g : Matrix n n F) - 1) ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hne : i ≠ j := fun h => by subst h; omega
    simp [Matrix.one_apply_ne hne]
  | succ k ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : e l < e i + k
    · rw [ih i l hl, zero_mul]
    · have hlj : e j ≤ e l := by push_cast at hij; omega
      rw [Matrix.sub_apply, hg l j (by simpa using hlj), sub_self, mul_zero]

/-- `g - 1` is nilpotent of order at most `d + 1` when `d` bounds the weight gaps. -/
theorem sub_one_pow_eq_zero {g : GL n F} (hg : g ∈ blockUnipotentSubgroup F (-e)) {d : ℕ}
    (hd : ∀ i j, e i < e j → e j - e i ≤ d) : ((g : Matrix n n F) - 1) ^ (d + 1) = 0 := by
  ext i j
  refine sub_one_pow_apply_eq_zero hg (d + 1) i j ?_
  rcases lt_or_ge (e i) (e j) with h | h
  · have := hd i j h
    push_cast
    omega
  · push_cast
    omega

/-- The inverse of a block unipotent matrix is the finite geometric series in `1 - g`. -/
theorem coe_inv_eq_sum {g : GL n F} (hg : g ∈ blockUnipotentSubgroup F (-e)) {d : ℕ}
    (hd : ∀ i j, e i < e j → e j - e i ≤ d) :
    ((g⁻¹ : GL n F) : Matrix n n F) =
      ∑ k ∈ Finset.range (d + 1), (-((g : Matrix n n F) - 1)) ^ k := by
  apply Units.inv_eq_of_mul_eq_one_right
  have h := mul_neg_geom_sum (-((g : Matrix n n F) - 1)) (d + 1)
  rw [sub_neg_eq_add, add_sub_cancel, neg_pow, sub_one_pow_eq_zero hg hd, mul_zero,
    sub_zero] at h
  exact h

variable [Nonempty n]

omit [DecidableEq n] in
theorem entryNorm_neg (X : Matrix n n F) : entryNorm (-X) = entryNorm X := by
  simp only [entryNorm, Matrix.neg_apply, norm_neg]

variable [IsUltrametricDist F]

theorem entryNorm_pow_le (X : Matrix n n F) (k : ℕ) :
    entryNorm (X ^ k) ≤ max 1 (entryNorm X) ^ k := by
  induction k with
  | zero => simp [entryNorm_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (entryNorm_mul_le _ _).trans
      (mul_le_mul ih (le_max_right _ _) (entryNorm_nonneg _)
        (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))

/-- The entries of `g` are at most `max 1 (offIdentityNorm g)`. -/
theorem entryNorm_le_max_offIdentityNorm (g : GL n F) :
    entryNorm (g : Matrix n n F) ≤ max 1 (offIdentityNorm g) := by
  refine entryNorm_le fun i j => ?_
  have h : (g : Matrix n n F) i j = ((g : Matrix n n F) - 1) i j + (1 : Matrix n n F) i j := by
    simp
  rw [h, max_comm]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · exact norm_le_entryNorm _ i j
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]

/-- For `g` block unipotent for `-e` with weight gaps at most `d`, the entries of `g⁻¹` are at
most `max 1 (offIdentityNorm g) ^ d`. -/
theorem entryNorm_inv_le {g : GL n F} (hg : g ∈ blockUnipotentSubgroup F (-e)) {d : ℕ}
    (hd : ∀ i j, e i < e j → e j - e i ≤ d) :
    entryNorm ((g⁻¹ : GL n F) : Matrix n n F) ≤ max 1 (offIdentityNorm g) ^ d := by
  rw [coe_inv_eq_sum hg hd]
  refine entryNorm_le fun i j => ?_
  rw [Matrix.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun k hk => ?_
  refine (norm_le_entryNorm _ i j).trans ((entryNorm_pow_le _ k).trans ?_)
  rw [entryNorm_neg]
  exact pow_le_pow_right₀ (le_max_left _ _) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

/-- For `g` block unipotent for `-e` with weight gaps at most `d`,
`glNorm g ≤ max 1 (offIdentityNorm g) ^ (d + 1)`. -/
theorem glNorm_le_max_offIdentityNorm_pow {g : GL n F}
    (hg : g ∈ blockUnipotentSubgroup F (-e)) {d : ℕ}
    (hd : ∀ i j, e i < e j → e j - e i ≤ d) :
    glNorm g ≤ max 1 (offIdentityNorm g) ^ (d + 1) := by
  have h1 : 1 ≤ max 1 (offIdentityNorm g) := le_max_left _ _
  refine max_le ((entryNorm_le_max_offIdentityNorm g).trans ?_)
    ((entryNorm_inv_le hg hd).trans (pow_le_pow_right₀ h1 (by omega)))
  calc max 1 (offIdentityNorm g) = max 1 (offIdentityNorm g) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ h1 (by omega)

omit [DecidableEq n] in
/-- Ultrametric bound for a matrix acting on a vector in the sup norm. -/
theorem norm_mulVec_le (A : Matrix n n F) (y : n → F) : ‖A *ᵥ y‖ ≤ entryNorm A * ‖y‖ := by
  have h0 : 0 ≤ entryNorm A * ‖y‖ := mul_nonneg (entryNorm_nonneg _) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  change ‖∑ k, A i k * y k‖ ≤ _
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_le_entryNorm A i k) (norm_le_pi_norm y k) (norm_nonneg _)
    (entryNorm_nonneg _)

end BlockUnipotentInverse

end Langlands.HarishChandraSchwartz

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The rational point of `𝔾_m` given by a unit of `F`. -/
def gmRationalPoint (t : Fˣ) :
    Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (Gm (Spec (CommRingCat.of F))).X :=
  (Gm.pointsEquiv _ _).symm
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom t)

/-- If `χ ≫ ρ` is the diagonal cocharacter of `e`, then `ρ(χ(t)) = diag(t ^ e i)`. -/
theorem rationalMatrix_gmRationalPoint_comp {ρ : MatrixRepresentation G n}
    {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {e : n → ℤ}
    (h : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of F) e) (t : Fˣ) :
    ρ.rationalMatrix (gmRationalPoint t ≫ χ.hom.hom) = diagonalUnits F e t := by
  rw [rationalMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, h,
    pointsEquiv_diagonalCocharacter, gmRationalPoint, MulEquiv.apply_symm_apply]
  apply Units.ext
  ext i j
  simp only [coe_diagonalUnits, Matrix.GeneralLinearGroup.map_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [← map_zpow, Units.coe_map]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply _
  · simp [hij]

/-- The rational matrix of the conjugate representation `ρ ≫ Int(g)`. -/
theorem rationalMatrix_comp_innerIso (ρ : MatrixRepresentation G n)
    (g : rationalPoints (groupScheme n (CommRingCat.of F))) (x : rationalPoints G) :
    rationalMatrix (ρ ≫ ((groupScheme n (CommRingCat.of F)).innerIso g).hom) x =
      rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g *
        rationalMatrix ρ x *
        (rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) g)⁻¹ := by
  have h1 : ∀ y : rationalPoints G, ∀ f : MatrixRepresentation G n,
      rationalMatrix f y =
        rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) (y ≫ f.hom.hom) := by
    intro y f
    rw [← rationalMatrix_restrict]
    simp [restrict]
  rw [h1, h1 x ρ, Grp.comp_hom_hom, ← Category.assoc]
  change _ = _ * _ * _
  have h2 := congrArg (fun φ => φ (x ≫ ρ.hom.hom))
    (rationalPoints_map_innerIso (G := groupScheme n (CommRingCat.of F)) g)
  simp only [rationalPoints.map_apply] at h2
  rw [h2, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- Block unipotence of rational matrices is the same over `F` and over `Γ(Spec F)`. -/
theorem rationalMatrix_mem_blockUnipotentSubgroup_iff (ρ : MatrixRepresentation G n)
    (x : rationalPoints G) (e : n → ℤ) :
    ρ.rationalMatrix x ∈ blockUnipotentSubgroup F e ↔
      pointsEquiv n _ (Over.mk (𝟙 (Spec (CommRingCat.of F)))) (x ≫ ρ.hom.hom) ∈
        blockUnipotentSubgroup Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤) e := by
  constructor
  · intro h
    have h' := map_mem_blockUnipotentSubgroup e
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom h
    have heq : Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (ρ.rationalMatrix x) =
          pointsEquiv n _ (Over.mk (𝟙 (Spec (CommRingCat.of F)))) (x ≫ ρ.hom.hom) := by
      rw [rationalMatrix_apply]
      apply Units.ext
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [heq] at h'
    exact h'
  · intro h
    exact map_mem_blockUnipotentSubgroup e (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h

/-- Block triangularity of rational matrices is the same over `F` and over `Γ(Spec F)`. -/
theorem rationalMatrix_mem_blockParabolicSubgroup_iff (ρ : MatrixRepresentation G n)
    (x : rationalPoints G) (e : n → ℤ) :
    ρ.rationalMatrix x ∈ blockParabolicSubgroup F e ↔
      pointsEquiv n _ (Over.mk (𝟙 (Spec (CommRingCat.of F)))) (x ≫ ρ.hom.hom) ∈
        blockParabolicSubgroup Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤) e := by
  constructor
  · intro h
    have h' := map_mem_blockParabolicSubgroup e
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom h
    have heq : Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (ρ.rationalMatrix x) =
          pointsEquiv n _ (Over.mk (𝟙 (Spec (CommRingCat.of F)))) (x ≫ ρ.hom.hom) := by
      rw [rationalMatrix_apply]
      apply Units.ext
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [heq] at h'
    exact h'
  · intro h
    exact map_mem_blockParabolicSubgroup e (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.HarishChandraSchwartz

section NormContinuity

variable {F : Type*} [NormedField F] {X : Type*} [TopologicalSpace X]

/-- `x ↦ entryNorm (M x)` is continuous when every `x ↦ ‖M x i j‖` is. No topology on `F`
is used. -/
theorem continuous_entryNorm_comp {κ : Type*} [Fintype κ] [Nonempty κ] {M : X → Matrix κ κ F}
    (h : ∀ i j, Continuous fun x => ‖M x i j‖) : Continuous fun x => entryNorm (M x) :=
  Continuous.finset_sup'_apply _ fun p _ => h p.1 p.2

/-- `x ↦ ‖f x‖` (sup norm) is continuous when every `x ↦ ‖f x k‖` is. No topology on `F` is
used. -/
theorem continuous_norm_pi_comp {κ : Type*} [Fintype κ] {f : X → κ → F}
    (h : ∀ k, Continuous fun x => ‖f x k‖) : Continuous fun x => ‖f x‖ := by
  simp only [Pi.norm_def]
  exact NNReal.continuous_coe.comp
    (Continuous.finset_sup_apply fun k _ => (h k).subtype_mk fun x => norm_nonneg _)

end NormContinuity

end Langlands.HarishChandraSchwartz

namespace Langlands.LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue-normalized absolute value detects the order of the valuation. -/
theorem vle_of_residueNormalizedAbsoluteValue_le {x y : F}
    (h : residueNormalizedAbsoluteValue F x ≤ residueNormalizedAbsoluteValue F y) : x ≤ᵥ y := by
  have hq : (1 : ℝ≥0) < (residueCardinality F : ℝ≥0) := by
    exact_mod_cast residueCardinality_gt_one F
  have h' : (WithZeroMulInt.toNNReal hq.ne_zero
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (ValuativeRel.valuation F x)) : ℝ) ≤
    (WithZeroMulInt.toNNReal hq.ne_zero
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (ValuativeRel.valuation F y)) : ℝ) :=
    h
  rw [NNReal.coe_le_coe, (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le,
    map_le_map_iff] at h'
  exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F) x y).mpr h'

/-- The closed balls of the residue-normalized absolute value are compact. -/
theorem isCompact_residueNormalizedAbsoluteValue_le (C : ℝ) :
    IsCompact {x : F | residueNormalizedAbsoluteValue F x ≤ C} := by
  have hq : (1 : ℝ) < (residueCardinality F : ℝ) := by
    exact_mod_cast residueCardinality_gt_one F
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hq
  let b : F := (uniformizer F ^ k)⁻¹
  have hb : residueNormalizedAbsoluteValue F b = (residueCardinality F : ℝ) ^ k := by
    simp only [b, map_inv₀, map_pow, residueNormalizedAbsoluteValue_of_ord_one F
      (ord_uniformizer F), inv_pow, inv_inv]
  refine (IsNonarchimedeanLocalField.isCompact_closedBall F
    (ValuativeRel.valuation F b)).of_isClosed_subset
    (isClosed_le (Plancherel.continuous_residueNormalizedAbsoluteValue F) continuous_const)
    fun x hx => ?_
  have hxb := vle_of_residueNormalizedAbsoluteValue_le F
    ((show residueNormalizedAbsoluteValue F x ≤ C from hx).trans (hk.le.trans hb.ge))
  exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F) x b).mp hxb

end Langlands.LocalField

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- The largest residue-normalized absolute value of a coordinate of a vector over `F`. -/
def rationalVectorNorm {n : Type} [Fintype n] (v : n → F) : ℝ :=
  letI := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  ‖v‖

/-- For a closed representation, the rational points whose matrices and inverse matrices have
entries of absolute value at most `C` form a compact set. -/
theorem isCompact_rationalMatrix_entry_le {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ) (C : ℝ) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact {g : rationalPoints G | ∀ i j,
      LocalField.residueNormalizedAbsoluteValue F
          ((ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F) i j) ≤ C ∧
        LocalField.residueNormalizedAbsoluteValue F
          ((((ρ.rationalMatrix g)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) i j) ≤ C} := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let K : Set (Matrix (Fin N) (Fin N) F) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      {x | LocalField.residueNormalizedAbsoluteValue F x ≤ C}
  have hK : IsCompact K := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => LocalField.isCompact_residueNormalizedAbsoluteValue_le F C
  let e := Units.embedProduct (Matrix (Fin N) (Fin N) F) ∘ ρ.rationalMatrix
  have he : IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.comp (ρ.isClosedEmbedding_rationalMatrix hρ)
  have hprod : IsCompact (K ×ˢ (MulOpposite.opHomeomorph '' K)) :=
    hK.prod (hK.image MulOpposite.opHomeomorph.continuous)
  have hset : {g : rationalPoints G | ∀ i j,
      LocalField.residueNormalizedAbsoluteValue F
          ((ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F) i j) ≤ C ∧
        LocalField.residueNormalizedAbsoluteValue F
          ((((ρ.rationalMatrix g)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) i j) ≤ C} =
      e ⁻¹' (K ×ˢ (MulOpposite.opHomeomorph '' K)) := by
    ext g
    constructor
    · intro h
      exact ⟨fun i _ j _ => (h i j).1, ⟨_, fun i _ j _ => (h i j).2, rfl⟩⟩
    · rintro ⟨h1, M, hM, hMeq⟩
      have hMeq' : MulOpposite.op M = MulOpposite.op
          (((ρ.rationalMatrix g)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := hMeq
      have hM' := MulOpposite.op_injective hMeq'
      subst hM'
      exact fun i j => ⟨h1 i (Set.mem_univ _) j (Set.mem_univ _),
        hM i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [hset]
  exact he.isCompact_preimage hprod

/-- Absolute values of the entries of `ρ(g) - 1` are continuous in `g`. -/
theorem continuous_absoluteValue_rationalMatrix_sub_one_apply {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) (i j : n) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Continuous fun g : rationalPoints G => LocalField.residueNormalizedAbsoluteValue F
      (((ρ.rationalMatrix g : Matrix n n F) - 1) i j) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  exact (Plancherel.continuous_residueNormalizedAbsoluteValue F).comp
    ((ρ.continuous_rationalMatrix_entry i j).sub continuous_const)

/-- Absolute values of the coordinates of `ρ(g) w - w` are continuous in `g`. -/
theorem continuous_absoluteValue_rationalMatrix_mulVec_sub_apply {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) (w : n → F) (k : n) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Continuous fun g : rationalPoints G => LocalField.residueNormalizedAbsoluteValue F
      (((ρ.rationalMatrix g : Matrix n n F) *ᵥ w - w) k) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  refine (Plancherel.continuous_residueNormalizedAbsoluteValue F).comp ?_
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  exact (continuous_finsetSum _ fun l _ =>
    (ρ.continuous_rationalMatrix_entry k l).mul continuous_const).sub continuous_const

/-- The rational points whose matrices are block unipotent form a closed set. -/
theorem isClosed_rationalMatrix_mem_blockUnipotentSubgroup {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) (f : n → ℤ) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsClosed {g : rationalPoints G | ρ.rationalMatrix g ∈ blockUnipotentSubgroup F f} := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have hset : {g : rationalPoints G | ρ.rationalMatrix g ∈ blockUnipotentSubgroup F f} =
      ⋂ i, ⋂ j, ⋂ (_ : f i ≤ f j), {g : rationalPoints G |
        (ρ.rationalMatrix g : Matrix n n F) i j = (1 : Matrix n n F) i j} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_blockUnipotentSubgroup]
  rw [hset]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (ρ.continuous_rationalMatrix_entry i j) continuous_const

/-- **Heights on opposite unipotent points, diagonal case.** Let `χ` be a cocharacter of `G`
with `χ ≫ ρ₀ = diag(t ^ e₀ i)` for a closed representation `ρ₀` and `χ ≫ ρ = diag(t ^ e i)`
for a representation `ρ`. Let `w` be supported on the weight block `{e = m}` and assume that
the only point of `Ū(F) = U(χ⁻¹)(F)` fixing `w` is `1`. Then the height of `x ∈ Ū(F)` is at
most a constant times a power of `max 1 ‖ρ(x) w‖`. -/
theorem exists_rationalMatrixNorm_le_of_diagonal
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    {e₀ : Fin N → ℤ} (hχ₀ : χ ≫ ρ₀ = diagonalCocharacter (Fin N) (CommRingCat.of F) e₀)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n) {e : n → ℤ}
    (hχ : χ ≫ ρ = diagonalCocharacter n (CommRingCat.of F) e)
    {m : ℤ} {w : n → F} (hw : ∀ k, e k ≠ m → w k = 0)
    (hfix : ∀ x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints,
      (ρ.rationalMatrix x : Matrix n n F) *ᵥ w = w → x = 1) :
    ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ ∀ x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints,
      rationalMatrixNorm F ρ₀ x ≤
        C * max 1 (rationalVectorNorm F ((ρ.rationalMatrix x : Matrix n n F) *ᵥ w)) ^ D := by
  let τ : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsClosedImmersion ρ₀.hom.hom.left := hρ₀
  set U := (Dynamic.unipotent (CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints with hU
  have hmemU : ∀ x : rationalPoints G,
      x ∈ U ↔ ρ₀.rationalMatrix x ∈ blockUnipotentSubgroup F (-e₀) := by
    intro x
    rw [rationalMatrix_mem_blockUnipotentSubgroup_iff]
    exact Dynamic.mem_unipotent_iff_of_diagonal hχ₀ x
  have hρU : ∀ x ∈ U, ρ.rationalMatrix x ∈ blockUnipotentSubgroup F (-e) := by
    intro x hx
    rw [rationalMatrix_mem_blockUnipotentSubgroup_iff]
    have h := Dynamic.unipotent_le_comap _ ρ _ hx
    rw [SubgroupFunctor.mem_comap, Category.assoc, hχ, inv_comp_diagonalCocharacter,
      unipotent_diagonalCocharacter] at h
    exact h
  have hUc : IsClosed (U : Set (rationalPoints G)) := by
    have h : (U : Set (rationalPoints G)) =
        {g | ρ₀.rationalMatrix g ∈ blockUnipotentSubgroup F (-e₀)} := by
      ext g
      exact hmemU g
    rw [h]
    exact isClosed_rationalMatrix_mem_blockUnipotentSubgroup F ρ₀ (-e₀)
  have hK := isCompact_rationalMatrix_entry_le F ρ₀ hρ₀ 1
  let t : Fˣ := Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F)
  let a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
  have hD₀ : ρ₀.rationalMatrix a = diagonalUnits F e₀ t := rationalMatrix_gmRationalPoint_comp hχ₀ t
  have hD : ρ.rationalMatrix a = diagonalUnits F e t := rationalMatrix_gmRationalPoint_comp hχ t
  obtain ⟨d, hd⟩ := HarishChandraSchwartz.exists_weight_gap_le e₀
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  have hconj : ∀ x ∈ U, a⁻¹ * x * a ∈ U := by
    intro x hx
    rw [hmemU, map_mul, map_mul, map_inv, hD₀]
    exact HarishChandraSchwartz.diagonalUnits_conj_mem e₀ t ((hmemU x).1 hx)
  let c : U → U := fun x => ⟨a⁻¹ * x * a, hconj x x.2⟩
  have hq1 : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have htn : ‖(t : F)‖ = (LocalField.residueCardinality F : ℝ)⁻¹ :=
    LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F)
  have ht : ‖(t : F)‖ < 1 := by
    rw [htn]
    exact inv_lt_one_of_one_lt₀ hq1
  let r₀ : U → GL (Fin N) F := fun x => ρ₀.rationalMatrix x.1
  let r : U → GL n F := fun x => ρ.rationalMatrix x.1
  have hβc : Continuous fun x : U => HarishChandraSchwartz.offIdentityNorm (r₀ x) :=
    HarishChandraSchwartz.continuous_entryNorm_comp fun i j =>
      (continuous_absoluteValue_rationalMatrix_sub_one_apply F ρ₀ i j).comp continuous_subtype_val
  have hgc : Continuous fun x : U => ‖(r x : Matrix n n F) *ᵥ w - w‖ :=
    HarishChandraSchwartz.continuous_norm_pi_comp fun k =>
      (continuous_absoluteValue_rationalMatrix_mulVec_sub_apply F ρ w k).comp
        continuous_subtype_val
  have hS : IsCompact (HarishChandraSchwartz.contractionScalingAnnulus
      (fun x => HarishChandraSchwartz.offIdentityNorm (r₀ x)) ‖(t : F)‖⁻¹ d) := by
    have hK' : IsCompact ((↑) ⁻¹' {g : rationalPoints G | ∀ i j,
      LocalField.residueNormalizedAbsoluteValue F
          ((ρ₀.rationalMatrix g : Matrix (Fin N) (Fin N) F) i j) ≤ 1 ∧
        LocalField.residueNormalizedAbsoluteValue F
          ((((ρ₀.rationalMatrix g)⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) i j) ≤ 1} :
          Set U) :=
      hUc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    refine hK'.of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le continuous_const (continuous_const.mul hβc)).inter
        (isClosed_le hβc continuous_const)
    · have hβ1 : HarishChandraSchwartz.offIdentityNorm (r₀ x) ≤ 1 := hx.2
      have hmax : max 1 (HarishChandraSchwartz.offIdentityNorm (r₀ x)) = 1 := max_eq_left hβ1
      intro i j
      constructor
      · have h := (HarishChandraSchwartz.norm_le_entryNorm _ i j).trans
          (HarishChandraSchwartz.entryNorm_le_max_offIdentityNorm (r₀ x))
        rw [hmax] at h
        exact h
      · have h := (HarishChandraSchwartz.norm_le_entryNorm _ i j).trans
          (HarishChandraSchwartz.entryNorm_inv_le ((hmemU x.1).1 x.2) hd)
        rw [hmax, one_pow] at h
        exact h
  obtain ⟨C₁, hC₁, hb⟩ := HarishChandraSchwartz.exists_offIdentityNorm_le_mul_pow c r₀ r t ht
    (fun x => (hmemU x.1).1 x.2) (fun x => hρU x.1 x.2)
    (fun x => by
      change ρ₀.rationalMatrix (a⁻¹ * x.1 * a) = _
      rw [map_mul, map_mul, map_inv, hD₀])
    (fun x => by
      change ρ.rationalMatrix (a⁻¹ * x.1 * a) = _
      rw [map_mul, map_mul, map_inv, hD])
    hw (fun x hx => by
      change ρ₀.rationalMatrix x.1 = 1
      rw [hfix x.1 x.2 hx, map_one]) hd hS hgc.continuousOn
  set L : ℝ := 1 + ‖w‖ with hL
  have hL1 : 1 ≤ L := le_add_of_nonneg_right (norm_nonneg _)
  set C₂ : ℝ := max 1 (C₁ * L ^ d) with hC₂
  have hC₂1 : 1 ≤ C₂ := le_max_left _ _
  refine ⟨C₂ ^ (d + 1), d * (d + 1), pow_pos (zero_lt_one.trans_le hC₂1) _, fun x hx => ?_⟩
  set Y : ℝ := max 1 ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ w‖ with hY
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hYd : 1 ≤ Y ^ d := one_le_pow₀ hY1
  have hg : ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ w - w‖ ≤ L * Y := by
    refine (norm_sub_le _ _).trans ?_
    calc ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ w‖ + ‖w‖ ≤ Y + ‖w‖ * Y :=
          add_le_add (le_max_right _ _) (le_mul_of_one_le_right (norm_nonneg _) hY1)
      _ = L * Y := by rw [hL]; ring
  have hβ : HarishChandraSchwartz.offIdentityNorm (ρ₀.rationalMatrix x) ≤ C₂ * Y ^ d := by
    by_cases h1 : 1 ≤ HarishChandraSchwartz.offIdentityNorm (ρ₀.rationalMatrix x)
    · calc HarishChandraSchwartz.offIdentityNorm (ρ₀.rationalMatrix x)
          ≤ C₁ * ‖(ρ.rationalMatrix x : Matrix n n F) *ᵥ w - w‖ ^ d := hb ⟨x, hx⟩ h1
        _ ≤ C₁ * (L * Y) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg d) hC₁.le
        _ = C₁ * L ^ d * Y ^ d := by rw [mul_pow, mul_assoc]
        _ ≤ C₂ * Y ^ d :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hYd)
    · rw [not_le] at h1
      exact h1.le.trans (one_le_mul_of_one_le_of_one_le hC₂1 hYd)
  have hmax : max 1 (HarishChandraSchwartz.offIdentityNorm (ρ₀.rationalMatrix x)) ≤ C₂ * Y ^ d :=
    max_le (one_le_mul_of_one_le_of_one_le hC₂1 hYd) hβ
  change HarishChandraSchwartz.glNorm (ρ₀.rationalMatrix x) ≤ C₂ ^ (d + 1) * Y ^ (d * (d + 1))
  calc HarishChandraSchwartz.glNorm (ρ₀.rationalMatrix x)
      ≤ max 1 (HarishChandraSchwartz.offIdentityNorm (ρ₀.rationalMatrix x)) ^ (d + 1) :=
        HarishChandraSchwartz.glNorm_le_max_offIdentityNorm_pow ((hmemU x).1 hx) hd
    _ ≤ (C₂ * Y ^ d) ^ (d + 1) :=
        pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hmax _
    _ = C₂ ^ (d + 1) * Y ^ (d * (d + 1)) := by rw [mul_pow, ← pow_mul]

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
