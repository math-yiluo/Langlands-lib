import Langlands.Geometry.Analytic.DrinfeldGroupAction

/-! # Norms on coefficient vectors and the reduction map of Drinfeld's upper half space -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory PresentedAffinoidAlgebra GeneralizedTateAlgebra

/-! ## Ultrametric norms on vector spaces -/

/-- An ultrametric norm on an `F`-vector space `V`, in multiplicative form. -/
structure VectorNorm (F : Type v) [NormedField F] (V : Type w) [AddCommGroup V]
    [Module F V] where
  /-- The value of the norm. -/
  toFun : V → ℝ
  pos' : ∀ x : V, x ≠ 0 → 0 < toFun x
  smul' : ∀ (t : F) (x : V), toFun (t • x) = ‖t‖ * toFun x
  add_le_max' : ∀ x y : V, toFun (x + y) ≤ max (toFun x) (toFun y)

namespace VectorNorm

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

instance : CoeFun (VectorNorm F V) fun _ => V → ℝ := ⟨VectorNorm.toFun⟩

@[ext]
theorem ext {ν μ : VectorNorm F V} (h : ∀ x, ν x = μ x) : ν = μ := by
  cases ν
  cases μ
  congr
  exact funext h

theorem pos (ν : VectorNorm F V) {x : V} (hx : x ≠ 0) : 0 < ν x := ν.pos' x hx

theorem map_smul (ν : VectorNorm F V) (t : F) (x : V) : ν (t • x) = ‖t‖ * ν x := ν.smul' t x

theorem add_le_max (ν : VectorNorm F V) (x y : V) : ν (x + y) ≤ max (ν x) (ν y) :=
  ν.add_le_max' x y

@[simp]
theorem map_zero (ν : VectorNorm F V) : ν 0 = 0 := by
  have h := ν.map_smul 0 0
  rw [zero_smul, norm_zero, zero_mul] at h
  exact h

theorem nonneg (ν : VectorNorm F V) (x : V) : 0 ≤ ν x := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  · exact (ν.pos hx).le

/-- Two norms are homothetic if they differ by a positive constant factor. -/
def Homothetic (ν μ : VectorNorm F V) : Prop := ∃ c : ℝ, 0 < c ∧ ∀ x, μ x = c * ν x

theorem Homothetic.refl (ν : VectorNorm F V) : Homothetic ν ν := ⟨1, one_pos, fun _ => (one_mul _).symm⟩

theorem Homothetic.symm {ν μ : VectorNorm F V} (h : Homothetic ν μ) : Homothetic μ ν := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c⁻¹, inv_pos.2 hc, fun x => ?_⟩
  rw [h, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem Homothetic.trans {ν μ ρ : VectorNorm F V} (h₁ : Homothetic ν μ) (h₂ : Homothetic μ ρ) :
    Homothetic ν ρ := by
  obtain ⟨c, hc, h₁⟩ := h₁
  obtain ⟨c', hc', h₂⟩ := h₂
  exact ⟨c' * c, mul_pos hc' hc, fun x => by rw [h₂, h₁, mul_assoc]⟩

variable (F V) in
/-- Homothety of norms. -/
def homotheticSetoid : Setoid (VectorNorm F V) where
  r := Homothetic
  iseqv := ⟨Homothetic.refl, Homothetic.symm, Homothetic.trans⟩

/-- The topology of pointwise convergence. -/
instance : TopologicalSpace (VectorNorm F V) :=
  TopologicalSpace.induced (fun ν : VectorNorm F V => (ν : V → ℝ)) inferInstance

end VectorNorm

variable (F : Type v) [NormedField F] (V : Type w) [AddCommGroup V] [Module F V] in
/-- Norms on `V` up to homothety. For `V = F^{d+1}` over a local field this is the
Bruhat–Tits building of `PGL_{d+1}(F)` (Bruhat–Tits 1984, 2.11). -/
abbrev NormClass := Quotient (VectorNorm.homotheticSetoid F V)

/-! ## The action of invertible matrices -/

namespace VectorNorm

variable {F : Type v} [NormedField F] {n : Type w} [Fintype n] [DecidableEq n]

theorem vecMul_ne_zero (γ : Matrix.GeneralLinearGroup n F) {a : n → F} (ha : a ≠ 0) :
    Matrix.vecMul a (γ : Matrix n n F) ≠ 0 := by
  intro h
  apply ha
  have h1 : (γ : Matrix n n F) * ((γ⁻¹ : Matrix.GeneralLinearGroup n F) : Matrix n n F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc a = Matrix.vecMul a 1 := (Matrix.vecMul_one a).symm
    _ = Matrix.vecMul (Matrix.vecMul a (γ : Matrix n n F))
          ((γ⁻¹ : Matrix.GeneralLinearGroup n F) : Matrix n n F) := by
        rw [Matrix.vecMul_vecMul, h1]
    _ = 0 := by rw [h, Matrix.zero_vecMul]

/-- The norm `a ↦ ν(a γ)` on row vectors. -/
def comapMatrix (ν : VectorNorm F (n → F)) (γ : Matrix.GeneralLinearGroup n F) :
    VectorNorm F (n → F) where
  toFun a := ν (Matrix.vecMul a (γ : Matrix n n F))
  pos' _ ha := ν.pos (vecMul_ne_zero γ ha)
  smul' t a := by rw [Matrix.smul_vecMul, ν.map_smul]
  add_le_max' a b := by rw [Matrix.add_vecMul]; exact ν.add_le_max _ _

/-- `GL_n(F)` acts on norms of row vectors by `(γ • ν)(a) = ν(a γ)`. -/
instance : MulAction (Matrix.GeneralLinearGroup n F) (VectorNorm F (n → F)) where
  smul γ ν := ν.comapMatrix γ
  one_smul ν := ext fun a => by
    change ν (Matrix.vecMul a ((1 : Matrix.GeneralLinearGroup n F) : Matrix n n F)) = ν a
    rw [Units.val_one, Matrix.vecMul_one]
  mul_smul γ γ' ν := ext fun a => by
    change ν (Matrix.vecMul a ((γ * γ' : Matrix.GeneralLinearGroup n F) : Matrix n n F)) =
      ν (Matrix.vecMul (Matrix.vecMul a (γ : Matrix n n F)) (γ' : Matrix n n F))
    rw [Units.val_mul, Matrix.vecMul_vecMul]

theorem smul_apply (γ : Matrix.GeneralLinearGroup n F) (ν : VectorNorm F (n → F)) (a : n → F) :
    (γ • ν) a = ν (Matrix.vecMul a (γ : Matrix n n F)) := rfl

theorem Homothetic.smul {ν μ : VectorNorm F (n → F)} (h : Homothetic ν μ)
    (γ : Matrix.GeneralLinearGroup n F) : Homothetic (γ • ν) (γ • μ) := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun a => h _⟩

end VectorNorm

namespace NormClass

variable {F : Type v} [NormedField F] {n : Type w} [Fintype n] [DecidableEq n]

instance : MulAction (Matrix.GeneralLinearGroup n F) (NormClass F (n → F)) where
  smul γ := Quotient.map (γ • ·) fun _ _ h => VectorNorm.Homothetic.smul h γ
  one_smul p := Quotient.inductionOn p fun ν => congrArg Quotient.mk'' (one_smul _ ν)
  mul_smul γ γ' p := Quotient.inductionOn p fun ν => congrArg Quotient.mk'' (mul_smul γ γ' ν)

theorem smul_mk (γ : Matrix.GeneralLinearGroup n F) (ν : VectorNorm F (n → F)) :
    γ • (⟦ν⟧ : NormClass F (n → F)) = ⟦γ • ν⟧ := rfl

end NormClass

/-! ## The reduction map -/

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable {F : Type v} [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coefficients_add (a b : Fin (d + 1) → F) :
    coefficients F K d (a + b) = coefficients F K d a + coefficients F K d b := by
  ext i
  simp [coefficients]

theorem linearNorm_nonneg (c : Fin (d + 1) → K) (z : Space K d) : 0 ≤ linearNorm K d c z := by
  obtain ⟨m, s, rfl⟩ := exists_chart K d z
  rw [linearNorm_chart]
  exact apply_nonneg _ _

theorem linearNorm_add_le (c c' : Fin (d + 1) → K) (z : Space K d) :
    linearNorm K d (c + c') z ≤ max (linearNorm K d c z) (linearNorm K d c' z) := by
  obtain ⟨m, s, rfl⟩ := exists_chart K d z
  rw [linearNorm_chart, linearNorm_chart, linearNorm_chart, linearForm_add]
  exact BanachSpectrum.isNonarchimedean (K := K) s _ _

theorem linearNorm_coefficients_smul (t : F) (a : Fin (d + 1) → F) (z : Space K d) :
    linearNorm K d (coefficients F K d (t • a)) z = ‖t‖ * linearNorm K d (coefficients F K d a) z := by
  obtain ⟨m, s, rfl⟩ := exists_chart K d z
  rw [linearNorm_chart, linearNorm_chart, coefficients_smul, linearForm_smul,
    map_mul s.toMulRingSeminorm]
  change s (algebraMap K (disc K d m) (algebraMap F K t)) * _ = _
  rw [BanachSpectrum.algebraMap_apply, norm_algebraMap']

/-- The norm `a ↦ |ℓ_a(z)|` on coefficient vectors attached to a point `z` of `Ω`. -/
def omegaNorm (z : Omega F K d) : VectorNorm F (Fin (d + 1) → F) where
  toFun a := linearNorm K d (coefficients F K d a) z
  pos' a ha := lt_of_le_of_ne (linearNorm_nonneg K _ _) (Ne.symm (z.2 a ha))
  smul' t a := linearNorm_coefficients_smul K t a z
  add_le_max' a b := by
    rw [coefficients_add]
    exact linearNorm_add_le K _ _ _

theorem omegaNorm_apply (z : Omega F K d) (a : Fin (d + 1) → F) :
    omegaNorm K z a = linearNorm K d (coefficients F K d a) z := rfl

theorem continuous_omegaNorm : Continuous (omegaNorm (F := F) K (d := d)) :=
  continuous_induced_rng.2 (continuous_pi fun _ =>
    (continuous_linearNorm K d _).comp continuous_subtype_val)

/-- The reduction map `Res : Ω → BT`: the homothety class of `a ↦ |ℓ_a(z)|`. -/
def reduction (z : Omega F K d) : NormClass F (Fin (d + 1) → F) := ⟦omegaNorm K z⟧

theorem continuous_reduction : Continuous (reduction (F := F) K (d := d)) :=
  continuous_quotient_mk'.comp (continuous_omegaNorm K)

variable [ProperSpace F] [NeZero d]

/-- `|ℓ_a(γ · z)| = |ℓ_{a γ}(z)| · |ℓ_{γ_0}(z)|⁻¹`. -/
theorem omegaNorm_actionMap (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (U : ExhaustionIndex F K d) (x : BanachSpectrum (exhaustionChart F K d U.level).algebra)
    (a : Fin (d + 1) → F) :
    omegaNorm K (actionMap K γ (exhaustionChartMap F K d U x)) a =
      x (inverse F K d (entries_row_zero_ne_zero γ) U.level) *
        omegaNorm K (exhaustionChartMap F K d U x) (Matrix.vecMul a (entries γ)) := by
  rw [omegaNorm_apply, omegaNorm_apply, actionMap_chart]
  change linearNorm K d (coefficients F K d a) (actionPoint K _ _ _ _ _ x) = _
  rw [linearNorm_actionPoint, mul_comm]
  rfl

/-- The reduction map is `GL_{d+1}(F)`-equivariant. -/
theorem reduction_actionMap (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) (z : Omega F K d) :
    reduction K (actionMap K γ z) = γ • reduction K z := by
  obtain ⟨U, x, rfl⟩ := exists_exhaustionChartMap_eq K z
  refine Quotient.sound (VectorNorm.Homothetic.symm
    ⟨x (inverse F K d (entries_row_zero_ne_zero γ) U.level), ?_, fun a => ?_⟩)
  · exact lt_of_le_of_ne (apply_nonneg _ _)
      (Ne.symm (inverse_apply_ne_zero K _ (entries_row_zero_ne_zero γ) U.level x))
  · exact omegaNorm_actionMap K γ U x a

/-! ## Scalar matrices -/

/-- A matrix whose action has the identity as pullback on every member acts as the identity. -/
theorem actionMap_eq_self (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (hid : ∀ U : ExhaustionIndex F K d, IsActionPullback K (entries γ)
      (entries_row_zero_ne_zero γ) U U
      (BoundedAlgHom.id K (exhaustionChart F K d U.level).algebra))
    (z : Omega F K d) : actionMap K γ z = z := by
  obtain ⟨U, x, rfl⟩ := exists_exhaustionChartMap_eq K z
  apply Subtype.ext
  rw [actionMap_chart, ← (hid U).chart_eq K x]
  exact congrArg (fun y => (exhaustionChartMap F K d U y).1)
    (BanachSpectrum.ext fun _ => rfl)

theorem compatibleHom_eq_id (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F)
    (hid : ∀ U : ExhaustionIndex F K d, IsActionPullback K (entries γ)
      (entries_row_zero_ne_zero γ) U U
      (BoundedAlgHom.id K (exhaustionChart F K d U.level).algebra)) :
    compatibleHom K γ = 𝟙 (compatiblePresentation F K d) := by
  refine AffinoidAtlasPresentation.CompatibleStrongHom.ext_of_pullback
    (ContinuousMap.ext (actionMap_eq_self K γ hid)) fun U => ?_
  have hU : (compatibleHom K γ).baseMap ''
        Set.range ((compatiblePresentation F K d).presentation.atlas.chart U) ⊆
      Set.range ((compatiblePresentation F K d).presentation.atlas.chart U) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (actionMap_eq_self K γ hid _).symm⟩
  refine ⟨U, hU, ?_⟩
  have hs : (targetIndex K γ U).1 ⊆ U.1 := targetIndex_subset K γ (hid U)
  refine (AffinoidAtlasPresentation.CompatibleStrongHom.ofChain_pullback_upper _ _ U U hU
    ((range_exhaustionChartMap_subset_iff F K d).2 hs)).trans
      (Eq.trans ?_ ((exhaustionAtlas F K d).restriction_id U Subset.rfl).symm)
  exact ((pullback_isActionPullback K γ U).comp_res hs).eq (hid U)

section scalar

variable (γ : Matrix.GeneralLinearGroup (Fin (d + 1)) F) {c : F}
  (hγ : (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = c • 1)
include hγ

omit [ProperSpace F] [NeZero d] in
theorem scalar_ne_zero : c ≠ 0 := by
  rintro rfl
  apply entries_row_zero_ne_zero γ
  funext j
  simp [entries, hγ]

omit [IsUltrametricDist K] [CompleteSpace K] [ProperSpace F] [NeZero d] in
theorem coefficients_entries_scalar (k : Fin (d + 1)) :
    coefficients F K d (entries γ k) = algebraMap F K c • Pi.single k 1 := by
  rw [← coefficients_entries_one (F := F) K k]
  ext j
  simp [coefficients, entries, hγ, Matrix.smul_apply]

omit [NeZero d] in
theorem actionTuple_scalar (N : ℕ) (i : Fin d) :
    actionTuple K (entries γ) (entries_row_zero_ne_zero γ) N i =
      (exhaustionChart F K d N).baseMap (coordinate K (disc K d N) i) := by
  have hc : algebraMap F K c ≠ 0 := (map_ne_zero (algebraMap F K)).2 (scalar_ne_zero γ hγ)
  set β := (exhaustionChart F K d N).baseMap
  have hinv : inverse F K d (entries_row_zero_ne_zero γ) N =
      algebraMap K (exhaustionChart F K d N).algebra (algebraMap F K c)⁻¹ := by
    refine (eq_inverse_of_mul_eq_one F K d _ N ?_).symm
    rw [coefficients_entries_scalar K γ hγ, linearForm_smul, linearForm_single_zero, mul_one,
      AlgHom.commutes, ← map_mul, mul_inv_cancel₀ hc, map_one]
  unfold actionTuple
  rw [hinv, coefficients_entries_scalar K γ hγ, linearForm_smul, linearForm_single_succ,
    map_mul, AlgHom.commutes, mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one,
    one_mul]

/-- Scalar matrices act trivially on `Ω`. -/
theorem compatibleHom_scalar : compatibleHom K γ = 𝟙 (compatiblePresentation F K d) :=
  compatibleHom_eq_id K γ fun U i => (actionTuple_scalar K γ hγ U.level i).symm

theorem omegaAction_ρ_scalar : (omegaAction F K d).ρ γ = 𝟙 _ := by
  rw [omegaAction_ρ, compatibleHom_scalar K γ hγ]
  exact (CompatibleAtlasPresentation.saturationFunctor ⋙
    SaturatedAtlasPresentation.localizationFunctor).map_id _

omit [ProperSpace F] [NeZero d] in
/-- Scalar matrices act trivially on classes of norms. -/
theorem smul_normClass_scalar (p : NormClass F (Fin (d + 1) → F)) : γ • p = p := by
  induction p using Quotient.inductionOn with
  | h ν =>
    refine Quotient.sound (VectorNorm.Homothetic.symm ⟨‖c‖, norm_pos_iff.2 (scalar_ne_zero γ hγ),
      fun a => ?_⟩)
    change ν (Matrix.vecMul a (γ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) = _
    rw [hγ, Matrix.vecMul_smul, Matrix.vecMul_one, ν.map_smul]

end scalar

end DrinfeldUpperHalfSpace

end Langlands.Analytic
