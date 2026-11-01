import Langlands.Global.IdeleAbsoluteValue
import Langlands.Global.AdelicBlockParabolic
import Langlands.Global.FiniteAdelicGL.Determinant
import Langlands.Representation.Jacquet.PositiveCharacter

/-!
# Actual adelic block determinant characters

The actual normalized idelic norm supplies every determinant factor. The
positive square root is canonical. Haar scaling is a separate identification.
-/

noncomputable section

universe uF

namespace Langlands.Global.AdelicBlockDeterminantCharacter

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped BigOperators NNReal

variable (F : Type uF) [Field F] [NumberField F]

/-- The actual full adelic determinant norm, with its units topology. -/
def determinantNorm (n : ℕ) : AdelicGL F n →ₜ* ℝ≥0ˣ :=
  (IdeleAbsoluteValue.full F).comp (AdelicGL.determinant F n)

/-- The actual finite adelic determinant norm. -/
def finiteDeterminantNorm (n : ℕ) : FiniteAdelicGL F n →ₜ* ℝ≥0ˣ :=
  (IdeleAbsoluteValue.finite F).comp (FiniteAdelicGL.determinant F n)

/-- The actual archimedean determinant norm, retaining all place multiplicities. -/
def infiniteDeterminantNorm (n : ℕ) : InfiniteAdelicGL F n →ₜ* ℝ≥0ˣ where
  toMonoidHom := (IdeleAbsoluteValue.infinite F).toMonoidHom.comp Matrix.GeneralLinearGroup.det
  continuous_toFun :=
    (IdeleAbsoluteValue.infinite F).continuous.comp Matrix.GeneralLinearGroup.continuous_det

@[simp]
theorem determinantNorm_rational (n : ℕ) (g : RationalGL F n) :
    determinantNorm F n (AdelicGL.rational F n g) = 1 := by
  change IdeleAbsoluteValue.full F
    (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F)) g)) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact IdeleAbsoluteValue.full_diagonalUnits F (Matrix.GeneralLinearGroup.det g)

@[simp]
theorem determinantNorm_scalar (n : ℕ) (a : Ideles F) :
    determinantNorm F n (AdelicGL.scalar F n a) = IdeleAbsoluteValue.full F a ^ n := by
  change IdeleAbsoluteValue.full F
    (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) a)) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]

/-- The full determinant norm is the product of the genuine two factors. -/
theorem determinantNorm_split (n : ℕ) (g : AdelicGL F n) :
    determinantNorm F n g =
      infiniteDeterminantNorm F n (AdelicGL.infinite F n g) *
        finiteDeterminantNorm F n (AdelicGL.finite F n g) := by
  have hi := Matrix.GeneralLinearGroup.map_det
    (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F)) g
  have hf := Matrix.GeneralLinearGroup.map_det
    (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F)) g
  change IdeleAbsoluteValue.infinite F
      ((ideleProductEquiv F (Matrix.GeneralLinearGroup.det g)).1) *
    IdeleAbsoluteValue.finite F
      ((ideleProductEquiv F (Matrix.GeneralLinearGroup.det g)).2) = _
  change _ = IdeleAbsoluteValue.infinite F
      (Matrix.GeneralLinearGroup.det (AdelicGL.infinite F n g)) *
    IdeleAbsoluteValue.finite F
      (Matrix.GeneralLinearGroup.det (AdelicGL.finite F n g))
  change Matrix.GeneralLinearGroup.det (AdelicGL.infinite F n g) = _ at hi
  change Matrix.GeneralLinearGroup.det (AdelicGL.finite F n g) = _ at hf
  rw [hi, hf]
  rfl

@[simp]
theorem determinantNorm_ofFinite (n : ℕ) (g : FiniteAdelicGL F n) :
    determinantNorm F n (AdelicGL.ofFinite F n g) = finiteDeterminantNorm F n g := by
  change IdeleAbsoluteValue.full F (AdelicGL.determinant F n (AdelicGL.ofFinite F n g)) = _
  rw [AdelicGL.determinant_ofFinite, IdeleAbsoluteValue.full_finiteIdelesInclusion]
  rfl

/-- The restriction to a single finite matrix group has the actual normalized local norm. -/
@[simp]
theorem coe_determinantNorm_localInclusion (n : ℕ) (v : FinitePlace F)
    (g : FiniteLocalGL F n v) :
    ((determinantNorm F n
      (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v g)) : ℝ≥0) : ℝ) =
        ‖(Matrix.GeneralLinearGroup.det g).val‖ := by
  change ((IdeleAbsoluteValue.full F
    (AdelicGL.determinant F n
      (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v g))) : ℝ≥0) : ℝ) = _
  rw [AdelicGL.determinant_ofFinite_localInclusion]
  exact IdeleAbsoluteValue.coe_full_finiteIdeleInclusion F v _

variable {n : ℕ} (B : BlockShape n)

private def blockProductHom {G : Type*} [Group G]
    (d : Fin B.length → G →* ℝ≥0ˣ) : G →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    d i ^ B.size j / d j ^ B.size i

private theorem blockProductHom_apply {G : Type*} [Group G]
    (d : Fin B.length → G →* ℝ≥0ˣ) (g : G) :
    blockProductHom B d g =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        d i g ^ B.size j / d j g ^ B.size i := by
  simp [blockProductHom]

private def blockProduct {G : Type*} [Group G] [TopologicalSpace G]
    (d : Fin B.length → G →ₜ* ℝ≥0ˣ) : G →ₜ* ℝ≥0ˣ where
  toMonoidHom := blockProductHom B (fun i => (d i).toMonoidHom)
  continuous_toFun := by
    change Continuous (fun g => blockProductHom B (fun i => (d i).toMonoidHom) g)
    simp_rw [blockProductHom_apply]
    simp only [div_eq_mul_inv]
    exact continuous_finsetProd _ fun i _ =>
      continuous_finsetProd _ fun j _ =>
        ((d i).continuous.pow _).mul ((d j).continuous.pow _).inv

/-- The full normalized determinant of an actual adelic Levi block. -/
def blockDeterminantNorm (i : Fin B.length) : FullLevi F B →ₜ* ℝ≥0ˣ where
  toFun m := determinantNorm F (B.size i) (m i)
  map_one' := map_one _
  map_mul' m k := map_mul _ (m i) (k i)
  continuous_toFun := (determinantNorm F (B.size i)).continuous.comp (continuous_apply i)

/-- The normalized determinant of an actual finite adelic Levi block. -/
def finiteBlockDeterminantNorm (i : Fin B.length) : FiniteLevi F B →ₜ* ℝ≥0ˣ where
  toFun m := finiteDeterminantNorm F (B.size i) (m i)
  map_one' := map_one _
  map_mul' m k := map_mul _ (m i) (k i)
  continuous_toFun := (finiteDeterminantNorm F (B.size i)).continuous.comp (continuous_apply i)

/-- The normalized determinant of an actual archimedean Levi block. -/
def infiniteBlockDeterminantNorm (i : Fin B.length) : InfiniteLevi F B →ₜ* ℝ≥0ˣ where
  toFun m := infiniteDeterminantNorm F (B.size i) (m i)
  map_one' := map_one _
  map_mul' m k := map_mul _ (m i) (k i)
  continuous_toFun := (infiniteDeterminantNorm F (B.size i)).continuous.comp (continuous_apply i)

/-- The positive pairwise determinant character on the actual full adelic Levi. -/
def leviCharacter : FullLevi F B →ₜ* ℝ≥0ˣ :=
  blockProduct B (blockDeterminantNorm F B)

/-- The same pairwise formula on the actual finite adelic Levi. -/
def finiteLeviCharacter : FiniteLevi F B →ₜ* ℝ≥0ˣ :=
  blockProduct B (finiteBlockDeterminantNorm F B)

/-- The same pairwise formula on the actual archimedean Levi. -/
def infiniteLeviCharacter : InfiniteLevi F B →ₜ* ℝ≥0ˣ :=
  blockProduct B (infiniteBlockDeterminantNorm F B)

theorem leviCharacter_apply (m : FullLevi F B) :
    leviCharacter F B m =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        determinantNorm F (B.size i) (m i) ^ B.size j /
          determinantNorm F (B.size j) (m j) ^ B.size i :=
  blockProductHom_apply B _ m

theorem finiteLeviCharacter_apply (m : FiniteLevi F B) :
    finiteLeviCharacter F B m =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        finiteDeterminantNorm F (B.size i) (m i) ^ B.size j /
          finiteDeterminantNorm F (B.size j) (m j) ^ B.size i :=
  blockProductHom_apply B _ m

theorem infiniteLeviCharacter_apply (m : InfiniteLevi F B) :
    infiniteLeviCharacter F B m =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        infiniteDeterminantNorm F (B.size i) (m i) ^ B.size j /
          infiniteDeterminantNorm F (B.size j) (m j) ^ B.size i :=
  blockProductHom_apply B _ m

/-- Pairwise factorization is compatible with the actual finite/infinite Levi splitting. -/
theorem leviCharacter_split (m : FullLevi F B) :
    leviCharacter F B m =
      infiniteLeviCharacter F B (leviInfinite F B m) *
        finiteLeviCharacter F B (leviFinite F B m) := by
  rw [leviCharacter_apply, infiniteLeviCharacter_apply, finiteLeviCharacter_apply]
  simp_rw [determinantNorm_split, mul_pow, ← div_mul_div_comm]
  simp only [leviInfinite, leviFinite, Finset.prod_mul_distrib]
  rfl

/-- The actual rational block diagonal map, without a topology on the number field. -/
def rationalLevi : B.Levi F →* FullLevi F B where
  toFun m i := AdelicGL.rational F (B.size i) (m i)
  map_one' := funext fun i => map_one (AdelicGL.rational F (B.size i))
  map_mul' m k := funext fun i => map_mul (AdelicGL.rational F (B.size i)) (m i) (k i)

@[simp]
theorem leviCharacter_rational (m : B.Levi F) :
    leviCharacter F B (rationalLevi F B m) = 1 := by
  rw [leviCharacter_apply]
  simp only [rationalLevi, MonoidHom.coe_mk, OneHom.coe_mk, determinantNorm_rational,
    one_pow, div_self', Finset.prod_const_one]

@[simp]
theorem leviCharacter_scalar (a : Ideles F) :
    leviCharacter F B (fun i => AdelicGL.scalar F (B.size i) a) = 1 := by
  rw [leviCharacter_apply]
  simp only [determinantNorm_scalar]
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j _
  rw [← pow_mul, ← pow_mul, Nat.mul_comm (B.size i) (B.size j)]
  exact div_self' _

/-- Inflate the constructed character through the actual continuous diagonal-block projection. -/
def parabolicCharacter : Full F B →ₜ* ℝ≥0ˣ :=
  (leviCharacter F B).comp (B.leviProjectionContinuous (Adeles F))

@[simp]
theorem parabolicCharacter_section (m : FullLevi F B) :
    parabolicCharacter F B (B.leviInParabolic (Adeles F) m) = leviCharacter F B m := by
  change leviCharacter F B (B.leviProjection (Adeles F) (B.leviInParabolic (Adeles F) m)) = _
  rw [B.leviProjection_section]

@[simp]
theorem parabolicCharacter_unipotent (u : B.unipotentRadical (Adeles F)) :
    parabolicCharacter F B u = 1 := by
  change leviCharacter F B (B.leviProjection (Adeles F) u.val) = 1
  rw [u.property, map_one]

@[simp]
theorem leviProjection_rational (g : Rational F B) :
    B.leviProjection (Adeles F) (AdelicBlockParabolic.rational F B g) =
      rationalLevi F B (B.leviProjection F g) := by
  funext i
  apply Units.ext
  ext a b
  rfl

@[simp]
theorem parabolicCharacter_rational (g : Rational F B) :
    parabolicCharacter F B (AdelicBlockParabolic.rational F B g) = 1 := by
  change leviCharacter F B (B.leviProjection (Adeles F)
    (AdelicBlockParabolic.rational F B g)) = 1
  rw [leviProjection_rational, leviCharacter_rational]

/-- The canonical positive half in nonnegative real units. -/
def leviPositiveHalf : FullLevi F B →ₜ* ℝ≥0ˣ where
  toMonoidHom := Jacquet.positiveHalfCharacter (leviCharacter F B).toMonoidHom
  continuous_toFun := NNReal.continuous_sqrt.units_map.comp (leviCharacter F B).continuous

/-- Embed the canonical positive half into complex units. -/
def leviHalfCharacter : FullLevi F B →ₜ* ℂˣ where
  toMonoidHom := Jacquet.complexCharacter (leviPositiveHalf F B).toMonoidHom
  continuous_toFun :=
    (Complex.continuous_ofReal.comp NNReal.continuous_coe).units_map.comp
      (leviPositiveHalf F B).continuous

@[simp]
theorem leviPositiveHalf_sq (m : FullLevi F B) :
    leviPositiveHalf F B m ^ 2 = leviCharacter F B m :=
  Jacquet.positiveHalfCharacter_sq _ m

@[simp]
theorem coe_leviHalfCharacter (m : FullLevi F B) :
    (leviHalfCharacter F B m : ℂ) =
      ((NNReal.sqrt (leviCharacter F B m : ℝ≥0) : ℝ) : ℂ) := rfl

theorem leviHalfCharacter_sq (m : FullLevi F B) :
    leviHalfCharacter F B m ^ 2 =
      Jacquet.complexCharacter (leviCharacter F B).toMonoidHom m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, coe_leviHalfCharacter, Jacquet.complexCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

/-- The positive complex half on the actual adelic parabolic. -/
def parabolicHalfCharacter : Full F B →ₜ* ℂˣ :=
  (leviHalfCharacter F B).comp (B.leviProjectionContinuous (Adeles F))

@[simp]
theorem parabolicHalfCharacter_section (m : FullLevi F B) :
    parabolicHalfCharacter F B (B.leviInParabolic (Adeles F) m) =
      leviHalfCharacter F B m := by
  change leviHalfCharacter F B (B.leviProjection (Adeles F) (B.leviInParabolic (Adeles F) m)) = _
  rw [B.leviProjection_section]

@[simp]
theorem leviHalfCharacter_eq_one (m : FullLevi F B) :
    leviHalfCharacter F B m = 1 ↔ leviCharacter F B m = 1 := by
  change Jacquet.complexCharacter
    (Jacquet.positiveHalfCharacter (leviCharacter F B).toMonoidHom) m = 1 ↔
      (leviCharacter F B).toMonoidHom m = 1
  simpa only [Jacquet.inverseHalfCharacter, MonoidHom.inv_apply, inv_eq_one] using
      Jacquet.inverseHalfCharacter_eq_one (leviCharacter F B).toMonoidHom m

@[simp]
theorem leviHalfCharacter_rational (m : B.Levi F) :
    leviHalfCharacter F B (rationalLevi F B m) = 1 := by
  rw [leviHalfCharacter_eq_one, leviCharacter_rational]

@[simp]
theorem leviHalfCharacter_scalar (a : Ideles F) :
    leviHalfCharacter F B (fun i => AdelicGL.scalar F (B.size i) a) = 1 := by
  rw [leviHalfCharacter_eq_one, leviCharacter_scalar]

theorem parabolicHalfCharacter_sq (g : Full F B) :
    parabolicHalfCharacter F B g ^ 2 =
      Jacquet.complexCharacter (parabolicCharacter F B).toMonoidHom g :=
  leviHalfCharacter_sq F B (B.leviProjection (Adeles F) g)

@[simp]
theorem parabolicHalfCharacter_unipotent (u : B.unipotentRadical (Adeles F)) :
    parabolicHalfCharacter F B u = 1 := by
  change leviHalfCharacter F B (B.leviProjection (Adeles F) u.val) = 1
  rw [u.property, map_one]

@[simp]
theorem parabolicHalfCharacter_rational (g : Rational F B) :
    parabolicHalfCharacter F B (AdelicBlockParabolic.rational F B g) = 1 := by
  change leviHalfCharacter F B (B.leviProjection (Adeles F)
    (AdelicBlockParabolic.rational F B g)) = 1
  rw [leviProjection_rational, leviHalfCharacter_eq_one, leviCharacter_rational]

end Langlands.Global.AdelicBlockDeterminantCharacter
