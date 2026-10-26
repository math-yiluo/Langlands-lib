import Langlands.Representation.Classification.SegmentConstituentCompatibilityStatement
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# The scalar action on segment inductions and their constituents

Ambient scalar matrices lie in every standard block Levi as constant block
scalars, the explicit block modulus is trivial on them, and normalized
parabolic induction acts on them through the inducing Levi representation.
The scalar characters of block factors multiply in their tensor product. For
the segment factors `ν^i A` the determinant powers add up to the exponent
`m (m - 1) / 2`, for both orders of the factors. Constituents inherit the
scalar character through their actual injective or surjective intertwiners.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands

universe uF uV

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (R : Type*) [CommRing R]

/-- Ambient scalars as the constant block scalars of the actual Levi. -/
def scalarLevi : Rˣ →* B.Levi R :=
  (B.blockScalarLevi R).comp (Pi.constMonoidHom _ _)

@[simp]
theorem scalarLevi_apply (a : Rˣ) (i : Fin B.length) :
    B.scalarLevi R a i = GeneralLinear.scalar a := rfl

/-- The constant block scalar `a` is the ambient scalar matrix `a`. -/
theorem leviEmbedding_scalarLevi (a : Rˣ) :
    B.leviEmbedding R (B.scalarLevi R a) = GeneralLinear.scalar a := by
  apply Units.ext
  change (B.blockScalar R (fun _ => a) : Matrix (Fin n) (Fin n) R) = _
  rw [B.coe_blockScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- Ambient scalars in the standard upper block parabolic. -/
def scalarParabolic : Rˣ →* B.parabolic R :=
  (B.leviInParabolic R).comp (B.scalarLevi R)

@[simp]
theorem coe_scalarParabolic (a : Rˣ) :
    ((B.scalarParabolic R a : B.parabolic R) : GeneralLinear n R) =
      GeneralLinear.scalar a :=
  B.leviEmbedding_scalarLevi R a

@[simp]
theorem leviProjection_scalarParabolic (a : Rˣ) :
    B.leviProjection R (B.scalarParabolic R a) = B.scalarLevi R a :=
  B.leviProjection_section R _

variable {B R}
variable {V : Fin B.length → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- If each block factor has scalar character `c i`, the block tensor product has
the product character on the constant block scalars. -/
theorem hasScalarCharacter_blockTensor
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) R) (V i)}
    {c : Fin B.length → (Rˣ →* ℂˣ)}
    (h : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (c i)) :
    Classification.HasScalarCharacter (B.blockTensor σ) (B.scalarLevi R) (∏ i, c i) := by
  intro a v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have hf : (fun i => σ i (B.scalarLevi R a i) (f i)) = fun i => (c i a : ℂ) • f i :=
      funext fun i => h i a (f i)
    rw [map_smul, B.blockTensor_tprod, hf, MultilinearMap.map_smul_univ, smul_comm r,
      MonoidHom.finsetProd_apply, Units.coe_prod]
  | add x y hx hy =>
    rw [map_add, hx, hy, smul_add]

end GeneralLinear.BlockShape

namespace Classification

/-- Twisting by a character `χ` multiplies the scalar character by `χ` on scalars. -/
theorem hasScalarCharacter_twist {n : ℕ} {R : Type*} [CommRing R] {V : Type*}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GeneralLinear n R) V}
    {ω : Rˣ →* ℂˣ} (χ : GeneralLinear n R →* ℂˣ)
    (h : HasScalarCharacter ρ GeneralLinear.scalar ω) :
    HasScalarCharacter (twist χ ρ) GeneralLinear.scalar (ω * χ.comp GeneralLinear.scalar) := by
  intro a v
  change (χ (GeneralLinear.scalar a) : ℂ) • ρ (GeneralLinear.scalar a) v = _
  rw [h a v, smul_smul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, mul_comm]

/-- The sum `0 + 1 + ⋯ + (m - 1) = m (m - 1) / 2`, in the real numbers. -/
theorem sum_fin_val_real (m : ℕ) :
    ∑ i : Fin m, ((i : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    push_cast
    ring

/-- The decreasing sum `(m - 1) + ⋯ + 1 + 0 = m (m - 1) / 2`, in the real numbers. -/
theorem sum_fin_rev_val_real (m : ℕ) :
    ∑ i : Fin m, ((m - 1 - (i : ℕ) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [← sum_fin_val_real m, ← Equiv.sum_comp Fin.revPerm (fun i : Fin m => ((i : ℕ) : ℝ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.revPerm_apply, Fin.val_rev]
  congr 1
  omega

end Classification

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Modulus

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The positive half modulus is trivial on ambient scalar matrices. -/
theorem leviHalfModulus_scalarLevi (a : F.Carrierˣ) :
    T.leviHalfModulus B (B.scalarLevi F.Carrier a) = 1 :=
  (T.leviHalfModulus_eq_one B _).mpr (T.leviModulus_scalar B a)

/-- The inflated positive half modulus is trivial on ambient scalar matrices. -/
theorem parabolicHalfModulus_scalarParabolic (a : F.Carrierˣ) :
    T.parabolicHalfModulus B (B.scalarParabolic F.Carrier a) = 1 := by
  rw [parabolicHalfModulus_apply, B.leviProjection_scalarParabolic]
  exact T.leviHalfModulus_scalarLevi B a

end Modulus

section Induced

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- A scalar character of the inducing Levi representation on the constant block
scalars is the scalar character of its normalized parabolic induction. -/
theorem hasScalarCharacter_normalizedParabolicInduced {V : Type uV} [AddCommGroup V]
    [Module ℂ V] {σ : Representation ℂ (B.Levi F.Carrier) V} {ω : F.Carrierˣ →* ℂˣ}
    (h : Classification.HasScalarCharacter σ (B.scalarLevi F.Carrier) ω) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Classification.HasScalarCharacter (T.normalizedParabolicInduced B σ)
      GeneralLinear.scalar ω := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro a f
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : x * GeneralLinear.scalar a =
      ((B.scalarParabolic F.Carrier a : B.parabolic F.Carrier) : GeneralLinear n F.Carrier) *
        x := by
    rw [B.coe_scalarParabolic]
    exact (Matrix.GeneralLinearGroup.scalar_commute a x).symm
  change Induction.eval (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) f
      (x * GeneralLinear.scalar a) =
    (ω a : ℂ) • Induction.eval (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) f x
  rw [hx, T.normalizedParabolicInduced_covariant B σ f, B.leviProjection_scalarParabolic,
    show T.leviModulus B (B.scalarLevi F.Carrier a) = 1 from T.leviModulus_scalar B a,
    Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one, one_smul]
  exact h a _

/-- If each block factor `σ i` has scalar character `c i`, then
`i(σ_1, …, σ_r)` has scalar character `∏ i, c i`. -/
theorem hasScalarCharacter_normalizedProductInduced {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)}
    {c : Fin B.length → (F.Carrierˣ →* ℂˣ)}
    (h : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (c i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Classification.HasScalarCharacter (T.normalizedProductInduced B σ)
      GeneralLinear.scalar (∏ i, c i) :=
  T.hasScalarCharacter_normalizedParabolicInduced B
    (GeneralLinear.BlockShape.hasScalarCharacter_blockTensor h)

end Induced

section Segment

/-- On the scalar matrix `a`, `|det|^s` on `GL_k` is `|a|^(k s)`. -/
theorem coe_determinantPowerCharacter_scalar (k : ℕ) (s : ℝ) (a : F.Carrierˣ) :
    (T.determinantPowerCharacter k s (GeneralLinear.scalar a) : ℂ) =
      (((T.normalizedAbsUnits a : ℝ≥0) : ℝ) ^ ((k : ℝ) * s) : ℝ) := by
  rw [coe_realPowerCharacter, T.determinantNorm_scalar, Units.val_pow_eq_pow_val,
    NNReal.coe_pow, ← Real.rpow_natCast, ← Real.rpow_mul (T.normalizedAbsUnits a : ℝ≥0).coe_nonneg]

/-- Multiplying the characters `ω ⊗ ν^(e i)` on scalars, for exponents summing to
`m (m - 1) / 2`, gives `ω^m ⊗ ν^((m - 1) / 2)` on `GL_{mr}`. -/
theorem prod_twistedScalarCharacter (ω : F.Carrierˣ →* ℂˣ) (r m : ℕ) (e : Fin m → ℝ)
    (he : ∑ i, e i = (m : ℝ) * ((m : ℝ) - 1) / 2) :
    ∏ i : Fin m, (ω * (T.determinantPowerCharacter r (e i)).comp GeneralLinear.scalar) =
      ω ^ m * (T.determinantPowerCharacter (m * r) (((m : ℝ) - 1) / 2)).comp
        GeneralLinear.scalar := by
  ext a
  have hpos : (0 : ℝ) < ((T.normalizedAbsUnits a : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (T.normalizedAbsUnits a).ne_zero)
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, MonoidHom.mul_apply, Units.val_mul,
    MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.comp_apply,
    coe_determinantPowerCharacter_scalar]
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply,
    coe_determinantPowerCharacter_scalar]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.ofReal_prod, ← Real.rpow_sum_of_pos hpos, ← Finset.mul_sum, he]
  congr 3
  push_cast
  ring

variable {r : ℕ}

/-- `ν^s A` has scalar character `ω ⊗ ν^s` when `A` has scalar character `ω`. -/
theorem hasScalarCharacter_segmentFactor
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (s : ℝ) {ω : F.Carrierˣ →* ℂˣ}
    (h : letI := T.topology
      Classification.HasScalarCharacter A.representation GeneralLinear.scalar ω) :
    letI := T.topology
    Classification.HasScalarCharacter (T.segmentFactor A s).representation
      GeneralLinear.scalar (ω * (T.determinantPowerCharacter r s).comp GeneralLinear.scalar) :=
  Classification.hasScalarCharacter_twist _ h

/-- `i(A, νA, …, ν^(m-1) A)` has scalar character `ω^m ⊗ ν^((m - 1) / 2)` on
`GL_{mr}` when `A` has scalar character `ω`. -/
theorem hasScalarCharacter_segmentInduced
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r)
    {ω : F.Carrierˣ →* ℂˣ}
    (h : letI := T.topology
      Classification.HasScalarCharacter A.representation GeneralLinear.scalar ω) :
    letI := T.topology
    Classification.HasScalarCharacter (T.segmentInduced A m hr).representation
      GeneralLinear.scalar
      (ω ^ m * (T.determinantPowerCharacter (m * r) (((m : ℝ) - 1) / 2)).comp
        GeneralLinear.scalar) := by
  rw [segmentInduced_representation,
    ← T.prod_twistedScalarCharacter ω r m _ (Classification.sum_fin_val_real m)]
  exact T.hasScalarCharacter_normalizedProductInduced _
    fun i => T.hasScalarCharacter_segmentFactor A _ h

/-- `i(ν^(m-1) A, …, νA, A)` has the same scalar character
`ω^m ⊗ ν^((m - 1) / 2)` on `GL_{mr}`. -/
theorem hasScalarCharacter_segmentInducedDown
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r)
    {ω : F.Carrierˣ →* ℂˣ}
    (h : letI := T.topology
      Classification.HasScalarCharacter A.representation GeneralLinear.scalar ω) :
    letI := T.topology
    Classification.HasScalarCharacter (T.segmentInducedDown A m hr).representation
      GeneralLinear.scalar
      (ω ^ m * (T.determinantPowerCharacter (m * r) (((m : ℝ) - 1) / 2)).comp
        GeneralLinear.scalar) := by
  rw [segmentInducedDown_representation,
    ← T.prod_twistedScalarCharacter ω r m _ (Classification.sum_fin_rev_val_real m)]
  exact T.hasScalarCharacter_normalizedProductInduced _
    fun i => T.hasScalarCharacter_segmentFactor A _ h

end Segment

end PadicField.TopologicalData

namespace Classification

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The scalar action on both segment inductions and on every irreducible
subrepresentation or quotient of the increasing one. -/
theorem segmentConstituentCentralCharacter :
    SegmentConstituentCentralCharacter.{uF, uV} F T := by
  intro Δ ω A hA hω
  have hup := T.hasScalarCharacter_segmentInduced A.obj Δ.length Δ.rank_pos hω
  refine ⟨hup, T.hasScalarCharacter_segmentInducedDown A.obj Δ.length Δ.rank_pos hω, ?_⟩
  rintro π (hπ | hπ)
  · obtain ⟨-, j, hj⟩ := (T.isSegmentSubrepresentation_iff Δ π A hA).mp hπ
    exact hup.of_injective j hj
  · obtain ⟨-, q, hq⟩ := (T.isSegmentQuotient_iff Δ π A hA).mp hπ
    exact hup.of_surjective q hq

end Classification

end Langlands
