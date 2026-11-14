import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped TensorProduct
open scoped NNReal
open CategoryTheory
open Topology
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility leftCharacter_radical leftCoefficientRadicalProjection leftCoefficientRadicalProjection_surjective leftPhiExpected leftPhiProduct leftPsiCoefficient leftPsiCoefficientEquiv leftPsiCoefficientEquiv_mk_tmul leftPsiCoefficientEquiv_natural leftPsiCoefficientEquiv_section_action leftPsiCoefficientMap leftPsiCoefficientOrdinaryEquiv leftPsiCoefficient_isSmooth leftPsiCoefficient_radical_tmul leftPsiInductionEquiv leftPsiInductionEquiv_natural leftPsiNormalizedCoefficient leftPsiNormalizedCoefficientMap leftPsiNormalizedCoefficient_action leftPsiSection_character leftPsiSection_determinantNorm leftPsiSection_halfModulus leftPsiZeroCoefficientEquiv leftPsiZeroCoefficient_isSmooth leftPsiZeroEquiv leftPsiZeroEquiv_natural leftPsiZeroTensorEquiv leftPsiZeroTensorEquiv_natural leftPsi_mirabolic_compactOpenBasis leftPsi_normalSplitEquiv leftPsi_normalSplitEquiv_natural psiMinusOrdinaryEquiv psiMinusOrdinaryEquiv_natural rightPhiProduct rightPhiQuotient rightPhiSubobject
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
universe u

section GroupData
variable {R : Type u} [CommRing R] {k r : ℕ}

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftIndex_first (i : Fin k) :
    leftIndex k r (Sum.inl i) =
      (finSumFinEquiv (Sum.inl i) : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftIndex_second (i : Fin r) :
    leftIndex k r (Sum.inr i.castSucc) =
      (finSumFinEquiv (Sum.inr i) : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

end GroupData
section TensorCoinvariants
universe uN uM uV uW

variable {N : Type uN} {M : Type uM} [Group N] [Group M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (f : N →* M) (hf : Function.Surjective f)
variable (σ : Representation ℂ N (V ⊗[ℂ] W)) (τ : Representation ℂ M W)
variable (hσ : ∀ (n : N) (v : V) (w : W), σ n (v ⊗ₜ w) = v ⊗ₜ τ (f n) w)

end TensorCoinvariants
section LeftCoefficient
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPsi_det_lastRow {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)
    (hA : ∀ j, A (Fin.last n) j = if j = Fin.last n then 1 else 0) :
    Matrix.det A = Matrix.det (A.submatrix Fin.castSucc Fin.castSucc) := by
  rw [Matrix.det_succ_row A (Fin.last n)]
  simp only [hA, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [Fin.succAbove_last, ← two_mul, pow_mul]

/-- The elementary last-row determinant calculation, kept local to this proof. -/
private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPsi_determinantNorm_projection {n : ℕ} (g : mirabolic n F.Carrier) :
    T.determinantNorm (n + 1) g.val = T.determinantNorm n (projection g) := by
  have hd : GeneralLinear.determinant g.val = GeneralLinear.determinant (projection g) :=
    Units.ext (leftPsi_det_lastRow g.val.val g.property)
  exact congrArg T.normalizedAbsUnits hd

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPsi_determinantNorm_radical {n : ℕ} (v : radical n F.Carrier) :
    T.determinantNorm (n + 1) v.val.val = 1 := by
  rw [leftPsi_determinantNorm_projection, (projection_eq_one_iff v.val).mpr v.property,
    map_one]

/-- Restrict the actual left normalizing character to the ambient radical. -/
theorem leftCharacter_radical {k r : ℕ} (v : radical (k + r) F.Carrier) :
    letI := T.topology
    (T.leftCharacter k r).toMonoidHom ⟨v.val, radical_le_leftSubgroup v.property⟩ = 1 := by
  apply Units.ext
  rw [T.leftCharacter_apply, T.leftLeviCharacter_apply, leftProjection_radical_gl,
    map_one, leftPsi_determinantNorm_radical T
      ⟨_, leftProjection_radical_mem v⟩]
  simp

/-- The determinant norm on the section splits into the actual two block norms. -/
theorem leftPsiSection_determinantNorm {k r : ℕ}
    (g : (leftSubgroup k r F.Carrier).comap (levi (n := k + r))) :
    T.determinantNorm (k + r) g.val =
      T.determinantNorm k (leftProjection ((levi (n := k + r)).subgroupComap
        (leftSubgroup k r F.Carrier) g)).1 *
      T.determinantNorm r (projection (leftProjection ((levi (n := k + r)).subgroupComap
        (leftSubgroup k r F.Carrier) g)).2) := by
  change T.normalizedAbsUnits _ = T.normalizedAbsUnits _ * T.normalizedAbsUnits _
  rw [leftPsiSection_determinant, map_mul]

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPsi_scalar_normalization (x y : ℝ≥0ˣ) (k r : ℕ) :
    (((((x * y : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((x : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
          ((((y : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) =
      ((((x : ℝ≥0) : ℝ) ^ ((r : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) *
          ((((y : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt y)
  have ha : ((x : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) *
      ((x : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) =
        ((x : ℝ≥0) : ℝ) ^ ((r : ℝ) / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  simp only [Units.val_mul, NNReal.coe_mul, Real.mul_rpow hx.le hy.le,
    Complex.ofReal_mul]
  calc
    _ = ((((x : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) * ((x : ℝ≥0) : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
          push_cast
          ring
    _ = _ := by rw [ha]

/-- Inverse-half normalization removes one half power from the first block
and retains the inverse-half character of the source Psi quotient. -/
theorem leftPsiSection_character {k r : ℕ}
    (g : (leftSubgroup k r F.Carrier).comap (levi (n := k + r))) :
    letI := T.topology
    let h := (levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g
    (Mirabolic.psiMinusCharacter T (k + r) g.val : ℂ) *
        ((T.leftCharacter k r).toMonoidHom h : ℂ) =
      ((((T.determinantNorm k (leftProjection h).1 : ℝ≥0) : ℝ) ^
          ((r : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm r (projection (leftProjection h).2) : ℝ≥0) : ℝ) ^
          (-((k : ℝ) / 2)) : ℝ) : ℂ) *
        (Mirabolic.psiMinusCharacter T r (projection (leftProjection h).2) : ℂ) := by
  let := T.topology
  dsimp only
  rw [T.leftCharacter_apply, T.leftLeviCharacter_apply,
    leftPsi_determinantNorm_projection T]
  simp only [Mirabolic.psiMinusCharacter, coe_realPowerCharacter,
    leftPsiSection_determinantNorm T]
  simpa only [mul_assoc] using leftPsi_scalar_normalization
    (T.determinantNorm k (leftProjection ((levi (n := k + r)).subgroupComap
      (leftSubgroup k r F.Carrier) g)).1)
    (T.determinantNorm r (projection (leftProjection ((levi (n := k + r)).subgroupComap
      (leftSubgroup k r F.Carrier) g)).2)) k r

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.leftPsi_sqrt_div_pow (x y : ℝ≥0ˣ) (a b : ℕ) :
    ((NNReal.sqrt ((x ^ a / y ^ b : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) =
      ((((x : ℝ≥0) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) *
        ((((y : ℝ≥0) : ℝ) ^ (-((b : ℝ) / 2)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt y)
  rw [Real.coe_sqrt, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow,
    Real.sqrt_eq_rpow, Real.div_rpow (pow_nonneg hx.le _) (pow_nonneg hy.le _),
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le,
    div_eq_mul_inv _ (((y : ℝ≥0) : ℝ) ^ ((b : ℝ) * (1 / 2))), ← Real.rpow_neg hy.le]
  congr 1 <;> congr 1 <;> ring

/-- The binary half modulus uses these same two determinant norms. -/
theorem leftPsiSection_halfModulus {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (g : (leftSubgroup k r F.Carrier).comap (levi (n := k + r))) :
    letI := T.topology
    let q : (BlockShape.binary k r hk hr).parabolic F.Carrier :=
      ⟨g.val, (leftSubgroup_comap_levi_binary hk hr).le g.property⟩
    let h := (levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g
    (T.parabolicHalfModulus (BlockShape.binary k r hk hr) q : ℂ) =
      ((((T.determinantNorm k (leftProjection h).1 : ℝ≥0) : ℝ) ^
          ((r : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm r (projection (leftProjection h).2) : ℝ≥0) : ℝ) ^
          (-((k : ℝ) / 2)) : ℝ) : ℂ) := by
  let := T.topology
  dsimp only
  have hm (m : (BlockShape.binary k r hk hr).Levi F.Carrier) :
      T.leviModulus (BlockShape.binary k r hk hr) m =
        T.determinantNorm k (m (0 : Fin 2)) ^ r /
          T.determinantNorm r (m (1 : Fin 2)) ^ k := by
    rw [T.leviModulus_apply]
    change (∏ i : Fin 2, ∏ j ∈ Finset.univ.filter (fun j : Fin 2 => i < j),
      T.determinantNorm ((BlockShape.binary k r hk hr).size i) (m i) ^
        (BlockShape.binary k r hk hr).size j /
      T.determinantNorm ((BlockShape.binary k r hk hr).size j) (m j) ^
        (BlockShape.binary k r hk hr).size i) = _
    rw [Fin.prod_univ_two]
    have h0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
    have h1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
    rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]
    rfl
  rw [T.parabolicHalfModulus_apply, T.leviHalfModulus_apply, hm, leftPsi_sqrt_div_pow]
  have hp := (leftPsiSection_binary_projection hk hr g).trans
    (leftPsiSectionTwoBlock_projection g)
  have hp0 := congrArg Prod.fst hp
  have hp1 := congrArg Prod.snd hp
  dsimp only [Prod.fst, Prod.snd] at hp0 hp1
  exact congrArg₂
    (fun (a : GeneralLinear k F.Carrier) (b : GeneralLinear r F.Carrier) =>
      ((((T.determinantNorm k a : ℝ≥0) : ℝ) ^ ((r : ℝ) / 2) : ℝ) : ℂ) *
        ((((T.determinantNorm r b : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ))
    hp0 hp1

/-- The radical of the ambient group, viewed inside the actual inducing subgroup,
projects surjectively onto the source radical. -/
def leftCoefficientRadicalProjection {k r : ℕ} :
    (radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier) →*
      radical r F.Carrier :=
  leftRadicalProjection.comp (Subgroup.subgroupOfEquivOfLe radical_le_leftSubgroup).toMonoidHom

theorem leftCoefficientRadicalProjection_surjective {k r : ℕ} :
    Function.Surjective (leftCoefficientRadicalProjection (F := F) (k := k) (r := r)) :=
  leftRadicalProjection_surjective.comp
    (Subgroup.subgroupOfEquivOfLe radical_le_leftSubgroup).surjective

variable {k r : ℕ}
variable (X : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))

/-- The actual normalized left coefficient representation, before induction. -/
def leftPsiCoefficient : letI := T.topology
    Representation ℂ (leftSubgroup k r F.Carrier) (X.1 ⊗[ℂ] X.2) :=
  letI := T.topology
  twist (T.leftCharacter k r).toMonoidHom
    (leftInducingRepresentation X.1.representation X.2.representation)

/-- On translations the normalized coefficient acts only on its second factor. -/
theorem leftPsiCoefficient_radical_tmul :
    letI := T.topology
    ∀ (v : (radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))
      (x : X.1) (y : X.2),
      leftPsiCoefficient T X v.val (x ⊗ₜ[ℂ] y) =
        x ⊗ₜ[ℂ] X.2.representation (leftCoefficientRadicalProjection v).val y := by
  let := T.topology
  intro v x y
  have hv : v.val = ⟨v.val.val, radical_le_leftSubgroup v.property⟩ := rfl
  change ((T.leftCharacter k r).toMonoidHom v.val : ℂ) •
    (X.1.representation (leftProjection v.val).1 x ⊗ₜ[ℂ]
      X.2.representation (leftProjection v.val).2 y) = _
  rw [hv, leftCharacter_radical T ⟨v.val.val, v.property⟩,
    leftProjection_radical_gl ⟨v.val.val, v.property⟩]
  simp only [Units.val_one, one_smul, map_one, Module.End.one_apply]
  rfl

/-- The full normalized coefficient coinvariants are the full first carrier tensored
with the source's ordinary coinvariants. -/
def leftPsiCoefficientOrdinaryEquiv : letI := T.topology
    Representation.Coinvariants ((leftPsiCoefficient T X).comp
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)).subtype) ≃ₗ[ℂ]
      X.1 ⊗[ℂ] Representation.Coinvariants
        (X.2.representation.comp (radical r F.Carrier).subtype) :=
  letI := T.topology
  tensorCoinvariantsEquiv leftCoefficientRadicalProjection
    leftCoefficientRadicalProjection_surjective _ _ (leftPsiCoefficient_radical_tmul T X)

/-- Identify the coefficient quotient with the actual Psi-minus carrier of the
second input. Its inverse-half normalization changes the action, not this carrier. -/
def leftPsiCoefficientEquiv : letI := T.topology
    Representation.Coinvariants ((leftPsiCoefficient T X).comp
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)).subtype) ≃ₗ[ℂ]
      X.1 ⊗[ℂ] (Mirabolic.psiMinus T r).obj X.2 :=
  letI := T.topology
  (leftPsiCoefficientOrdinaryEquiv T X).trans
    (TensorProduct.congr (LinearEquiv.refl ℂ X.1)
      (Jacquet.Localization.trivialEquiv X.2.representation (radical r F.Carrier)
        (leviSubgroup r F.Carrier) leviSubgroup_le_normalizer).toLinearEquiv.symm)

@[simp] theorem leftPsiCoefficientEquiv_mk_tmul :
    letI := T.topology
    ∀ (x : X.1) (y : X.2),
      leftPsiCoefficientEquiv T X (Representation.Coinvariants.mk _ (x ⊗ₜ y)) =
        x ⊗ₜ Mirabolic.psiMinusQuotient T r X.2 y := by
  intros
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The section action on the coefficient quotient keeps precisely the original
left character and the unnormalized source Psi action. -/
theorem leftPsiCoefficientEquiv_section_action :
    letI := T.topology
    ∀ (g : (leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
      (z : Representation.Coinvariants ((leftPsiCoefficient T X).comp
        ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)).subtype)),
      leftPsiCoefficientEquiv T X
          ((leftPsiCoefficient T X).toCoinvariants
            ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))
            ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g) z) =
        ((T.leftCharacter k r).toMonoidHom
          ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g) : ℂ) •
          TensorProduct.map
            (X.1.representation
              (leftProjection ((levi (n := k + r)).subgroupComap
                (leftSubgroup k r F.Carrier) g)).1)
            (((Mirabolic.psiMinusUnnormalized T r).obj X.2).representation
              (projection (leftProjection ((levi (n := k + r)).subgroupComap
                (leftSubgroup k r F.Carrier) g)).2))
            (leftPsiCoefficientEquiv T X z) := by
  let := T.topology
  intro g z
  let h := (levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g
  let σ := (leftPsiCoefficient T X).comp
    ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)).subtype
  let e := leftPsiCoefficientEquiv T X
  let c : ℂ := (T.leftCharacter k r).toMonoidHom h
  let A := X.1.representation (leftProjection h).1
  let B : (Mirabolic.psiMinus T r).obj X.2 →ₗ[ℂ]
      (Mirabolic.psiMinus T r).obj X.2 :=
    ((Mirabolic.psiMinusUnnormalized T r).obj X.2).representation
      (projection (leftProjection h).2)
  let L := e.toLinearMap.comp
    ((leftPsiCoefficient T X).toCoinvariants
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)) h)
  let R := c • (TensorProduct.map A B).comp e.toLinearMap
  have heq : L = R := by
    apply Representation.Coinvariants.hom_ext
    apply TensorProduct.ext'
    intro x y
    change e (Representation.Coinvariants.mk σ
        (c • (A x ⊗ₜ[ℂ] X.2.representation (leftProjection h).2 y))) =
      c • TensorProduct.map A B (e (Representation.Coinvariants.mk σ (x ⊗ₜ[ℂ] y)))
    have hs (v : X.1 ⊗[ℂ] X.2) :
        e (Representation.Coinvariants.mk σ (c • v)) =
          c • e (Representation.Coinvariants.mk σ v) :=
      (congrArg e ((Representation.Coinvariants.mk σ).map_smul c v)).trans
        (e.map_smul c (Representation.Coinvariants.mk σ v))
    have ht : B (Mirabolic.psiMinusQuotient T r X.2 y) =
        Mirabolic.psiMinusQuotient T r X.2 (X.2.representation (leftProjection h).2 y) := by
      change Mirabolic.psiMinusQuotient T r X.2
          (X.2.representation (levi (projection (leftProjection h).2)) y) = _
      exact congrArg (fun q => Mirabolic.psiMinusQuotient T r X.2
        (X.2.representation q y)) (leftProjection_levi_second g).symm
    calc
      _ = c • (A x ⊗ₜ[ℂ] Mirabolic.psiMinusQuotient T r X.2
          (X.2.representation (leftProjection h).2 y)) :=
        (hs _).trans (congrArg (fun v => c • v)
          (leftPsiCoefficientEquiv_mk_tmul T X (A x)
            (X.2.representation (leftProjection h).2 y)))
      _ = c • (A x ⊗ₜ[ℂ] B (Mirabolic.psiMinusQuotient T r X.2 y)) :=
        congrArg (fun v => c • (A x ⊗ₜ[ℂ] v)) ht.symm
      _ = c • TensorProduct.map A B (e (Representation.Coinvariants.mk σ (x ⊗ₜ[ℂ] y))) :=
        congrArg (fun v => c • v)
          ((TensorProduct.map_tmul A B x (Mirabolic.psiMinusQuotient T r X.2 y)).symm.trans
            (congrArg (TensorProduct.map A B) (leftPsiCoefficientEquiv_mk_tmul T X x y).symm))
  exact LinearMap.congr_fun heq z

/-- The section coefficient after the ambient inverse-half normalization. -/
def leftPsiNormalizedCoefficient : letI := T.topology
    Representation ℂ ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
      (Representation.Coinvariants ((leftPsiCoefficient T X).comp
        ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)).subtype)) :=
  letI := T.topology
  twist ((Mirabolic.psiMinusCharacter T (k + r)).comp
    ((leftSubgroup k r F.Carrier).comap (levi (n := k + r))).subtype)
    (((leftPsiCoefficient T X).toCoinvariants
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))).comp
      ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier)))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- After normalization the coefficient is the normalized binary tensor action.
This formula includes a zero source GL rank and retains its entire carrier. -/
theorem leftPsiNormalizedCoefficient_action :
    letI := T.topology
    ∀ (g : (leftSubgroup k r F.Carrier).comap (levi (n := k + r))) (z),
      let h := (levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g
      leftPsiCoefficientEquiv T X (leftPsiNormalizedCoefficient T X g z) =
        (((((T.determinantNorm k (leftProjection h).1 : ℝ≥0) : ℝ) ^
            ((r : ℝ) / 2) : ℝ) : ℂ) *
          ((((T.determinantNorm r (projection (leftProjection h).2) : ℝ≥0) : ℝ) ^
            (-((k : ℝ) / 2)) : ℝ) : ℂ)) •
          TensorProduct.map
            (X.1.representation (leftProjection h).1)
            (((Mirabolic.psiMinus T r).obj X.2).representation
              (projection (leftProjection h).2))
            (leftPsiCoefficientEquiv T X z) := by
  let := T.topology
  intro g z
  dsimp only
  let h := (levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier) g
  let e := leftPsiCoefficientEquiv T X
  let a : ℂ := Mirabolic.psiMinusCharacter T (k + r) g.val
  let b : ℂ := (T.leftCharacter k r).toMonoidHom h
  let c : ℂ := Mirabolic.psiMinusCharacter T r (projection (leftProjection h).2)
  let d : ℂ :=
    ((((T.determinantNorm k (leftProjection h).1 : ℝ≥0) : ℝ) ^
      ((r : ℝ) / 2) : ℝ) : ℂ) *
    ((((T.determinantNorm r (projection (leftProjection h).2) : ℝ≥0) : ℝ) ^
      (-((k : ℝ) / 2)) : ℝ) : ℂ)
  let A := X.1.representation (leftProjection h).1
  let B : (Mirabolic.psiMinus T r).obj X.2 →ₗ[ℂ]
      (Mirabolic.psiMinus T r).obj X.2 :=
    ((Mirabolic.psiMinusUnnormalized T r).obj X.2).representation
      (projection (leftProjection h).2)
  have hn : ((Mirabolic.psiMinus T r).obj X.2).representation
      (projection (leftProjection h).2) = c • B := by
    apply LinearMap.ext
    intro w
    exact Mirabolic.psiMinus_action_eq_smul T r X.2 _ w
  have hc : a * b = d * c := leftPsiSection_character T g
  have hs := leftPsiCoefficientEquiv_section_action T X g z
  change e (a • ((leftPsiCoefficient T X).toCoinvariants
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier)) h z)) =
    d • TensorProduct.map A _ (e z)
  calc
    _ = a • e (((leftPsiCoefficient T X).toCoinvariants
        ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))) h z) :=
      e.map_smul a _
    _ = a • (b • TensorProduct.map A B (e z)) := congrArg (fun w => a • w) hs
    _ = (d * c) • TensorProduct.map A B (e z) := by rw [smul_smul, hc]
    _ = d • (c • TensorProduct.map A B (e z)) :=
      (smul_smul d c (TensorProduct.map A B (e z))).symm
    _ = d • TensorProduct.map A (c • B) (e z) :=
      congrArg (fun w => d • w)
        (LinearMap.congr_fun (TensorProduct.map_smul_right c A B) (e z)).symm
    _ = _ := congrArg (fun B' => d • TensorProduct.map A B' (e z)) hn.symm

variable {Y : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}

/-- The inducing coefficient map of a pair of input morphisms. -/
def leftPsiCoefficientMap (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    (leftPsiCoefficient T X).IntertwiningMap (leftPsiCoefficient T Y) :=
  letI := T.topology
  twistIntertwining (T.leftCharacter k r).toMonoidHom
    (MixedProductTensor.pullbackMap leftProjection
      (MixedProductTensor.externalMap (SmoothRep.hom f.1) (SmoothRep.hom f.2)))

/-- The same quotient-induced map after restriction and normalization. -/
def leftPsiNormalizedCoefficientMap (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    (leftPsiNormalizedCoefficient T X).IntertwiningMap (leftPsiNormalizedCoefficient T Y) :=
  letI := T.topology
  twistIntertwining _ (Induction.restrictAlongMap
    ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier))
    (Induction.normalCoinvariantsMap
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))
      (leftPsiCoefficientMap T X f)))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The coefficient identification is natural in both original representation inputs. -/
theorem leftPsiCoefficientEquiv_natural
    (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    ∀ z, leftPsiCoefficientEquiv T Y (leftPsiNormalizedCoefficientMap T X f z) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap
        (SmoothRep.hom ((Mirabolic.psiMinus T r).map f.2)).toLinearMap
        (leftPsiCoefficientEquiv T X z) := by
  let := T.topology
  intro z
  let L := (leftPsiCoefficientEquiv T Y).toLinearMap.comp
    (leftPsiNormalizedCoefficientMap T X f).toLinearMap
  let R := (TensorProduct.map (SmoothRep.hom f.1).toLinearMap
    (SmoothRep.hom ((Mirabolic.psiMinus T r).map f.2)).toLinearMap).comp
    (leftPsiCoefficientEquiv T X).toLinearMap
  have heq : L = R := by
    apply Representation.Coinvariants.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  exact LinearMap.congr_fun heq z

end LeftCoefficient
section NormalSplitKernel
universe uG uL uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Equality transport for the kernel subgroup, kept at generic representation
types before specializing to the mixed-product function carrier. -/
private def _root_.Langlands.Derivative.MirabolicProductMinus.normalSplitCompactEquivOfKernel
    (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (r : G →* L) (s : L →* G) (hr : Continuous r) (hs : Continuous s)
    (hrs : ∀ l, r (s l) = l) (H N : Subgroup G) [N.Normal]
    (hN : r.ker = N) (hH : IsClosed (H : Set G)) (hclosed : IsClosed (N : Set G))
    (hker : N ≤ H) (σ : Representation ℂ H V) (hσ : IsSmooth σ) :
    Representation.Equiv (((Induction.compactInduced H σ).toCoinvariants N).comp s)
      (Induction.compactInduced (H.comap s)
        ((σ.toCoinvariants (N.subgroupOf H)).comp (s.subgroupComap H))) := by
  subst N
  exact Induction.normalSplitCompactEquiv hBasis r s hr hs hrs H hH hclosed hker σ hσ

variable
    (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (r : G →* L) (s : L →* G) (hr : Continuous r) (hs : Continuous s)
    (hrs : ∀ l, r (s l) = l) (H N : Subgroup G) [N.Normal]
    (hN : r.ker = N) (hH : IsClosed (H : Set G)) (hclosed : IsClosed (N : Set G))
    (hker : N ≤ H) (σ : Representation ℂ H V) (hσ : IsSmooth σ)

universe uW

private theorem _root_.Langlands.Derivative.MirabolicProductMinus.normalSplitCompactEquivOfKernel_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (hτ : IsSmooth τ) (t : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((Induction.compactInduced H σ).comp N.subtype)) :
    normalSplitCompactEquivOfKernel hBasis r s hr hs hrs H N hN hH hclosed hker τ hτ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (Induction.compactInducedMap H t) N) z) =
      Induction.compactInducedMap (H.comap s)
        (Induction.restrictAlongMap (s.subgroupComap H)
          (Induction.normalCoinvariantsMap (N.subgroupOf H) t))
        (normalSplitCompactEquivOfKernel hBasis r s hr hs hrs H N hN hH hclosed hker σ hσ z) := by
  subst N
  exact Induction.normalSplitCompactEquiv_natural
    hBasis r s hr hs hrs H hH hclosed hker σ hσ hτ t z

omit [T2Space G] in
/-- Character multiplication commutes with every induced coefficient map. -/
private theorem _root_.Langlands.Derivative.MirabolicProductMinus.compactInductionTwistEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (t : σ.IntertwiningMap τ)
    (χ : Induction.SmoothCharacter ℂ G) (z : Induction.CompactFunctions H σ) :
    Induction.compactInductionTwistEquiv H χ τ
        (Induction.compactInducedMap H t z) =
      Induction.compactInducedMap H
        (twistIntertwining (χ.toMonoidHom.comp H.subtype) t)
        (Induction.compactInductionTwistEquiv H χ σ z) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact (t.toLinearMap.map_smul (χ.toMonoidHom g : ℂ) _).symm

end NormalSplitKernel
section LeftInduction
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The actual unnormalized Psi quotient agrees with ordinary radical
coinvariants, with their action restricted along the actual GL Levi section. -/
def psiMinusOrdinaryEquiv (n : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) :
    letI := T.topology
    Representation.Equiv (((Mirabolic.psiMinusUnnormalized T n).obj A).representation)
      ((A.representation.toCoinvariants (radical n F.Carrier)).comp (levi (n := n))) := by
  let := T.topology
  refine
    { toLinearEquiv := (Jacquet.Localization.trivialEquiv A.representation
        (radical n F.Carrier) (leviSubgroup n F.Carrier)
        leviSubgroup_le_normalizer).toLinearEquiv
      isIntertwining' := ?_ }
  intro g
  exact (Jacquet.Localization.trivialEquiv A.representation
    (radical n F.Carrier) (leviSubgroup n F.Carrier)
    leviSubgroup_le_normalizer).isIntertwining' (leviEquiv g)

theorem psiMinusOrdinaryEquiv_natural (n : ℕ)
    {A B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
    (f : letI := T.topology; A ⟶ B) :
    letI := T.topology
    ∀ z : (Mirabolic.psiMinus T n).obj A,
      psiMinusOrdinaryEquiv T n B (SmoothRep.hom ((Mirabolic.psiMinus T n).map f) z) =
        Representation.Coinvariants.map _ _ (Jacquet.restrictMap (SmoothRep.hom f)
          (radical n F.Carrier)) (psiMinusOrdinaryEquiv T n A z) := by
  let := T.topology
  intro z
  exact congrArg (fun t => t z)
    (Jacquet.Localization.trivialEquiv_natural
      (radical n F.Carrier) (leviSubgroup n F.Carrier)
      leviSubgroup_le_normalizer (SmoothRep.hom f)).symm

/-- Closed mirabolic subgroups have the compact open basis needed by normal
coinvariant comparison, in the supplied field topology. -/
theorem leftPsi_mirabolic_compactOpenBasis (n : ℕ) :
    letI := T.topology
    ∀ O : Set (mirabolic n F.Carrier), IsOpen O → (1 : mirabolic n F.Carrier) ∈ O →
      ∃ K : OpenSubgroup (mirabolic n F.Carrier),
        IsCompact (K : Set (mirabolic n F.Carrier)) ∧ (K : Set (mirabolic n F.Carrier)) ⊆ O := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := Mirabolic.locallyCompactSpace (F := F.Carrier) (n := n)
  have : NonarchimedeanGroup (mirabolic n F.Carrier) := by
    constructor
    intro U hU
    rw [IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
    exact ⟨OpenSubgroup.comap (mirabolic n F.Carrier).subtype continuous_subtype_val L,
      fun x hx => hVU (hL hx)⟩
  intro O hO h1
  exact compactOpenSubgroupBasis (mirabolic n F.Carrier) O (hO.mem_nhds h1)

variable {k r : ℕ}
variable (X : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))

theorem leftPsiCoefficient_isSmooth :
    letI := T.topology
    IsSmooth (leftPsiCoefficient T X) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1)
  exact (isSmooth_twist_iff _ _ (T.leftCharacter k r).isOpen_ker).mpr
    (isSmooth_leftInducingRepresentation X.1.isSmooth X.2.isSmooth)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary radical coinvariants of the left mixed product, pulled back to
the actual GL section, are compact induction of the section coefficient quotient. -/
def leftPsi_normalSplitEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    Representation.Equiv
      ((((T.leftMixedProductFunctor k r).obj X).representation.toCoinvariants
        (radical (k + r) F.Carrier)).comp (levi (n := k + r)))
      (Induction.compactInduced
        ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
        (((leftPsiCoefficient T X).toCoinvariants
          ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))).comp
          ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier)))) := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1)
  let := T.generalLinearTopologicalGroup (k + r)
  exact
    (normalSplitCompactEquivOfKernel (leftPsi_mirabolic_compactOpenBasis T (k + r))
      (projection (n := k + r)) (levi (n := k + r))
      continuous_projection continuous_levi projection_levi
      (leftSubgroup k r F.Carrier) (radical (k + r) F.Carrier) ker_projection
      leftSubgroup_isClosed radical_isClosed radical_le_leftSubgroup
      (leftPsiCoefficient T X) (leftPsiCoefficient_isSmooth T X))

/-- The actual inverse-half normalized Psi of the left mixed product is
compact induction of its normalized section coefficient. -/
def leftPsiInductionEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    Representation.Equiv
      (((Mirabolic.psiMinus T (k + r)).obj
        ((T.leftMixedProductFunctor k r).obj X)).representation)
      (Induction.compactInduced
        ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
        (leftPsiNormalizedCoefficient T X)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r)
  let e := (psiMinusOrdinaryEquiv T (k + r)
    ((T.leftMixedProductFunctor k r).obj X)).trans (leftPsi_normalSplitEquiv T X)
  let χ : Induction.SmoothCharacter ℂ (GeneralLinear (k + r) F.Carrier) :=
    ⟨Mirabolic.psiMinusCharacter T (k + r), Mirabolic.isOpen_ker_psiMinusCharacter T (k + r)⟩
  exact (twistEquiv χ.toMonoidHom e).trans
    (Induction.compactInductionTwistEquiv
      ((leftSubgroup k r F.Carrier).comap (levi (n := k + r))) χ
      (((leftPsiCoefficient T X).toCoinvariants
        ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))).comp
        ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier))))

variable {Y : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)}

theorem leftPsi_normalSplitEquiv_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    ∀ z : Representation.Coinvariants
      (((T.leftMixedProductFunctor k r).obj X).representation.comp
        (radical (k + r) F.Carrier).subtype),
      leftPsi_normalSplitEquiv T Y
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (SmoothRep.hom ((T.leftMixedProductFunctor k r).map f))
            (radical (k + r) F.Carrier)) z) =
        Induction.compactInducedMap
          ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
          (Induction.restrictAlongMap
            ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier))
            (Induction.normalCoinvariantsMap
              ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))
              (leftPsiCoefficientMap T X f))) (leftPsi_normalSplitEquiv T X z) := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + r + 1)
  let := T.generalLinearTopologicalGroup (k + r)
  intro z
  exact normalSplitCompactEquivOfKernel_natural
    (leftPsi_mirabolic_compactOpenBasis T (k + r))
    (projection (n := k + r)) (levi (n := k + r))
    continuous_projection continuous_levi projection_levi
    (leftSubgroup k r F.Carrier) (radical (k + r) F.Carrier) ker_projection
    leftSubgroup_isClosed radical_isClosed radical_le_leftSubgroup
    (leftPsiCoefficient T X) (leftPsiCoefficient_isSmooth T X)
    (leftPsiCoefficient_isSmooth T Y) (leftPsiCoefficientMap T X f) z

set_option backward.isDefEq.respectTransparency.types false in
/-- The induction comparison is natural in both mixed-product inputs. -/
theorem leftPsiInductionEquiv_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r)
    ∀ z : (Mirabolic.psiMinus T (k + r)).obj ((T.leftMixedProductFunctor k r).obj X),
      leftPsiInductionEquiv T Y
        (SmoothRep.hom ((Mirabolic.psiMinus T (k + r)).map
          ((T.leftMixedProductFunctor k r).map f)) z) =
      Induction.compactInducedMap
        ((leftSubgroup k r F.Carrier).comap (levi (n := k + r)))
        (leftPsiNormalizedCoefficientMap T X f)
        (leftPsiInductionEquiv T X z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r)
  intro z
  let χ : Induction.SmoothCharacter ℂ (GeneralLinear (k + r) F.Carrier) :=
    ⟨Mirabolic.psiMinusCharacter T (k + r), Mirabolic.isOpen_ker_psiMinusCharacter T (k + r)⟩
  let σ := ((leftPsiCoefficient T X).toCoinvariants
    ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))).comp
    ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier))
  let τ := ((leftPsiCoefficient T Y).toCoinvariants
    ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))).comp
    ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier))
  let t := Induction.restrictAlongMap
    ((levi (n := k + r)).subgroupComap (leftSubgroup k r F.Carrier))
    (Induction.normalCoinvariantsMap
      ((radical (k + r) F.Carrier).subgroupOf (leftSubgroup k r F.Carrier))
      (leftPsiCoefficientMap T X f))
  have h₁ := psiMinusOrdinaryEquiv_natural T (k + r)
    ((T.leftMixedProductFunctor k r).map f) z
  have h₂ := leftPsi_normalSplitEquiv_natural T X f
    (psiMinusOrdinaryEquiv T (k + r) ((T.leftMixedProductFunctor k r).obj X) z)
  have h₃ := compactInductionTwistEquiv_natural
    ((leftSubgroup k r F.Carrier).comap (levi (n := k + r))) σ t χ
    (leftPsi_normalSplitEquiv T X
      (psiMinusOrdinaryEquiv T (k + r) ((T.leftMixedProductFunctor k r).obj X) z))
  exact (congrArg (fun q => Induction.compactInductionTwistEquiv
    ((leftSubgroup k r F.Carrier).comap (levi (n := k + r))) χ τ
      (leftPsi_normalSplitEquiv T Y q)) h₁).trans
    ((congrArg (Induction.compactInductionTwistEquiv
      ((leftSubgroup k r F.Carrier).comap (levi (n := k + r))) χ τ) h₂).trans h₃)

end LeftInduction
section LeftZero
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable {k : ℕ}
variable (X : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- At source rank one the quotient coefficient is the full tensor carrier
with the first-factor action; the entire actual GL-zero output is retained. -/
def leftPsiZeroCoefficientEquiv :
    letI := T.topology
    Representation.Equiv (leftPsiNormalizedCoefficient T X)
      ((BinaryTensor.rankZeroRight (b := 0) (R := F.Carrier) rfl X.1.representation
        ((Mirabolic.psiMinus T 0).obj X.2)).comp
          ((leftSubgroup k 0 F.Carrier).comap (levi (n := k + 0))).subtype) := by
  let := T.topology
  refine Representation.Equiv.mk (leftPsiCoefficientEquiv T X) ?_
  intro g
  apply LinearMap.ext
  intro z
  let e := leftPsiCoefficientEquiv T X
  let B := ((Mirabolic.psiMinus T 0).obj X.2).representation
  let A (a : GeneralLinear k F.Carrier) (b : GeneralLinear 0 F.Carrier) :=
    (((((T.determinantNorm k a : ℝ≥0) : ℝ) ^ (((0 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
      ((((T.determinantNorm 0 b : ℝ≥0) : ℝ) ^ (-((k : ℝ) / 2)) : ℝ) : ℂ)) •
      TensorProduct.map (X.1.representation a) (B b) (e z)
  have hg0 : projection (leftProjection (k := k) (r := 0) (R := F.Carrier)
      ((levi (n := k + 0)).subgroupComap (leftSubgroup k 0 F.Carrier) g)).2 = 1 :=
    Subsingleton.elim _ _
  have hp := congrArg₂ A
    (leftPsiSection_zero_projection (k := k) (R := F.Carrier) g) hg0
  have ha := leftPsiNormalizedCoefficient_action (k := k) (r := 0) T X g z
  have h : e (leftPsiNormalizedCoefficient T X g z) = A g.val 1 :=
    ha.trans hp
  have hc : A g.val 1 = TensorProduct.map (X.1.representation g.val) LinearMap.id (e z) := by
    dsimp only [A]
    simp only [map_one, Nat.cast_zero, zero_div, Real.rpow_zero, NNReal.coe_one, Units.val_one,
      Complex.ofReal_one, one_mul, one_smul, Real.one_rpow]
    rfl
  change leftPsiCoefficientEquiv T X (leftPsiNormalizedCoefficient T X g z) =
    TensorProduct.map
      (X.1.representation (reindex (R := F.Carrier) (finCongr (rfl : k = k)) g.val))
      LinearMap.id (leftPsiCoefficientEquiv T X z)
  simpa only [reindex_finCongr_rfl, MulEquiv.refl_apply] using h.trans hc

theorem leftPsiZeroCoefficient_isSmooth :
    letI := T.topology
    IsSmooth (leftPsiNormalizedCoefficient T X) := by
  let := T.topology
  let e := leftPsiZeroCoefficientEquiv T X
  let B := (T.binaryNormalizedProductFunctor k 0).obj
    (X.1, (Mirabolic.psiMinus T 0).obj X.2)
  have hB := isSmooth_of_surjective
    (T.binaryRightZeroTensorEquiv rfl (X.1, (Mirabolic.psiMinus T 0).obj X.2)).toIntertwiningMap
    (T.binaryRightZeroTensorEquiv rfl (X.1, (Mirabolic.psiMinus T 0).obj X.2)).surjective B.isSmooth
  exact isSmooth_of_injective e.toIntertwiningMap e.injective
    (isSmooth_comp _ continuous_subtype_val hB)

/-- Evaluation at the identity for the rank-one source comparison, followed
by the actual coefficient equivalence, gives the complete tensor model. -/
def leftPsiZeroTensorEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 0)
    Representation.Equiv
      (((Mirabolic.psiMinus T (k + 0)).obj
        ((T.leftMixedProductFunctor k 0).obj X)).representation)
      (BinaryTensor.rankZeroRight (b := 0) (R := F.Carrier) rfl X.1.representation
        ((Mirabolic.psiMinus T 0).obj X.2)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + 0)
  let e := Induction.compactInducedTopEquiv
    ((leftSubgroup k 0 F.Carrier).comap (levi (n := k + 0))) mem_leftPsiSection_zero
    (leftPsiNormalizedCoefficient T X) (leftPsiZeroCoefficient_isSmooth T X)
  let e' : Representation.Equiv
      ((leftPsiNormalizedCoefficient T X).comp (Induction.topHom
        ((leftSubgroup k 0 F.Carrier).comap (levi (n := k + 0))) mem_leftPsiSection_zero))
      (BinaryTensor.rankZeroRight (b := 0) (R := F.Carrier) rfl X.1.representation
        ((Mirabolic.psiMinus T 0).obj X.2)) :=
    { toLinearEquiv := (leftPsiZeroCoefficientEquiv T X).toLinearEquiv
      isIntertwining' g := (leftPsiZeroCoefficientEquiv T X).isIntertwining'
        (Induction.topHom
          ((leftSubgroup k 0 F.Carrier).comap (levi (n := k + 0))) mem_leftPsiSection_zero g) }
  exact (leftPsiInductionEquiv T X).trans (e.trans e')

/-- The left Psi comparison at a rank-one source, with both full carriers. -/
def leftPsiZeroEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 0)
    Representation.Equiv
      (((Mirabolic.psiMinus T (k + 0)).obj
        ((T.leftMixedProductFunctor k 0).obj X)).representation)
      (((T.binaryNormalizedProductFunctor k 0).obj
        (X.1, (Mirabolic.psiMinus T 0).obj X.2)).representation) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + 0)
  (leftPsiZeroTensorEquiv T X).trans
    (T.binaryRightZeroTensorEquiv rfl (X.1, (Mirabolic.psiMinus T 0).obj X.2)).symm

variable {Y : letI := T.topology
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier)}

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the complete rank-one source tensor comparison. -/
theorem leftPsiZeroTensorEquiv_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 0)
    ∀ z : (Mirabolic.psiMinus T (k + 0)).obj ((T.leftMixedProductFunctor k 0).obj X),
      leftPsiZeroTensorEquiv T Y
        (SmoothRep.hom ((Mirabolic.psiMinus T (k + 0)).map
          ((T.leftMixedProductFunctor k 0).map f)) z) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap
        (SmoothRep.hom ((Mirabolic.psiMinus T 0).map f.2)).toLinearMap
        (leftPsiZeroTensorEquiv T X z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + 0)
  intro z
  let H := (leftSubgroup k 0 F.Carrier).comap (levi (n := k + 0))
  let σ := leftPsiNormalizedCoefficient T X
  let τ := leftPsiNormalizedCoefficient T Y
  have h := congrArg
    (fun q : Induction.CompactFunctions H τ =>
      leftPsiCoefficientEquiv T Y (Induction.eval H τ q.val 1))
    (leftPsiInductionEquiv_natural (k := k) (r := 0) T X f z)
  exact h.trans (leftPsiCoefficientEquiv_natural (k := k) (r := 0) T X f
    (Induction.eval H σ (leftPsiInductionEquiv T X z).val 1))

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the binary-product comparison, retaining the full GL-zero carrier. -/
theorem leftPsiZeroEquiv_natural (f : letI := T.topology; X ⟶ Y) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + 0)
    ∀ z : (Mirabolic.psiMinus T (k + 0)).obj ((T.leftMixedProductFunctor k 0).obj X),
      leftPsiZeroEquiv T Y
        (SmoothRep.hom ((Mirabolic.psiMinus T (k + 0)).map
          ((T.leftMixedProductFunctor k 0).map f)) z) =
      SmoothRep.hom ((T.binaryNormalizedProductFunctor k 0).map
        (f.1, (Mirabolic.psiMinus T 0).map f.2)) (leftPsiZeroEquiv T X z) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + 0)
  intro z
  let eX := T.binaryRightZeroTensorEquiv rfl (X.1, (Mirabolic.psiMinus T 0).obj X.2)
  let eY := T.binaryRightZeroTensorEquiv rfl (Y.1, (Mirabolic.psiMinus T 0).obj Y.2)
  apply eY.injective
  change eY (eY.symm (leftPsiZeroTensorEquiv T Y _)) =
    eY (SmoothRep.hom ((T.binaryNormalizedProductFunctor k 0).map
      (f.1, (Mirabolic.psiMinus T 0).map f.2)) (eX.symm (leftPsiZeroTensorEquiv T X z)))
  rw [Representation.Equiv.apply_symm_apply,
    T.binaryRightZeroTensorEquiv_naturality rfl,
    Representation.Equiv.apply_symm_apply]
  exact leftPsiZeroTensorEquiv_natural T X f z

end LeftZero
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
