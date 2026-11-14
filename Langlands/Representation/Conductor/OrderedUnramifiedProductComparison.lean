import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries
import Langlands.Representation.Induction.Equivalences
import Mathlib.RingTheory.PiTensorProduct

/-!
# Unramified principal series as a normalized product of rank-one blocks

Over a nonarchimedean local field `F`, the unramified principal series
`principalSeries hϖ n hq z` of `Conductor.UnramifiedPrincipalSeries` is equivalent to the
normalized product induction, from the singleton block shape, of any family of
one-dimensional representations of `GL_1(F)` on which `g` acts by `z_i ^ ord(det g)`.
The normalizing character of the product induction is the all-field half modulus of
`Langlands.AllFieldBZ`; on the upper Borel it agrees with the explicit half modulus
`halfModulusCharacter`.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedProductComparison

open Langlands.GeneralLinear Langlands.Conductor.UnramifiedPrincipalSeries
open scoped NNReal

universe uF uV

/-- The all-field package of a field. -/
abbrev pkg (F : Type uF) [Field F] : AllFieldBZ.LocalFieldPackage.{uF} :=
  AllFieldBZ.LocalFieldPackage.ofField F

/-- The supplied local-field structures of `F`, as local-field data of its package. -/
abbrev data (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (pkg F).TopologicalData :=
  LocalFieldData.ofInstances F

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : Fˣ}
  (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

section Arithmetic

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem data_discreteValuation [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) :
    (data F).discreteValuation x =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (ValuativeRel.valuation F x) :=
  rfl

theorem data_ord_of_valuation {x : F} {k : ℤ}
    (hx : ValuativeRel.valuation F x = ValuativeRel.valuation F (ϖ : F) ^ k) :
    (data F).ord x = k * (data F).ord (ϖ : F) := by
  simp only [LocalFieldData.ord, data_discreteValuation, hx, map_zpow₀, WithZero.log_zpow,
    smul_eq_mul]
  ring

include hϖ in
theorem data_ord_uniformizer : (data F).ord (ϖ : F) = 1 := by
  set t := (data F).ord (ϖ : F) with ht_def
  have hπ : (data F).uniformizer ≠ 0 := by
    intro h
    have h1 := (data F).ord_uniformizer
    rw [h, (data F).ord_zero] at h1
    exact zero_ne_one h1
  obtain ⟨k, hk⟩ := hϖ.2 _ hπ
  have h1 : k * t = 1 := by
    rw [← data_ord_of_valuation hk, (data F).ord_uniformizer]
  have ht : 0 < t := by
    set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
    have hlt : e (ValuativeRel.valuation F (ϖ : F)) < 1 := by
      rw [← map_one e]
      exact (map_lt_map_iff e).2 hϖ.1
    have hne : e (ValuativeRel.valuation F (ϖ : F)) ≠ 0 := by
      simp
    have hlog : WithZero.log (e (ValuativeRel.valuation F (ϖ : F))) < 0 := by
      rw [← WithZero.exp_log hne] at hlt
      rw [← WithZero.exp_zero] at hlt
      exact WithZero.exp_lt_exp.1 hlt
    rw [ht_def]
    simp only [LocalFieldData.ord, data_discreteValuation]
    change 0 < -WithZero.log (e (ValuativeRel.valuation F (ϖ : F)))
    omega
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem data_ord (a : Fˣ) : (data F).ord (a : F) = ord hϖ a := by
  rw [data_ord_of_valuation (valuation_eq_pow_ord hϖ a), data_ord_uniformizer hϖ, mul_one]

theorem data_residueCardinality {q : ℕ} (hq : IsResidueCardinality (F := F) q) :
    (data F).residueCardinality = q :=
  hq.symm

theorem data_normalizedAbs {q : ℕ} (hq : IsResidueCardinality (F := F) q) (a : Fˣ) :
    (data F).normalizedAbs (a : F) = (q : ℝ) ^ (-ord hϖ a) := by
  rw [(data F).normalizedAbs_of_ne_zero a.ne_zero, data_ord hϖ, data_residueCardinality hq]

end Arithmetic

section PairSum

/-- The exponent of the singleton block modulus, rewritten as the exponent of the
explicit half modulus `halfModulusCharacter`. -/
theorem pairSum_eq (n : ℕ) (o : Fin (n + 1) → ℤ) :
    ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j => i < j), (o j - o i) =
      -∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * o i := by
  have h1 : ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j => i < j), o j =
      ∑ j : Fin (n + 1), (j : ℤ) * o j := by
    rw [Finset.sum_comm' (s' := fun j => Finset.univ.filter (fun i => i < j))
      (t' := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_const, nsmul_eq_mul, Finset.filter_gt_eq_Iio, Fin.card_Iio]
    · intro i j
      simp
  have h2 : ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j => i < j), o i =
      ∑ i : Fin (n + 1), ((n : ℤ) - (i : ℤ)) * o i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    push_cast [Nat.add_sub_cancel, hi]
    ring
  simp only [Finset.sum_sub_distrib]
  rw [h1, h2, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PairSum

section Borel

variable (n : ℕ)

/-- The upper Borel of `UnramifiedPrincipalSeries`, identified with the parabolic of the
singleton block shape; the underlying matrices are unchanged. -/
def toParabolic :
    Borel (F := F) n ≃* (GeneralLinear.BlockShape.singletons (n + 1)).parabolic F :=
  MulEquiv.subgroupCongr (borel_eq_singleton_parabolic n)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem toParabolic_val (b : Borel (F := F) n) :
    ((toParabolic n b : (GeneralLinear.BlockShape.singletons (n + 1)).parabolic F) :
      Langlands.GeneralLinear (n + 1) F) = b.val := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The determinant of the `i`-th singleton block of the Levi projection is the
`i`-th diagonal entry. -/
theorem determinant_leviProjection_toParabolic (b : Borel (F := F) n) (i : Fin (n + 1)) :
    GeneralLinear.determinant
        ((GeneralLinear.BlockShape.singletons (n + 1)).leviProjection F (toParabolic n b) i) =
      diagonalUnit n i b := by
  apply Units.ext
  change Matrix.det
      (((GeneralLinear.BlockShape.singletons (n + 1)).leviProjection F
        (toParabolic n b) i).val) = b.val i i
  rw [Matrix.det_unique]
  change b.val ((GeneralLinear.BlockShape.singletons (n + 1)).index i default)
      ((GeneralLinear.BlockShape.singletons (n + 1)).index i default) = b.val i i
  rw [GeneralLinear.BlockShape.singletons_index]

end Borel


section HalfModulus

variable (n : ℕ) {q : ℕ} (hq : IsResidueCardinality (F := F) q)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] (a : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

/-- The residue cardinality as a unit of `ℝ≥0`. -/
def residueUnit : ℝ≥0ˣ :=
  Units.mk0 (q : ℝ≥0) (by exact_mod_cast (residueCardinality_pos hq).ne')

@[simp] theorem residueUnit_val : ((residueUnit hq : ℝ≥0) : ℝ) = q := rfl

theorem normalizedAbsUnits_eq (a : Fˣ) :
    (data F).normalizedAbsUnits a = residueUnit hq ^ (-ord hϖ a) := by
  apply Units.ext
  apply NNReal.eq
  erw [AllFieldBZ.LocalFieldPackage.TopologicalData.normalizedAbsUnits_coe]
  rw [data_normalizedAbs hϖ hq, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, residueUnit_val]

/-- The all-field singleton block modulus of the Levi part of a Borel element. -/
theorem leviModulus_toParabolic (b : Borel (F := F) n) :
    (data F).leviModulus (GeneralLinear.BlockShape.singletons (n + 1))
        ((GeneralLinear.BlockShape.singletons (n + 1)).leviProjection F (toParabolic n b)) =
      residueUnit hq ^
        (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i b)) := by
  have h : ∀ k : Fin (n + 1),
      (data F).determinantNorm 1
          ((GeneralLinear.BlockShape.singletons (n + 1)).leviProjection F (toParabolic n b) k) =
        residueUnit hq ^ (-ord hϖ (diagonalUnit n k b)) := fun k =>
    (congrArg (data F).normalizedAbsUnits (determinant_leviProjection_toParabolic n b k)).trans
      (normalizedAbsUnits_eq hϖ hq _)
  erw [AllFieldBZ.LocalFieldPackage.TopologicalData.leviModulus_apply]
  rw [← pairSum_eq, ← prod_zpow_eq_zpow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← prod_zpow_eq_zpow_sum]
  apply Finset.prod_congr rfl
  intro j _
  refine (congrArg₂ (fun x y : ℝ≥0ˣ => x ^ 1 / y ^ 1) (h i) (h j)).trans ?_
  rw [pow_one, pow_one, div_eq_mul_inv, ← zpow_sub]
  congr 1
  ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem nnrealSqrt_zpow (x : ℝ≥0) (k : ℤ) : NNReal.sqrt (x ^ k) = NNReal.sqrt x ^ k :=
  map_zpow₀ NNReal.sqrtHom x k

/-- The all-field normalizing half modulus agrees with the explicit half modulus on the
upper Borel. -/
theorem leviHalfModulus_toParabolic (b : Borel (F := F) n) :
    ((data F).leviHalfModulus (GeneralLinear.BlockShape.singletons (n + 1))
        ((GeneralLinear.BlockShape.singletons (n + 1)).leviProjection F (toParabolic n b)) :
          ℂ) =
      (halfModulusCharacter hϖ n hq b : ℂ) := by
  erw [AllFieldBZ.LocalFieldPackage.TopologicalData.leviHalfModulus_apply,
    leviModulus_toParabolic hϖ n hq]
  rw [halfModulusCharacter_apply, Units.val_zpow_eq_zpow_val,
    nnrealSqrt_zpow, NNReal.coe_zpow, Complex.ofReal_zpow]
  congr 2
  change ((NNReal.sqrt (residueUnit hq : ℝ≥0) : ℝ≥0) : ℝ) = Real.sqrt (q : ℝ)
  rw [Real.coe_sqrt, residueUnit_val]

end HalfModulus

section Equivalence

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A family of scalar actions acts on the finite external tensor product by the product
of the scalars. -/
theorem external_eq_smul {ι : Type*} [Fintype ι] {H : ι → Type*} [∀ i, Group (H i)]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (c : ∀ i, H i → ℂ)
    (hρ : ∀ i g v, ρ i g v = c i g • v) (m : ∀ i, H i) (x : PiTensorProduct ℂ V) :
    FiniteTensor.external ρ m x = (∏ i, c i (m i)) • x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, FiniteTensor.external_tprod, smul_comm]
    congr 1
    simp_rw [hρ]
    exact MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ) _ _
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-- Smooth induction along equal subgroups. -/
private def smoothInducedSubgroupCongr {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H K : Subgroup G) (h : H = K) (σ : Representation ℂ K V) :
    (Induction.smoothInduced H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom)).Equiv
      (Induction.smoothInduced K σ) := by
  subst K
  exact Representation.Equiv.refl _

variable (n : ℕ) {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)

/-- The singleton block shape of size `n + 1`. -/
abbrev blocks : GeneralLinear.BlockShape (n + 1) := GeneralLinear.BlockShape.singletons (n + 1)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The topological ring structure of the supplied local-field data. -/
theorem isTopologicalRing_data [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    letI := (data F).topology
    IsTopologicalRing (pkg F).Carrier :=
  (inferInstance : IsTopologicalRing F)

/-- The inducing representation of the parabolic of the normalized product induction of
the blocks `X`. -/
abbrev blockInducing
    (X : ∀ i : Fin (n + 1), SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear ((blocks n).size i) F)) :
    Representation ℂ ((blocks n).parabolic (pkg F).Carrier) (PiTensorProduct ℂ (fun i => X i)) :=
  letI := (data F).topology
  letI := isTopologicalRing_data (F := F)
  (blocks n).inducingRepresentation ((data F).leviHalfCharacter (blocks n))
    ((blocks n).blockTensor (fun i => (X i).representation))

/-- The normalized Borel character, as the Levi half modulus times the block characters. -/
theorem normalizedCharacter_eq_levi (b : Borel (F := F) n) :
    (normalizedCharacter hϖ n hq z b : ℂ) =
      ((data F).leviHalfModulus (blocks n)
          ((blocks n).leviProjection F (toParabolic n b)) : ℂ) *
        ∏ i, (character hϖ (z i) (GeneralLinear.determinant
          ((blocks n).leviProjection F (toParabolic n b) i)) : ℂ) := by
  rw [normalizedCharacter_apply, leviHalfModulus_toParabolic hϖ n hq]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun a => (character hϖ (z i) a : ℂ))
    (determinant_leviProjection_toParabolic n b i).symm

/-- On the line of a scalar block family, the normalized Borel character representation
is the inducing representation of the normalized product induction, pulled back to the
Borel. -/
def characterEquiv
    (X : ∀ i : Fin (n + 1), SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear ((blocks n).size i) F))
    (E : PiTensorProduct ℂ (fun i => X i) ≃ₗ[ℂ] ℂ)
    (hX : ∀ i g v, (X i).representation g v =
      (character hϖ (z i) (GeneralLinear.determinant g) : ℂ) • v) :
    (Langlands.characterRepresentation (normalizedCharacter hϖ n hq z)).Equiv
      ((blockInducing n X).comp (toParabolic n).toMonoidHom) where
  toLinearEquiv := E.symm
  isIntertwining' b := LinearMap.ext fun c => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change E.symm ((normalizedCharacter hϖ n hq z b : ℂ) • c) =
      ((data F).leviHalfModulus (blocks n)
          ((blocks n).leviProjection F (toParabolic n b)) : ℂ) •
        FiniteTensor.external (fun i => (X i).representation)
          ((blocks n).leviProjection F (toParabolic n b)) (E.symm c)
    rw [external_eq_smul _ (fun i g => (character hϖ (z i) (GeneralLinear.determinant g) : ℂ))
      hX, smul_smul, ← normalizedCharacter_eq_levi hϖ n hq z b, map_smul]

/-- The unramified principal series is equivalent to the normalized product induction,
from the singleton block shape, of a family of blocks on which `GL_1(F)` acts by the
unramified characters `z_i ^ ord(det g)`. -/
def principalSeriesEquiv
    (X : ∀ i : Fin (n + 1), SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear ((blocks n).size i) F))
    (E : PiTensorProduct ℂ (fun i => X i) ≃ₗ[ℂ] ℂ)
    (hX : ∀ i g v, (X i).representation g v =
      (character hϖ (z i) (GeneralLinear.determinant g) : ℂ) • v) :
    letI := (data F).topology
    (principalSeries hϖ n hq z).Equiv
      (((data F).normalizedProductInductionFunctor (blocks n)).obj X).representation :=
  (Induction.smoothInducedEquiv (Borel n) (characterEquiv hϖ n hq z X E hX)).trans
    (smoothInducedSubgroupCongr (Borel n) ((blocks n).parabolic F)
      (borel_eq_singleton_parabolic n) (blockInducing n X))

end Equivalence

section Line

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A finite tensor product of lines is a line: the tensor product of linear
identifications `V i ≃ ℂ`, followed by multiplication of the factors. -/
def lineEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (e : ∀ i, V i ≃ₗ[ℂ] ℂ) :
    PiTensorProduct ℂ V ≃ₗ[ℂ] ℂ :=
  (PiTensorProduct.congr e).trans (PiTensorProduct.constantBaseRingEquiv ι ℂ).toLinearEquiv

end Line

end Langlands.Conductor.OrderedUnramifiedProductComparison
