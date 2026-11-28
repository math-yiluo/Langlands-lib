import Langlands.Representation.Shahidi.OpenCellThreeBlock

/-! # Induction in stages for the block sizes `(1, d + 1, t + 1)`

For `ψ` of conductor `𝒪`, the section on `GL_((1 + (d+1)) + (t+1))` induced through the `(d + 2, t + 1)` parabolic from
the degree-`D` piece of `δ^(1/2) F₁ ⊗ W°_c`, where `F₁` is the lift of the degree-`e₁` piece
of the `(1, d + 1)` section with parameters `(a₁, a')`, agrees after reassociating the rank
with the section on `GL_(1 + ((d+1) + (t+1)))` induced through the `(1, d + t + 2)` parabolic
from the degree-`e₁` piece of `δ^(1/2) W°_(a₁) ⊗ F₂`, where `F₂` is the lift of the degree-
`(D - e₁)` piece of the `(d + 1, t + 1)` section with parameters `(a', c)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocTBSTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocTBSValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocTBSLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section Reindex

variable (d t : ℕ)

/-- The rank reassociation `GL_((1 + (d+1)) + (t+1)) ≅ GL_(1 + ((d+1) + (t+1)))`. -/
def threeReindex : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier ≃*
    Langlands.GeneralLinear ((0 + 1) + ((d + 1) + (t + 1))) K.Carrier :=
  GeneralLinear.reindex (finCongr (Nat.add_assoc (0 + 1) (d + 1) (t + 1)))

theorem threeReindex_apply (g : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier)
    (i j : Fin ((0 + 1) + ((d + 1) + (t + 1)))) :
    threeReindex (K := K) d t g i j =
      g (Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm i)
        (Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm j) := rfl

theorem threeReindex_mem_upperUnipotent
    {u : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier}
    (hu : u ∈ upperUnipotent (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier) :
    threeReindex d t u ∈ upperUnipotent ((0 + 1) + ((d + 1) + (t + 1))) K.Carrier := by
  constructor
  · intro i j hij
    rw [threeReindex_apply]
    exact hu.1 (by simpa only [id_eq, Fin.lt_def, Fin.val_cast] using hij)
  · intro i
    rw [threeReindex_apply]
    exact hu.2 _

theorem threeReindex_torus (ν : Fin (((0 + 1) + (d + 1)) + (t + 1)) → ℤ) :
    threeReindex d t (Iwasawa.torus ϖ ν) =
      Iwasawa.torus ϖ fun i => ν (Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm i) := by
  apply Units.ext
  ext i j
  change (Iwasawa.torus ϖ ν).val _ _ = (Iwasawa.torus ϖ _).val i j
  rw [torus_val, torus_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have : Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm i ≠
        Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm j :=
      fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
    simp only [finCongr_symm, finCongr_apply, this, hij, ite_false]

theorem threeReindex_mem_integralSubgroup
    {k : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier}
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers ((0 + 1) + (d + 1) + t)) :
    threeReindex d t k ∈
      integralSubgroup K.canonicalTopologicalData.Integers ((0 + 1) + ((d + 1) + t)) := by
  rw [mem_integralSubgroup] at hk ⊢
  refine ⟨fun i j => hk.1 _ _, fun i j => ?_⟩
  rw [← map_inv]
  exact hk.2 _ _

end Reindex

section Sections

variable (d t : ℕ) (a₁ : Fin (0 + 1) → ℂˣ) (a' : Fin (d + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ)
  (D e₁ : ℤ)

/-- The section induced in stages through the `(d + 2, t + 1)` parabolic. -/
def leftSection : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier → ℂ :=
  liftFunction hϖ (degreePiece hϖ D (prodΦ (r := 0 + 1 + d) (t := t) 0
    (liftFunction hϖ (degreePiece hϖ e₁ (Base.fullΦ ψ hϖ a₁ a' 0)))
    (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
      K.canonicalTopologicalData.residueCardinality c)))

/-- The section induced in stages through the `(1, d + t + 2)` parabolic. -/
def rightSection : Langlands.GeneralLinear ((0 + 1) + ((d + 1) + (t + 1))) K.Carrier → ℂ :=
  liftFunction hϖ (degreePiece hϖ e₁ (prodΦ (r := 0) (t := d + 1 + t) 0
    (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
      K.canonicalTopologicalData.residueCardinality a₁)
    (liftFunction hϖ (degreePiece hϖ (D - e₁) (Base.fullΦ ψ hϖ a' c 0)))))

/-- The common value of both sections at a three-block Levi point. -/
def threeBlockValue (x₁ : Langlands.GeneralLinear (0 + 1) K.Carrier)
    (x₂ : Langlands.GeneralLinear (d + 1) K.Carrier) (x₃ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    ℂ :=
  if detExponent hϖ x₁ = e₁ ∧ detExponent hϖ x₂ = D - e₁ then
    (((((K.canonicalTopologicalData.determinantNorm (0 + 1) x₁ : NNReal) : ℝ) *
          ((K.canonicalTopologicalData.determinantNorm (d + 1) x₂ : NNReal) : ℝ)) ^ (t + 1) /
        ((K.canonicalTopologicalData.determinantNorm (t + 1) x₃ : NNReal) : ℝ) ^ (0 + 1 + d + 1) :
          ℝ) : ℂ) ^ ((1 : ℂ) / 2 + 0 / ((0 + 1 + d + t + 2 : ℕ) : ℂ)) *
      ((twoBlockModulus K x₁ x₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + 0 / ((0 + d + 2 : ℕ) : ℂ)) *
      GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a₁ x₁ *
      GeneralLinear.Spherical.sphericalWhittaker (n := d) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ d)
        K.canonicalTopologicalData.residueCardinality a' x₂ *
      GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c x₃
  else 0

variable {ψ}

include hϖ in
theorem whittaker_mul_integral' (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) {n : ℕ}
    (x : Fin (n + 1) → ℂˣ) :
    ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers n,
      GeneralLinear.Spherical.sphericalWhittaker (n := n) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n)
        K.canonicalTopologicalData.residueCardinality x (g * k) =
      GeneralLinear.Spherical.sphericalWhittaker (n := n) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n)
        K.canonicalTopologicalData.residueCardinality x g := fun g _k hk =>
  GeneralLinear.Spherical.sphericalWhittaker_mul_integral hϖ _ x
    (isIntegrallyTrivial_of_additiveConductor K hψ n) g hk

theorem isLeviInvariant_leftSection (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) :
    IsLeviInvariant (degreePiece hϖ D (prodΦ (r := 0 + 1 + d) (t := t) 0
      (liftFunction hϖ (degreePiece hϖ e₁ (Base.fullΦ ψ hϖ a₁ a' 0)))
      (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
        K.canonicalTopologicalData.residueCardinality c))) :=
  isLeviInvariant_degreePiece hϖ D (isLeviInvariant_prodΦ (r := 0 + 1 + d) (t := t) 0
    (fun g k hk => liftFunction_mul_integral hϖ
      (isLeviInvariant_degreePiece hϖ e₁ (Base.isLeviInvariant_fullΦ hϖ hψ a₁ a' 0)) g k hk)
    (whittaker_mul_integral' hϖ hψ c))

theorem isLeviInvariant_rightSection (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) :
    IsLeviInvariant (degreePiece hϖ e₁ (prodΦ (r := 0) (t := d + 1 + t) 0
      (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
        (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
        K.canonicalTopologicalData.residueCardinality a₁)
      (liftFunction hϖ (degreePiece hϖ (D - e₁) (Base.fullΦ ψ hϖ a' c 0))))) :=
  isLeviInvariant_degreePiece hϖ e₁ (isLeviInvariant_prodΦ (r := 0) (t := d + 1 + t) 0
    (whittaker_mul_integral' hϖ hψ a₁)
    (fun g k hk => liftFunction_mul_integral hϖ
      (isLeviInvariant_degreePiece hϖ (D - e₁) (Base.isLeviInvariant_fullΦ hϖ hψ a' c 0)) g k hk))

include hϖ in
theorem det_unipotent_mul_torus_sum {m n : ℕ} {u : Langlands.GeneralLinear (m + n) K.Carrier}
    (hu : u ∈ upperUnipotent (m + n) K.Carrier) (ν : Fin (m + n) → ℤ) :
    ((K.canonicalTopologicalData.determinantNorm (m + n) (u * Iwasawa.torus ϖ ν) : NNReal) : ℝ) =
      ((K.canonicalTopologicalData.determinantNorm m
          (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd n)) : NNReal) : ℝ) *
        ((K.canonicalTopologicalData.determinantNorm n
          (botRight u hu.1 * Iwasawa.torus ϖ fun j => ν (j.natAdd m)) : NNReal) : ℝ) := by
  have hq : (K.canonicalTopologicalData.residueCardinality : ℝ) ≠ 0 := by
    have := residueCardinality_pos K
    positivity
  rw [determinantNorm_unipotent_mul_torus K hϖ hu,
    determinantNorm_unipotent_mul_torus K hϖ (topLeft_mem_upperUnipotent hu),
    determinantNorm_unipotent_mul_torus K hϖ (botRight_mem_upperUnipotent hu), ← zpow_add₀ hq,
    Fin.sum_univ_add, neg_add]

/-- The left section at an upper triangular point, for `ψ` of conductor `𝒪`. -/
theorem leftSection_unipotent_mul_torus (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    {u : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier}
    (hu : u ∈ upperUnipotent (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier)
    (μ : Fin (((0 + 1) + (d + 1)) + (t + 1)) → ℤ) :
    leftSection ψ hϖ d t a₁ a' c D e₁ (u * Iwasawa.torus ϖ μ) =
      threeBlockValue ψ hϖ d t a₁ a' c D e₁
        (topLeft (topLeft u hu.1) (topLeft_mem_upperUnipotent hu).1 *
          Iwasawa.torus ϖ fun i => μ ((i.castAdd (d + 1)).castAdd (t + 1)))
        (botRight (topLeft u hu.1) (topLeft_mem_upperUnipotent hu).1 *
          Iwasawa.torus ϖ fun j => μ ((j.natAdd (0 + 1)).castAdd (t + 1)))
        (botRight u hu.1 * Iwasawa.torus ϖ fun j => μ (j.natAdd (0 + 1 + d + 1))) := by
  have hu₁ := topLeft_mem_upperUnipotent hu
  unfold leftSection
  rw [liftFunction_unipotent_mul_torus hϖ (isLeviInvariant_leftSection hϖ d t a₁ a' c D e₁ hψ) hu]
  simp only [degreePiece, prodΦ]
  rw [liftFunction_unipotent_mul_torus hϖ
    (isLeviInvariant_degreePiece hϖ e₁ (Base.isLeviInvariant_fullΦ hϖ hψ a₁ a' 0)) hu₁]
  simp only [degreePiece, Base.fullΦ, threeBlockValue]
  have hdet : detExponent hϖ (topLeft u hu.1 * Iwasawa.torus ϖ fun i => μ (i.castAdd (t + 1))) =
      detExponent hϖ (topLeft (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun i => μ ((i.castAdd (d + 1)).castAdd (t + 1))) +
        detExponent hϖ (botRight (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun j => μ ((j.natAdd (0 + 1)).castAdd (t + 1))) := by
    rw [detExponent_unipotent_mul_torus hϖ hu₁,
      detExponent_unipotent_mul_torus hϖ (topLeft_mem_upperUnipotent hu₁),
      detExponent_unipotent_mul_torus hϖ (botRight_mem_upperUnipotent hu₁)]
    erw [Fin.sum_univ_add (a := 0 + 1) (b := d + 1)]
  have hmod : twoBlockModulus K (topLeft u hu.1 * Iwasawa.torus ϖ fun i => μ (i.castAdd (t + 1)))
      (botRight u hu.1 * Iwasawa.torus ϖ fun j => μ (j.natAdd (0 + 1 + d + 1))) =
      (((K.canonicalTopologicalData.determinantNorm (0 + 1) (topLeft (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun i => μ ((i.castAdd (d + 1)).castAdd (t + 1))) : NNReal) : ℝ) *
        ((K.canonicalTopologicalData.determinantNorm (d + 1) (botRight (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun j => μ ((j.natAdd (0 + 1)).castAdd (t + 1))) : NNReal) : ℝ)) ^ (t + 1) /
      ((K.canonicalTopologicalData.determinantNorm (t + 1) (botRight u hu.1 *
          Iwasawa.torus ϖ fun j => μ (j.natAdd (0 + 1 + d + 1))) : NNReal) : ℝ) ^ (0 + 1 + d + 1) := by
    rw [twoBlockModulus]
    erw [det_unipotent_mul_torus_sum hϖ hu₁]
    rfl
  erw [hdet, hmod]
  by_cases h₁ : detExponent hϖ (topLeft (topLeft u hu.1) hu₁.1 *
      Iwasawa.torus ϖ fun i => μ ((i.castAdd (d + 1)).castAdd (t + 1))) = e₁
  · by_cases h₂ : detExponent hϖ (botRight (topLeft u hu.1) hu₁.1 *
        Iwasawa.torus ϖ fun j => μ ((j.natAdd (0 + 1)).castAdd (t + 1))) = D - e₁
    · have h₃ : detExponent hϖ (topLeft (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun i => μ ((i.castAdd (d + 1)).castAdd (t + 1))) +
          detExponent hϖ (botRight (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun j => μ ((j.natAdd (0 + 1)).castAdd (t + 1))) = D := by omega
      simp only [h₁, h₂, and_self, add_sub_cancel, ↓reduceIte]
      ring
    · have h₃ : ¬ (detExponent hϖ (topLeft (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun i => μ ((i.castAdd (d + 1)).castAdd (t + 1))) +
          detExponent hϖ (botRight (topLeft u hu.1) hu₁.1 *
          Iwasawa.torus ϖ fun j => μ ((j.natAdd (0 + 1)).castAdd (t + 1))) = D) := by omega
      simp only [h₃, h₂, and_false, ite_false]
  · simp only [h₁, false_and, ite_false, mul_zero, zero_mul, ite_self]

theorem cpow_half_identity (d₁ d₂ d₃ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (d t : ℕ) :
    ((d₁ ^ (d + 1 + t + 1) / (d₂ * d₃) ^ (0 + 1) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) *
        ((d₂ ^ (t + 1) / d₃ ^ (d + 1) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) =
      (((d₁ * d₂) ^ (t + 1) / d₃ ^ (0 + 1 + d + 1) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) *
        ((d₁ ^ (d + 1) / d₂ ^ (0 + 1) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
  rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← Complex.ofReal_mul,
    ← Complex.ofReal_mul]
  congr 2
  field_simp
  ring

theorem determinantNorm_pos {n : ℕ} (g : Langlands.GeneralLinear n K.Carrier) :
    0 < ((K.canonicalTopologicalData.determinantNorm n g : NNReal) : ℝ) := by
  have := (K.canonicalTopologicalData.determinantNorm n g).ne_zero
  positivity

/-- The right section at an upper triangular point, for `ψ` of conductor `𝒪`. -/
theorem rightSection_unipotent_mul_torus (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    {u : Langlands.GeneralLinear ((0 + 1) + ((d + 1) + (t + 1))) K.Carrier}
    (hu : u ∈ upperUnipotent ((0 + 1) + ((d + 1) + (t + 1))) K.Carrier)
    (ν : Fin ((0 + 1) + ((d + 1) + (t + 1))) → ℤ) :
    rightSection ψ hϖ d t a₁ a' c D e₁ (u * Iwasawa.torus ϖ ν) =
      threeBlockValue ψ hϖ d t a₁ a' c D e₁
        (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd (d + 1 + t + 1)))
        (topLeft (botRight u hu.1) (botRight_mem_upperUnipotent hu).1 *
          Iwasawa.torus ϖ fun i => ν ((i.castAdd (t + 1)).natAdd (0 + 1)))
        (botRight (botRight u hu.1) (botRight_mem_upperUnipotent hu).1 *
          Iwasawa.torus ϖ fun j => ν ((j.natAdd (d + 1)).natAdd (0 + 1))) := by
  have hu₂ := botRight_mem_upperUnipotent hu
  unfold rightSection
  rw [liftFunction_unipotent_mul_torus hϖ (isLeviInvariant_rightSection hϖ d t a₁ a' c D e₁ hψ) hu]
  simp only [degreePiece, prodΦ]
  erw [liftFunction_unipotent_mul_torus hϖ
    (isLeviInvariant_degreePiece hϖ (D - e₁) (Base.isLeviInvariant_fullΦ hϖ hψ a' c 0)) hu₂]
  simp only [degreePiece, Base.fullΦ, threeBlockValue]
  by_cases h₁ : detExponent hϖ (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd (d + 1 + t + 1))) = e₁
  · by_cases h₂ : detExponent hϖ (topLeft (botRight u hu.1) hu₂.1 *
        Iwasawa.torus ϖ fun i => ν ((i.castAdd (t + 1)).natAdd (0 + 1))) = D - e₁
    · simp only [h₁, h₂, and_self, ↓reduceIte, zero_div, add_zero]
      rw [twoBlockModulus, twoBlockModulus, twoBlockModulus]
      erw [det_unipotent_mul_torus_sum hϖ hu₂]
      have key := cpow_half_identity
        ((K.canonicalTopologicalData.determinantNorm (0 + 1)
          (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd (d + 1 + t + 1))) : NNReal) : ℝ)
        ((K.canonicalTopologicalData.determinantNorm (d + 1) (topLeft (botRight u hu.1) hu₂.1 *
          Iwasawa.torus ϖ fun i => ν ((i.castAdd (t + 1)).natAdd (0 + 1))) : NNReal) : ℝ)
        ((K.canonicalTopologicalData.determinantNorm (t + 1) (botRight (botRight u hu.1) hu₂.1 *
          Iwasawa.torus ϖ fun j => ν ((j.natAdd (d + 1)).natAdd (0 + 1))) : NNReal) : ℝ)
        (determinantNorm_pos _) (determinantNorm_pos _) (determinantNorm_pos _) d t
      linear_combination
        (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
          K.canonicalTopologicalData.residueCardinality a₁
          (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd (d + 1 + t + 1))) *
        GeneralLinear.Spherical.sphericalWhittaker (n := d) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ d)
          K.canonicalTopologicalData.residueCardinality a' (topLeft (botRight u hu.1) hu₂.1 *
            Iwasawa.torus ϖ fun i => ν ((i.castAdd (t + 1)).natAdd (0 + 1))) *
        GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c (botRight (botRight u hu.1) hu₂.1 *
            Iwasawa.torus ϖ fun j => ν ((j.natAdd (d + 1)).natAdd (0 + 1)))) * key
    · simp only [h₁, h₂, and_false, ↓reduceIte, mul_zero]
  · simp only [h₁, false_and, ↓reduceIte]

theorem leftSection_mul_integral (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (x k : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers ((0 + 1) + (d + 1) + t)) :
    leftSection ψ hϖ d t a₁ a' c D e₁ (x * k) = leftSection ψ hϖ d t a₁ a' c D e₁ x :=
  liftFunction_mul_integral hϖ (isLeviInvariant_leftSection hϖ d t a₁ a' c D e₁ hψ) x k hk

theorem rightSection_mul_integral (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (x k : Langlands.GeneralLinear ((0 + 1) + ((d + 1) + (t + 1))) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers ((0 + 1) + ((d + 1) + t))) :
    rightSection ψ hϖ d t a₁ a' c D e₁ (x * k) = rightSection ψ hϖ d t a₁ a' c D e₁ x :=
  liftFunction_mul_integral hϖ (isLeviInvariant_rightSection hϖ d t a₁ a' c D e₁ hψ) x k hk

/-- **Induction in stages: the two three-block sections agree**, for `ψ` of conductor `𝒪`. -/
theorem leftSection_eq_rightSection (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (g : Langlands.GeneralLinear (((0 + 1) + (d + 1)) + (t + 1)) K.Carrier) :
    leftSection ψ hϖ d t a₁ a' c D e₁ g = rightSection ψ hϖ d t a₁ a' c D e₁ (threeReindex d t g) := by
  obtain ⟨u, hu, μ, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (n := (0 + 1) + (d + 1) + t) hϖ g
  rw [map_mul, map_mul, threeReindex_torus, leftSection_mul_integral hϖ d t a₁ a' c D e₁ hψ _ k hk,
    rightSection_mul_integral hϖ d t a₁ a' c D e₁ hψ _ _ (threeReindex_mem_integralSubgroup d t hk),
    leftSection_unipotent_mul_torus hϖ d t a₁ a' c D e₁ hψ hu,
    rightSection_unipotent_mul_torus hϖ d t a₁ a' c D e₁ hψ (threeReindex_mem_upperUnipotent d t hu)]
  have hu' := threeReindex_mem_upperUnipotent d t hu
  have hu₁ := topLeft_mem_upperUnipotent (m := 0 + 1 + (d + 1)) (n := t + 1) hu
  have hu₂ := botRight_mem_upperUnipotent hu'
  have h₁ : topLeft (topLeft (m := 0 + 1 + (d + 1)) (n := t + 1) u hu.1) hu₁.1 *
        Iwasawa.torus ϖ (fun i : Fin (0 + 1) => μ ((i.castAdd (d + 1)).castAdd (t + 1))) =
      topLeft (threeReindex d t u) hu'.1 * Iwasawa.torus ϖ (fun i : Fin (0 + 1) =>
        μ (Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm (i.castAdd (d + 1 + t + 1)))) := by
    congr 1
  have h₂ : botRight (topLeft (m := 0 + 1 + (d + 1)) (n := t + 1) u hu.1) hu₁.1 *
        Iwasawa.torus ϖ (fun j : Fin (d + 1) => μ ((j.natAdd (0 + 1)).castAdd (t + 1))) =
      topLeft (botRight (threeReindex d t u) hu'.1) hu₂.1 * Iwasawa.torus ϖ (fun i : Fin (d + 1) =>
        μ (Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm ((i.castAdd (t + 1)).natAdd (0 + 1)))) := by
    congr 1
  have h₃ : botRight (m := 0 + 1 + (d + 1)) (n := t + 1) u hu.1 *
        Iwasawa.torus ϖ (fun j : Fin (t + 1) => μ (j.natAdd (0 + 1 + d + 1))) =
      botRight (botRight (threeReindex d t u) hu'.1) hu₂.1 * Iwasawa.torus ϖ (fun j : Fin (t + 1) =>
        μ (Fin.cast (Nat.add_assoc (0 + 1) (d + 1) (t + 1)).symm ((j.natAdd (d + 1)).natAdd (0 + 1)))) := by
    congr 1
    all_goals first
      | (apply Units.ext; ext i j; change u _ _ = u _ _
         exact congrArg₂ (fun a b => u a b) (Fin.ext (by simp; try omega))
           (Fin.ext (by simp; try omega)))
      | (congr 1; funext i; exact congrArg μ (Fin.ext (by simp; try omega)))
  rw [h₁, h₂, h₃]

end Sections

end Langlands.Shahidi.OpenCell
