import Langlands.Representation.Shahidi.OpenCellThreeBlockCoordinates

/-! # Shell sums as Jacquet functions of degree pieces

For an additive character of conductor `𝒪` and a Levi-invariant Levi function, the Jacquet
function at `1` of the degree-`e` piece is the finite sum, over the classes of
`M_((t+1)×(r+1))(K) / M_((t+1)×(r+1))(𝒪)` of depth `e`, of the open-cell summands of the lift.
Hence the shell identities of the two-block section are equalities of Jacquet functions of
degree pieces. The Jacquet integrand of a degree piece of a Levi-invariant function is integrable
at every torus point (after the rectangular change of variables its amplitude is supported on a
single depth shell), and at every point when the function is moreover Levi-equivariant (by the
Iwasawa decomposition). -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocShellTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocShellValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocShellLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocShellT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocShellSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocShellMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocShellBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}

section DetExponent

include hϖ in
/-- `|det m| = q^(-v(det m))`. -/
theorem determinantNorm_eq_zpow {n : ℕ} (m : Langlands.GeneralLinear (n + 1) K.Carrier) :
    ((K.canonicalTopologicalData.determinantNorm (n + 1) m : NNReal) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-detExponent hϖ m) := by
  obtain ⟨u, hu, k, hk, h⟩ := Iwasawa.exists_eq_exponent hϖ m
  conv_lhs => rw [h]
  rw [Base.determinantNorm_mul_integral' _ k hk, determinantNorm_unipotent_mul_torus K hϖ hu]
  rfl

/-- Left multiplication by an element with `|det g| = 1` keeps the degree. -/
theorem detExponent_mul_of_determinantNorm {n : ℕ} {g : Langlands.GeneralLinear (n + 1) K.Carrier}
    (hg : ((K.canonicalTopologicalData.determinantNorm (n + 1) g : NNReal) : ℝ) = 1)
    (m : Langlands.GeneralLinear (n + 1) K.Carrier) :
    detExponent hϖ (g * m) = detExponent hϖ m := by
  have h := determinantNorm_eq_zpow hϖ (g * m)
  rw [map_mul, Units.val_mul, NNReal.coe_mul, hg, one_mul, determinantNorm_eq_zpow hϖ m] at h
  have := Base.zpow_residue_injective (K := K) h
  omega

theorem detExponent_torus_mul_unipotent_mul_torus {n : ℕ} (μ ρ : Fin (n + 1) → ℤ)
    {u : Langlands.GeneralLinear (n + 1) K.Carrier} (hu : u ∈ upperUnipotent (n + 1) K.Carrier) :
    detExponent hϖ (Iwasawa.torus ϖ μ * (u * Iwasawa.torus ϖ ρ)) = ∑ i, μ i + ∑ i, ρ i := by
  rw [torus_mul_unipotent_mul_torus,
    detExponent_unipotent_mul_torus hϖ
      (RankinSelberg.UnramifiedWhittaker.torus_conj_mem_upperUnipotent ϖ μ hu),
    ← Finset.sum_add_distrib]
  rfl

/-- The Levi function recording the first-block degree. -/
def degreeΦ (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    (_m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) : ℂ :=
  (detExponent hϖ m₁ : ℂ)

theorem isLeviInvariant_degreeΦ : IsLeviInvariant (degreeΦ (r := r) (t := t) hϖ) := by
  intro m₁ μ₁ m₂ μ₂ h₁ _
  simp only [degreeΦ, detExponent_mul_integral hϖ m₁ h₁]

theorem liftFunction_degreeΦ (x : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ (degreeΦ hϖ) x = (liftDegree hϖ x : ℂ) := rfl

theorem liftDegree_mul_integral (x k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    liftDegree hϖ (x * k) = liftDegree hϖ x := by
  have h := liftFunction_mul_integral hϖ (isLeviInvariant_degreeΦ (r := r) (t := t) hϖ) x k hk
  rw [liftFunction_degreeΦ, liftFunction_degreeΦ] at h
  exact_mod_cast h

theorem liftDegree_law (X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier)
    (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier) (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (k : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier)
    (hk : k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t)) :
    liftDegree hϖ (upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k) =
      detExponent hϖ m₁ := by
  have h := liftFunction_law hϖ (isLeviInvariant_degreeΦ (r := r) (t := t) hϖ) X m₁ m₂ k hk
  rw [liftFunction_degreeΦ] at h
  unfold degreeΦ at h
  exact_mod_cast h

/-- The first-block degree of `lower(Y)` is the depth of `Y`. -/
theorem liftDegree_lower (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    liftDegree hϖ (lower (r + 1) (t + 1) K.Carrier Y) = openCellDepth hϖ Y := by
  obtain ⟨u₁, hu₁, u₂, _, h⟩ := liftFunction_lower hϖ (isLeviInvariant_degreeΦ (r := r) (t := t) hϖ) Y
  rw [liftFunction_degreeΦ, degreeΦ, detExponent_unipotent_mul_torus hϖ hu₁] at h
  exact_mod_cast h

theorem liftDegree_open (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    liftDegree hϖ (blockWeyl (r + 1) (t + 1) K.Carrier *
        intertwiningUnipotent (r + 1) (t + 1) K.Carrier Y) = openCellDepth hϖ Y := by
  rw [blockWeyl_mul_intertwiningUnipotent,
    liftDegree_mul_integral hϖ _ _ (blockWeyl_mem_integralSubgroup K r t), liftDegree_lower]

end DetExponent

section Kernel

theorem intertwiningJacquetKernel_eq_conj (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    intertwiningJacquetKernel r t ψ Y = starRingEnd ℂ (ψ (Y (Fin.last t) 0) : ℂ) := by
  rw [intertwiningJacquetKernel_eq_neg_corner]
  have h := Base.conj_char_neg (ψ := ψ) (-(Y (Fin.last t) 0))
  rw [neg_neg] at h
  rw [h]
  rfl

theorem norm_intertwiningJacquetKernel (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ‖intertwiningJacquetKernel r t ψ Y‖ = 1 := by
  rw [intertwiningJacquetKernel_eq_neg_corner,
    HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex]

theorem intertwiningJacquetKernel_add_integral
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (Y Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (hZ : Z ∈ integralMatrices K (t + 1) (r + 1)) :
    intertwiningJacquetKernel r t ψ (Y + Z) = intertwiningJacquetKernel r t ψ Y := by
  have hψI := RankinSelberg.HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero K ψ hψ
  rw [intertwiningJacquetKernel_eq_conj, intertwiningJacquetKernel_eq_conj, Matrix.add_apply,
    AddChar.map_add_eq_mul, hψI.1 _ ((mem_integralMatrices_iff K _ _ Z).1 hZ _ _)]
  simp

end Kernel

section Shell

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

theorem jacquetIntegrandAt_one (hΦ : IsLeviInvariant Φ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    jacquetIntegrandAt ψ hϖ Φ 1 Y =
      intertwiningJacquetKernel r t ψ Y * liftFunction hϖ Φ (lower (r + 1) (t + 1) K.Carrier Y) := by
  rw [jacquetIntegrandAt_apply, mul_one, blockWeyl_mul_intertwiningUnipotent,
    liftFunction_mul_integral hϖ hΦ _ _ (blockWeyl_mem_integralSubgroup K r t)]

/-- The classes of depth `e`. -/
def shellSet (e : ℤ) :
    Set (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1)) :=
  {y | openCellDepth hϖ (Quotient.out y) = e}

theorem shellSet_finite (e : ℤ) : (shellSet (r := r) (t := t) hϖ e).Finite := by
  refine (finite_and_ncard_le K hϖ (t + 1) (r + 1) (D := e.toNat) _ ?_).1
  intro y hy i j
  have h := uniformizer_pow_depth_mul_mem hϖ (Quotient.out y) i j
  have hy' : openCellDepth hϖ (Quotient.out y) = e := hy
  have h0 := openCellDepth_nonneg hϖ (Quotient.out y)
  have he : ((e.toNat : ℕ) : ℤ) = openCellDepth hϖ (Quotient.out y) := by omega
  rw [he]
  exact h

/-- The classes of depth `e`, as a finite set. -/
def shellFinset (e : ℤ) :
    Finset (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1)) :=
  (shellSet_finite (r := r) (t := t) hϖ e).toFinset

theorem mem_shellFinset {e : ℤ}
    {y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1)} :
    y ∈ shellFinset hϖ e ↔ openCellDepth hϖ (Quotient.out y) = e := by
  rw [shellFinset, Set.Finite.mem_toFinset]
  rfl

theorem jacquetIntegrandAt_degreePiece_one (hΦ : IsLeviInvariant Φ) (e : ℤ)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) 1 Y =
      if openCellDepth hϖ Y = e then
        intertwiningJacquetKernel r t ψ Y * liftFunction hϖ Φ (lower (r + 1) (t + 1) K.Carrier Y)
      else 0 := by
  rw [jacquetIntegrandAt_one ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ), liftFunction_degreePiece,
    liftDegree_lower]
  split_ifs <;> simp

theorem isLatticePeriodic_jacquetIntegrandAt_one
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (hΦ : IsLeviInvariant Φ) :
    IsLatticePeriodic K (jacquetIntegrandAt ψ hϖ Φ 1) := by
  intro Y Z hZ
  rw [jacquetIntegrandAt_one ψ hϖ hΦ, jacquetIntegrandAt_one ψ hϖ hΦ,
    intertwiningJacquetKernel_add_integral ψ hψ Y Z hZ, liftFunction_lower_add_integral hϖ hΦ Y Z hZ]

/-- **The Jacquet function at `1` of a degree piece is a sum over the classes of that depth**,
for `ψ` of conductor `𝒪` and a Levi-invariant `Φ`. -/
theorem hasSum_jacquetFunction_degreePiece_one
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (hΦ : IsLeviInvariant Φ) (e : ℤ) :
    Integrable (jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) 1) (matrixHaar K (t + 1) (r + 1)) ∧
    jacquetFunction ψ hϖ (degreePiece hϖ e Φ) 1 =
      ∑ y ∈ shellFinset hϖ e, intertwiningJacquetKernel r t ψ (Quotient.out y) *
        liftFunction hϖ Φ (lower (r + 1) (t + 1) K.Carrier (Quotient.out y)) := by
  have hper := isLatticePeriodic_jacquetIntegrandAt_one ψ hϖ hψ (isLeviInvariant_degreePiece hϖ e hΦ)
  have hzero : ∀ y ∉ shellFinset hϖ e,
      jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) 1 (Quotient.out y) = 0 := by
    intro y hy
    rw [mem_shellFinset] at hy
    rw [jacquetIntegrandAt_degreePiece_one ψ hϖ hΦ, ite_eq_right_iff.2 fun h => absurd h hy]
  have hs : Summable fun y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
      integralMatrices K (t + 1) (r + 1) =>
        ‖jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) 1 (Quotient.out y)‖ :=
    summable_of_ne_finset_zero (s := shellFinset hϖ e) fun y hy => by rw [hzero y hy, norm_zero]
  obtain ⟨hint, hsum⟩ := integrable_and_hasSum_of_isLatticePeriodic K hper hs
  refine ⟨hint, ?_⟩
  have h2 : HasSum (fun y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
      integralMatrices K (t + 1) (r + 1) =>
        jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) 1 (Quotient.out y))
      (∑ y ∈ shellFinset hϖ e, jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) 1 (Quotient.out y)) :=
    hasSum_sum_of_ne_finset_zero hzero
  rw [jacquetFunction, hsum.unique h2]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [mem_shellFinset] at hy
  rw [jacquetIntegrandAt_degreePiece_one ψ hϖ hΦ, ite_eq_left_iff.2 fun h => absurd hy h]

theorem jacquetFunction_degreePiece_one_of_neg
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) (hΦ : IsLeviInvariant Φ) {e : ℤ}
    (he : e < 0) : jacquetFunction ψ hϖ (degreePiece hϖ e Φ) 1 = 0 := by
  rw [(hasSum_jacquetFunction_degreePiece_one ψ hϖ hψ hΦ e).2]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [mem_shellFinset] at hy
  have := openCellDepth_nonneg hϖ (Quotient.out y)
  omega

/-- **Termwise sums of degree pieces.** For `ψ` of conductor `𝒪` and Levi-invariant `Φ`, `Φᵢ`: if
`Φ = ∑ᵢ wᵢ Φᵢ` pointwise, then the same holds for the Jacquet functions at `1` of their degree-`e`
pieces. -/
theorem hasSum_jacquetFunction_degreePiece_one_of_hasSum {ι : Type*}
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    {Φs : ι → Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΦs : ∀ i, IsLeviInvariant (Φs i)) (hΦ : IsLeviInvariant Φ) (w : ι → ℂ)
    (h : ∀ m₁ m₂, HasSum (fun i => w i * Φs i m₁ m₂) (Φ m₁ m₂)) (e : ℤ) :
    HasSum (fun i => w i * jacquetFunction ψ hϖ (degreePiece hϖ e (Φs i)) 1)
      (jacquetFunction ψ hϖ (degreePiece hϖ e Φ) 1) := by
  simp only [fun i => (hasSum_jacquetFunction_degreePiece_one ψ hϖ hψ (hΦs i) e).2,
    (hasSum_jacquetFunction_degreePiece_one ψ hϖ hψ hΦ e).2, Finset.mul_sum]
  apply hasSum_sum
  intro y _
  have hy := (h (liftFirst K r t ⟨(exists_liftShape_parabolic_mul r t hϖ
      (lower (r + 1) (t + 1) K.Carrier (Quotient.out y))).choose,
      (exists_liftShape_parabolic_mul r t hϖ
        (lower (r + 1) (t + 1) K.Carrier (Quotient.out y))).choose_spec.1⟩)
    (liftSecond K r t ⟨(exists_liftShape_parabolic_mul r t hϖ
      (lower (r + 1) (t + 1) K.Carrier (Quotient.out y))).choose,
      (exists_liftShape_parabolic_mul r t hϖ
        (lower (r + 1) (t + 1) K.Carrier (Quotient.out y))).choose_spec.1⟩)).mul_left
    (intertwiningJacquetKernel r t ψ (Quotient.out y))
  convert hy using 2 with i
  · unfold liftFunction
    ring
  · rfl

end Shell

section Identity

variable {a : Fin (r + 1) → ℂˣ} {c : Fin (t + 1) → ℂˣ} {s : ℂ}
  {f : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier → ℂ}

/-- For `ψ` of conductor `𝒪` and a section with the target transformation law, the shell of
depth `D` sums to the Jacquet function at `1` of the degree-`D` piece. -/
theorem hasSum_shell_jacquetFunction (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (hf : IsOpenCellSection K ψ hϖ a c s f) (D : ℕ) :
    HasSum (fun y : {y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
        integralMatrices K (t + 1) (r + 1) // classDepth K hϖ y = D} =>
          openCellSummand K ψ f (Quotient.out y.1))
      (jacquetFunction ψ hϖ (degreePiece hϖ D (Base.fullΦ ψ hϖ a c s)) 1) := by
  have hΦ := Base.isLeviInvariant_fullΦ hϖ hψ a c s
  rw [(hasSum_jacquetFunction_degreePiece_one ψ hϖ hψ hΦ D).2]
  have hS : ∀ y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1),
      classDepth K hϖ y = D ↔ y ∈ shellFinset hϖ (D : ℤ) := by
    intro y
    rw [mem_shellFinset, classDepth]
    have := openCellDepth_nonneg hϖ (Quotient.out y)
    omega
  set S : Set (Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1)) :=
    {y | classDepth K hϖ y = D} with hSdef
  set g : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸ integralMatrices K (t + 1) (r + 1) → ℂ :=
    fun y => openCellSummand K ψ f (Quotient.out y) with hg
  have hzero : ∀ y ∉ shellFinset (r := r) (t := t) hϖ (D : ℤ), S.indicator g y = 0 := by
    intro y hy
    rw [Set.indicator_of_notMem]
    intro hy'
    exact hy ((hS y).1 hy')
  have h : HasSum (S.indicator g) (∑ y ∈ shellFinset (r := r) (t := t) hϖ (D : ℤ), S.indicator g y) :=
    hasSum_sum_of_ne_finset_zero hzero
  have h' : HasSum (g ∘ ((↑) : S → Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
      integralMatrices K (t + 1) (r + 1)))
      (∑ y ∈ shellFinset (r := r) (t := t) hϖ (D : ℤ), S.indicator g y) :=
    (hasSum_subtype_iff_indicator (f := g) (s := S)).2 h
  have hsum_eq : ∑ y ∈ shellFinset (r := r) (t := t) hϖ (D : ℤ),
      intertwiningJacquetKernel r t ψ (Quotient.out y) *
        liftFunction hϖ (Base.fullΦ ψ hϖ a c s) (lower (r + 1) (t + 1) K.Carrier (Quotient.out y)) =
      ∑ y ∈ shellFinset (r := r) (t := t) hϖ (D : ℤ), S.indicator g y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Set.indicator_of_mem (s := S) (show y ∈ S from (hS y).2 hy), hg]
    simp only
    rw [Base.openCellSummand_eq_lower hϖ hψ hf, intertwiningJacquetKernel_eq_conj, mul_comm]
  rw [hsum_eq]
  exact h'

/-- **The shell identities as identities of degree pieces**, for `ψ` of conductor `𝒪` and a
section with the target transformation law. -/
theorem shellIdentity_iff (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0)
    (hf : IsOpenCellSection K ψ hϖ a c s f) :
    ShellIdentity K ψ hϖ a c s f ↔ ∀ D : ℕ,
      jacquetFunction ψ hϖ (degreePiece hϖ D (Base.fullΦ ψ hϖ a c s)) 1 =
        shellCoefficient (pairParameter K.canonicalTopologicalData.residueCardinality a c s) D := by
  constructor
  · intro h D
    exact (hasSum_shell_jacquetFunction ψ hϖ hψ hf D).unique (h D)
  · intro h D
    rw [← h D]
    exact hasSum_shell_jacquetFunction ψ hϖ hψ hf D

end Identity

section PieceIntegrability

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

include hϖ in
theorem translatedLower_degreePiece_eq_zero (hΦ : IsLeviInvariant Φ) (e : ℤ)
    (μ₁ : Fin (r + 1) → ℤ) (h₂ : Langlands.GeneralLinear (t + 1) K.Carrier)
    (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier)
    (hY : openCellDepth hϖ Y ≠ e - ∑ i, μ₁ i) :
    translatedLower hϖ (degreePiece hϖ e Φ) (Iwasawa.torus ϖ μ₁) h₂ Y = 0 := by
  obtain ⟨u₁, hu₁, u₂, _, h⟩ := translatedLower_eq hϖ (isLeviInvariant_degreePiece hϖ e hΦ)
    (Iwasawa.torus ϖ μ₁) h₂ Y
  rw [h, degreePiece, detExponent_torus_mul_unipotent_mul_torus hϖ μ₁ _ hu₁, ite_eq_right_iff]
  intro h'
  exfalso
  apply hY
  rw [openCellDepth]
  omega

/-- **The Jacquet integrands of degree pieces of a Levi-invariant `Φ` are integrable at every
torus point.** -/
theorem integrable_jacquetIntegrandAt_degreePiece_torus (hΦ : IsLeviInvariant Φ) (e : ℤ)
    (μ : Fin ((r + 1) + (t + 1)) → ℤ) :
    Integrable (jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) (Iwasawa.torus ϖ μ))
      (matrixHaar K (t + 1) (r + 1)) := by
  have hΦe := isLeviInvariant_degreePiece hϖ e hΦ
  rw [torus_eq_swapRank_blockSum, jacquetIntegrandAt_swap ψ hϖ hΦe]
  set μ₂ : Fin (t + 1) → ℤ := fun j => μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (j.castAdd (r + 1)))
  set μ₁ : Fin (r + 1) → ℤ := fun i => μ (Fin.cast (Nat.add_comm (t + 1) (r + 1)) (i.natAdd (t + 1)))
  have hper := isLatticePeriodic_translatedLower hϖ hΦe (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂)
  have hzero : ∀ y ∉ shellFinset (r := r) (t := t) hϖ (e - ∑ i, μ₁ i),
      translatedLower hϖ (degreePiece hϖ e Φ) (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂)
        (Quotient.out y) = 0 := by
    intro y hy
    rw [mem_shellFinset] at hy
    exact translatedLower_degreePiece_eq_zero hϖ hΦ e μ₁ _ _ hy
  have hs : Summable fun y : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier ⧸
      integralMatrices K (t + 1) (r + 1) => ‖translatedLower hϖ (degreePiece hϖ e Φ)
        (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂) (Quotient.out y)‖ :=
    summable_of_ne_finset_zero (s := shellFinset (r := r) (t := t) hϖ (e - ∑ i, μ₁ i))
      fun y hy => by rw [hzero y hy, norm_zero]
  have hG := (integrable_and_hasSum_of_isLatticePeriodic K hper hs).1
  have hGc : Integrable (translatedLower hϖ (degreePiece hϖ e Φ)
      (Iwasawa.torus ϖ μ₁) (Iwasawa.torus ϖ μ₂) ∘
        rectangularConj (Iwasawa.torus ϖ μ₂) (Iwasawa.torus ϖ μ₁))
      (matrixHaar K (t + 1) (r + 1)) := by
    rw [← integrable_map_equiv, map_rectangularConj_padic K K.canonicalTopologicalData]
    exact hG.smul_measure_nnreal
  exact Integrable.bdd_mul (c := 1) hGc (continuous_intertwiningJacquetKernel ψ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => (norm_intertwiningJacquetKernel ψ Y).le)

/-- **The Jacquet integrands of degree pieces are integrable at every point**, for a
Levi-invariant `Φ` that is Levi-equivariant for the standard characters. -/
theorem integrable_jacquetIntegrandAt_degreePiece (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ r)
      (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t) Φ) (e : ℤ)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    Integrable (jacquetIntegrandAt ψ hϖ (degreePiece hϖ e Φ) g) (matrixHaar K (t + 1) (r + 1)) := by
  obtain ⟨u, hu, μ, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (n := r + 1 + t) hϖ g
  rw [jacquetIntegrandAt_mul_integral ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ) _ k hk]
  exact integrable_jacquetIntegrandAt_unipotent_mul ψ hϖ (isLeviInvariant_degreePiece hϖ e hΦ)
    (isLeviEquivariant_degreePiece hϖ e hθ) ⟨u, hu⟩ _
    (integrable_jacquetIntegrandAt_degreePiece_torus ψ hϖ hΦ e μ)

end PieceIntegrability

end Langlands.Shahidi.OpenCell
