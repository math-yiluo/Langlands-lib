import Langlands.AllFieldBZ.Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllFieldBZ.Group.GL.BlockIwahoriBasis
import Langlands.AllFieldBZ.Representation.Category.Contragredient
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.AllFieldBZ.Group.GL.UnramifiedCharacter
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwistSupplement
import Langlands.AllFieldBZ.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof

/-!
# All-field port of `Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof`

The proof follows the unbounded matrix coefficient argument of Zelevinsky 1980,
Proposition 1.11.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability

open Langlands.Classification

universe uF uG uV uW

section GeneralLinearLevel

open Langlands.GeneralLinear

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- With a block Iwahori factorization `K = L M U` and a weakly contracting
block scalar `A`, every `k A^m` with `k ∈ K` lies in `(P ∩ K) A^m K`. -/
theorem exists_mul_blockScalar_pow {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization_allFieldBZ T K →
    ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting_allFieldBZ T a →
    ∀ (m : ℕ) (k : K), ∃ q : B.parabolic F.Carrier, ∃ k' : K,
      (q : GeneralLinear n F.Carrier) ∈ K ∧
      (k : GeneralLinear n F.Carrier) * B.blockScalar F.Carrier a ^ m =
        q * B.blockScalar F.Carrier a ^ m * k' := by
  let _ := T.topology
  intro K hK a ha m k
  have ham : B.IsWeaklyContracting_allFieldBZ T (a ^ m) := by
    induction m with
    | zero => simp [B.isWeaklyContracting_one_allFieldBZ T]
    | succ m ih =>
      rw [pow_succ]
      exact Langlands.GeneralLinear.BlockShape.IsWeaklyContracting_allFieldBZ.mul B T ih ha
  obtain ⟨⟨l, x, u⟩, hlxu⟩ := hK.1.2 k⁻¹
  have hval : (k : GeneralLinear n F.Carrier)⁻¹ = l.val * x.val * u.val := by
    have h := congrArg Subtype.val hlxu
    simpa using h.symm
  have hk : (k : GeneralLinear n F.Carrier) = u.val⁻¹ * x.val⁻¹ * l.val⁻¹ := by
    rw [← inv_inv (k : GeneralLinear n F.Carrier), hval]
    simp only [mul_inv_rev, mul_assoc]
  have hAm : B.blockScalar F.Carrier a ^ m = B.blockScalar F.Carrier (a ^ m) :=
    (map_pow _ _ _).symm
  have hl : (B.blockScalar F.Carrier a ^ m)⁻¹ * l.val⁻¹ * B.blockScalar F.Carrier a ^ m ∈
      B.iwahoriLower F.Carrier K.toSubgroup := by
    rw [hAm]
    exact (hK.2 (a ^ m) ham).2 _ ((B.iwahoriLower F.Carrier K.toSubgroup).inv_mem l.property)
  have hq : u.val⁻¹ * x.val⁻¹ ∈ B.parabolic F.Carrier :=
    (B.parabolic F.Carrier).mul_mem
      (Langlands.Classification.TwoBlockExponentNonUnitarizability.unipotentSubgroup_le_parabolic B F.Carrier
        ((B.unipotentSubgroup F.Carrier).inv_mem u.property.2))
      (Langlands.Classification.TwoBlockExponentNonUnitarizability.leviSubgroup_le_parabolic B F.Carrier
        ((B.leviSubgroup F.Carrier).inv_mem x.property.2))
  refine ⟨⟨_, hq⟩, ⟨_, hl.1⟩, K.mul_mem (K.inv_mem u.property.1) (K.inv_mem x.property.1), ?_⟩
  change (k : GeneralLinear n F.Carrier) * _ = u.val⁻¹ * x.val⁻¹ * _ *
    ((B.blockScalar F.Carrier a ^ m)⁻¹ * l.val⁻¹ * B.blockScalar F.Carrier a ^ m)
  rw [hk]
  group

/-- Normalized parabolic induction of an admissible representation `τ` of the
block Levi is not unitarizable when a vector `e` with `ℓ e ≠ 0` is an
eigenvector of a weakly contracting block scalar with eigenvalue (including
`δ_P^{1/2}`) of norm greater than one. -/
theorem not_isUnitarizable_normalizedParabolicInduced {n : ℕ} (B : BlockShape n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (B.Levi F.Carrier) W) :
    letI := T.topology
    IsAdmissible τ →
    ∀ (a : Fin B.length → F.Carrierˣ), B.IsWeaklyContracting_allFieldBZ T a →
    ∀ (e : W) (c : ℂ), 1 < ‖c‖ →
      twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier))
        (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)) e = c • e →
    ∀ ℓ : Module.Dual ℂ W, ℓ e ≠ 0 →
      ¬ IsUnitarizable (T.normalizedParabolicInduced B τ) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup n
  intro hτ a ha e c hc hA ℓ hℓ
  have hσP : IsAdmissible
      (twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier))) :=
    (isAdmissible_twist_iff (T.parabolicHalfModulus B) _
      (T.isOpen_ker_parabolicHalfModulus B)).mpr
      ((Langlands.AllFieldBZ.Parabolic.leviInflationAdmissibility F T B W τ).mpr hτ)
  have hadm : IsAdmissible (Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier)))) :=
    Langlands.AllFieldBZ.Parabolic.normalizedInductionAdmissibility F T B W τ hτ
  obtain ⟨H, hH⟩ := hσP.1 e
  obtain ⟨O, hO, hOH⟩ := isOpen_induced_iff.mp H.isOpen
  have h1O : (1 : GeneralLinear n F.Carrier) ∈ O := by
    have h1 : (1 : B.parabolic F.Carrier) ∈ (H : Set (B.parabolic F.Carrier)) := H.one_mem
    rw [← hOH] at h1
    exact h1
  obtain ⟨K, hKc, hKO, hfacK⟩ :=
    B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization_allFieldBZ T (hO.mem_nhds h1O)
  have he : e ∈ fixedVectors
      (twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier)))
      (Induction.conjOpenSubgroup (B.parabolic F.Carrier) K 1).toSubgroup := by
    rw [fixedVectors, Representation.mem_invariants]
    intro q
    have hqK : ((q : B.parabolic F.Carrier) : GeneralLinear n F.Carrier) ∈ K := by
      have h := Induction.mem_conjOpenSubgroup.mp q.property
      simpa using h
    have hqH : (q : B.parabolic F.Carrier) ∈ H := by
      have h : (q : B.parabolic F.Carrier) ∈ Subtype.val ⁻¹' O := hKO hqK
      rw [hOH] at h
      exact h
    exact hH ⟨q, hqH⟩
  let _ : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
  have _ : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
  have _ := T.generalLinearLocallyCompactSpace n
  exact Langlands.Classification.TwoBlockExponentNonUnitarizability.not_isUnitarizable_of_growth (B.parabolic F.Carrier) _
    (Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T n) hadm MeasureTheory.Measure.haar K hKc _
    (B.blockScalar F.Carrier a) c hc e ℓ hℓ
    (Langlands.Classification.TwoBlockExponentNonUnitarizability.eval_doubleCosetSection_mul_pow (B.parabolic F.Carrier) _ K hKc e he
      (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)) c hA
      (exists_mul_blockScalar_pow T B hfacK ha))

end GeneralLinearLevel

section TwoBlock

open Langlands.GeneralLinear

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A scalar matrix `z` acts on `ν^t ρ`, for an irreducible unitarizable smooth
representation `ρ` of `GL_r(F)`, by a scalar of norm `|z|^(r t)`. -/
theorem exists_segmentFactor_scalar_eigen {r : ℕ}
    (ρ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ρ.representation.IsIrreducible → IsUnitarizable ρ.representation →
    ∀ (t : ℝ) (z : F.Carrierˣ), ∃ x : ρ, x ≠ 0 ∧ ∃ ω : ℂ,
      ‖ω‖ = T.normalizedAbs (z : F.Carrier) ^ ((r : ℝ) * t) ∧
      (T.determinantPowerTwist ρ t).representation (scalar z) x = ω • x := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup r
  intro hirr hunit t z
  have hadm : IsAdmissible ρ.representation :=
    (Langlands.AllFieldBZ.CuspidalSupport.cuspidalEmbedding F T r ρ hirr).1
  obtain ⟨χ⟩ := unitarizableCentralCharacter ρ.representation hadm hirr hunit
  have _ := hirr
  have _ : Nontrivial ρ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear r F.Carrier))
      ρ.representation.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : ρ)
  refine ⟨x, hx, (T.determinantPowerCharacter r t (scalar z) : ℂ) *
    (χ.character (scalarToCenter z) : ℂ), ?_, ?_⟩
  · rw [norm_mul, χ.norm_eq_one, mul_one, T.norm_determinantPowerCharacter_scalar]
  · change (T.determinantPowerCharacter r t (scalar z) : ℂ) •
      ρ.representation ((scalarToCenter z : Subgroup.center (GeneralLinear r F.Carrier)) :
        GeneralLinear r F.Carrier) x = _
    rw [χ.acts, smul_smul]

end TwoBlock

end Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear Langlands.Classification.TwoBlockExponentNonUnitarizability

universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- For positive rank `k`, an irreducible unitarizable smooth representation `ρ`
of `GL_k(F)` and a real `s < -k/2`, the normalized product `ν^s ρ × ν^(-s) ρ`
is not unitarizable. -/
theorem twoBlockLargeExponentNonUnitarizable :
    TwoBlockLargeExponentNonUnitarizable.{uF, uV} F T := by
  let _ := T.topology
  intro k hk ρ hirr hunit s hs
  let B := Shahidi.twoBlocks k k hk hk
  let A := Langlands.Classification.twoBlockFactors hk hk ρ ρ
  let u : Fin B.length → ℝ := ![s, -s]
  have hirrA : ∀ i, (A i).representation.IsIrreducible := by
    intro i
    fin_cases i
    · exact hirr
    · exact hirr
  have hunitA : ∀ i, IsUnitarizable (A i).representation := by
    intro i
    fin_cases i
    · exact hunit
    · exact hunit
  let ϖ : F.Carrierˣ := T.uniformizerUnit
  let a : Fin B.length → F.Carrierˣ := ![ϖ, 1]
  choose x hx ω hω hxω using fun i =>
    Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability.exists_segmentFactor_scalar_eigen T (A i) (hirrA i) (hunitA i) (u i) (a i)
  let σ := fun i => (T.twistedBlocks B A u i).representation
  let y : ∀ i, T.twistedBlocks B A u i := x
  have hy : ∀ i, y i ≠ 0 := hx
  have hadmσ : ∀ i, IsAdmissible (σ i) := fun i =>
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_determinantPowerCharacter _ _)).mpr
      (Langlands.AllFieldBZ.CuspidalSupport.cuspidalEmbedding F T _ (A i) (hirrA i)).1
  obtain ⟨ℓ, hℓ⟩ := Langlands.Classification.TwoBlockExponentNonUnitarizability.exists_dual_tprod_eq_one y hy
  let c : ℂ := (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) * ∏ i, ω i
  have hA : twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
      (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a))
        (PiTensorProduct.tprod ℂ y) = c • PiTensorProduct.tprod ℂ y := by
    change (T.parabolicHalfModulus B
        (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)) : ℂ) •
      B.blockTensor σ (B.leviProjection F.Carrier
        (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)))
          (PiTensorProduct.tprod ℂ y) = _
    rw [T.parabolicHalfModulus_section, B.leviProjection_section, B.blockTensor_tprod]
    have hcomp : (fun i => σ i (B.blockScalarLevi F.Carrier a i) (y i)) =
        fun i => ω i • y i := by
      funext i
      exact hxω i
    rw [hcomp, MultilinearMap.map_smul_univ, smul_smul]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have hϖ : T.normalizedAbs (ϖ : F.Carrier) = (T.residueCardinality : ℝ)⁻¹ := by
    rw [T.uniformizerUnit_val, T.normalizedAbs_uniformizer, zpow_neg_one]
  have hϖ0 : 0 < T.normalizedAbs (ϖ : F.Carrier) := by
    rw [hϖ]
    exact inv_pos.mpr (zero_lt_one.trans hq)
  have hϖ1 : T.normalizedAbs (ϖ : F.Carrier) < 1 := by
    rw [hϖ]
    exact inv_lt_one_of_one_lt₀ hq
  have ha : B.IsWeaklyContracting_allFieldBZ T a := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · change T.normalizedAbs ((ϖ * (1 : F.Carrierˣ)⁻¹ : F.Carrierˣ) : F.Carrier) ≤ 1
      rw [inv_one, mul_one]
      exact hϖ1.le
    · simp at hij
    · exact absurd hij (lt_irrefl _)
  have hω0 : ‖ω 0‖ = T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * s) := hω 0
  have hω1 : ‖ω 1‖ = 1 := by
    rw [hω 1]
    change T.normalizedAbs ((1 : F.Carrierˣ) : F.Carrier) ^ _ = 1
    rw [Units.val_one, T.normalizedAbs_one, Real.one_rpow]
  have hmod : ((T.leviModulus B (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) =
      T.normalizedAbs (ϖ : F.Carrier) ^ (k * k) := by
    have h := T.leviModulus_twoBlocks hk hk (B.blockScalarLevi F.Carrier a)
    have h0 : T.determinantNorm k (B.blockScalarLevi F.Carrier a 0) =
        T.normalizedAbsUnits ϖ ^ k :=
      T.determinantNorm_scalar k ϖ
    have h1 : T.determinantNorm k (B.blockScalarLevi F.Carrier a 1) = 1 := by
      change T.determinantNorm k (GeneralLinear.scalar (n := k) (1 : F.Carrierˣ)) = 1
      rw [map_one, map_one]
    rw [h0, h1, one_pow, div_one, ← pow_mul] at h
    change ((T.leviModulus (Shahidi.twoBlocks k k hk hk)
      (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) = _
    rw [h]
    simp
  have hnorm : ‖c‖ = Real.sqrt (T.normalizedAbs (ϖ : F.Carrier) ^ (k * k)) *
      T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * s) := by
    have hprod : ∏ i, ω i = ω 0 * ω 1 := Fin.prod_univ_two ω
    simp only [c, norm_mul, hprod, hω0, hω1, mul_one, T.leviHalfModulus_apply,
      Complex.norm_real, Real.coe_sqrt, hmod]
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp : Real.sqrt (T.normalizedAbs (ϖ : F.Carrier) ^ (k * k)) *
      T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * s) =
      T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * ((k : ℝ) / 2 + s)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hϖ0.le,
      ← Real.rpow_add hϖ0]
    congr 1
    push_cast
    ring
  have hc : 1 < ‖c‖ := by
    rw [hnorm, hexp]
    apply Real.one_lt_rpow_of_pos_of_lt_one_of_neg hϖ0 hϖ1
    apply mul_neg_of_pos_of_neg hk0
    linarith
  exact Langlands.AllFieldBZ.Classification.TwoBlockExponentNonUnitarizability.not_isUnitarizable_normalizedParabolicInduced T B (B.blockTensor σ)
    (FiniteTensor.isAdmissible_external σ hadmσ) a ha (PiTensorProduct.tprod ℂ y) c hc hA ℓ
    (by rw [hℓ]; exact one_ne_zero)

end Langlands.AllFieldBZ.Classification
