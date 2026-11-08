import Langlands.Representation.RankinSelberg.HighlyRamified.DualAverage
import Langlands.Representation.RankinSelberg.HighlyRamified.DualWeight
import Langlands.Representation.RankinSelberg.HighlyRamified.InducedLevel
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly

/-!
# Model facts for the test representation

Facts about a coefficient model of a representation `τ` used on the test side of
Jacquet and Shalika (1985), §4.4:

* a finite algebraic average of right translates of a model function is a model function;
* a nonzero model function of an irreducible `τ` that is right invariant under an open
  subgroup comes from a nonzero invariant vector, so it gives a principal level vector;
* a nonzero model function transforming by `a` under the scalar `z` forces the central
  character value `ω_τ(z) = a`;
* determinant twists keep the functional (as the same linear form) and multiply model
  functions by the character; unramified twists keep genericity and the level, and
  multiply the central character by `ν^(m+1)`;
* two characters agreeing on the integral units differ by the `(m+1)`-th power of an
  unramified character.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uG uX uV

section Average

variable {X : Type uX} [MeasurableSpace X] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A finite algebraic integral of vectors of a submodule stays in the submodule. -/
theorem algebraicIntegral_mem (μ : Measure X) (M : Submodule ℂ V) (f : SimpleFunc X V)
    (hf : ∀ x, f x ∈ M) : AlgebraicIntegral.integral μ f ∈ M := by
  unfold AlgebraicIntegral.integral
  refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ ?_
  obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp hv
  exact hf x

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G]
variable {N : Subgroup G} {θ : N →* ℂˣ} {W : Type uV} [AddCommGroup W] [Module ℂ W]

/-- (T-i) The weighted inverse average `g ↦ ∫ w(k) W(g k⁻¹) dk` of a model function is
again a model function: it is a finite combination of right translates. -/
theorem exists_model_inverseAverage (ρ : Representation ℂ G W) (ℓ : functionals N θ ρ)
    (Φ : (coefficientModel ρ ℓ).toSubmodule) (μG : Measure G) (L : OpenSubgroup G)
    (hΦ : ∀ g l, l ∈ L → Φ.val.val (g * l) = Φ.val.val g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w) :
    ∃ Ψ : (coefficientModel ρ ℓ).toSubmodule,
      Ψ.val.val = inverseAverage μG Φ.val.val L hΦ w hw hwc := by
  let M : Submodule ℂ (G → ℂ) :=
    (coefficientModel ρ ℓ).toSubmodule.map (equivariantFunctions N θ).toSubmodule.subtype
  have hmem : inverseAverage μG Φ.val.val L hΦ w hw hwc ∈ M := by
    apply algebraicIntegral_mem
    intro k
    change w k • (fun g => Φ.val.val (g * k⁻¹)) ∈ M
    refine Submodule.smul_mem _ _ ?_
    exact ⟨(modelRepresentation ρ ℓ k⁻¹ Φ).val, (modelRepresentation ρ ℓ k⁻¹ Φ).property, rfl⟩
  obtain ⟨ψ, hψ, hφ⟩ := hmem
  exact ⟨⟨ψ, hψ⟩, hφ⟩

end Average

section Level

variable {G : Type uG} [Group G] {N : Subgroup G} {θ : N →* ℂˣ}
variable {W : Type uV} [AddCommGroup W] [Module ℂ W]

/-- A nonzero model function of an irreducible representation that is right invariant
under a subgroup `K` is the coefficient function of a nonzero `K`-fixed vector. -/
theorem fixedVectors_ne_bot_of_model (ρ : Representation ℂ G W) [Representation.IsIrreducible ρ]
    (ℓ : functionals N θ ρ) (Φ : (coefficientModel ρ ℓ).toSubmodule) (hΦ : Φ ≠ 0)
    (K : Subgroup G) (hK : ∀ g, ∀ k ∈ K, Φ.val.val (g * k) = Φ.val.val g) :
    Langlands.fixedVectors ρ K ≠ ⊥ := by
  obtain ⟨v, hv⟩ := modelMap_surjective ρ ℓ Φ
  have hinj : Function.Injective (modelMap ρ ℓ) := by
    rcases Representation.IsIrreducible.injective_or_eq_zero
        (k := ℂ) (V := W) (W := (coefficientModel ρ ℓ).toSubmodule)
        (ρ := ρ) (σ := modelRepresentation ρ ℓ) (modelMap ρ ℓ) with h | h
    · exact h
    · exfalso
      apply hΦ
      rw [← hv, h]
      rfl
  rw [Submodule.ne_bot_iff]
  refine ⟨v, ?_, fun h0 => hΦ (by rw [← hv, h0, map_zero])⟩
  simp only [Langlands.fixedVectors, Representation.mem_invariants]
  intro k
  apply hinj
  change modelMap ρ ℓ (ρ k.val v) = modelMap ρ ℓ v
  rw [(modelMap ρ ℓ).isIntertwining, hv]
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hK g k.val k.property

end Level

section Central

variable {F : Type uF} [Field F] {m : ℕ} {N : Subgroup (Langlands.GeneralLinear (m + 1) F)}
variable {θ : N →* ℂˣ} {W : Type uV} [AddCommGroup W] [Module ℂ W]

/-- A model function satisfies `W(g z) = ω_τ(z) W(g)` for scalar matrices `z`. -/
theorem model_mul_scalar (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) W)
    (ω : Fˣ →* ℂˣ) (hω : Classification.HasGLCentralCharacter F (m + 1) τ ω)
    (ℓ : functionals N θ τ) (Φ : (coefficientModel τ ℓ).toSubmodule) (z : Fˣ)
    (g : Langlands.GeneralLinear (m + 1) F) :
    Φ.val.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z) =
      (ω z : ℂ) * Φ.val.val g := by
  obtain ⟨v, rfl⟩ := modelMap_surjective τ ℓ Φ
  change ℓ.val (τ (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z) v) =
    (ω z : ℂ) * ℓ.val (τ g v)
  rw [map_mul, Module.End.mul_apply, hω z v, map_smul, map_smul, smul_eq_mul]

/-- (T-iii) If a nonzero model function transforms by `a` under the scalar `z`, then
the central character takes the value `a` at `z`. -/
theorem centralCharacter_eq_of_model (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) W)
    (ω : Fˣ →* ℂˣ) (hω : Classification.HasGLCentralCharacter F (m + 1) τ ω)
    (ℓ : functionals N θ τ) (Φ : (coefficientModel τ ℓ).toSubmodule) (hΦ : Φ ≠ 0)
    (z : Fˣ) (a : ℂ)
    (hz : ∀ g, Φ.val.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z) =
      a * Φ.val.val g) :
    (ω z : ℂ) = a := by
  have hne : ∃ g, Φ.val.val g ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hΦ (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨g, hg⟩ := hne
  have h := (model_mul_scalar τ ω hω ℓ Φ z g).symm.trans (hz g)
  exact mul_right_cancel₀ hg h

/-- (T-iii) A nonzero model function with `W(g z) = ω(z)⁻¹ W(g)` for all integral units
`z` forces `ω_τ = ω⁻¹` on the integral units. -/
theorem centralCharacter_eq_inv_of_model [ValuativeRel F]
    (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) W)
    (ωτ ω : Fˣ →* ℂˣ) (hωτ : Classification.HasGLCentralCharacter F (m + 1) τ ωτ)
    (ℓ : functionals N θ τ) (Φ : (coefficientModel τ ℓ).toSubmodule) (hΦ : Φ ≠ 0)
    (hz : ∀ z : Fˣ, IsIntegralUnit (z : F) → ∀ g,
      Φ.val.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z) =
        ((ω z : ℂ))⁻¹ * Φ.val.val g) :
    ∀ z : Fˣ, IsIntegralUnit (z : F) → ωτ z = (ω z)⁻¹ := by
  intro z hzu
  apply Units.ext
  rw [Units.val_inv_eq_inv_val]
  exact centralCharacter_eq_of_model τ ωτ hωτ ℓ Φ hΦ z _ (hz z hzu)

end Central

section Twist

variable {F : Type uF} [Field F] [TopologicalSpace F] {m : ℕ}
variable {W : Type uV} [AddCommGroup W] [Module ℂ W]

/-- (T-iv) Model transfer for determinant twists: the same linear form is a functional
for `τ ⊗ (χ ∘ det)`, and multiplying a model function by `χ(det g)` gives a model
function of the twist. -/
theorem exists_twist_model (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ)
    (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) W)
    (ℓ : glInverseFunctionals ψ m τ) :
    ∃ ℓχ : glInverseFunctionals ψ m (Langlands.twist (χ.comp determinant) τ),
      ℓχ.val = ℓ.val ∧ ∀ Φ : (coefficientModel τ ℓ).toSubmodule,
        ∃ Ψ : (coefficientModel (Langlands.twist (χ.comp determinant) τ) ℓχ).toSubmodule,
          ∀ g, Ψ.val.val g = (χ (determinant g) : ℂ) * Φ.val.val g :=
  ⟨twistFunctional _ _ (χ.comp determinant) (determinantCharacter_unipotent χ) τ ℓ, rfl,
    fun Φ => ⟨twistModelLinearMap _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) τ ℓ Φ, fun _ => rfl⟩⟩

end Twist

section Unramified

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- (T-ii) A nonzero model function of an irreducible `τ` that is right invariant under
`1 + ϖ^f M_(m+1)(O)` gives a principal level vector of level `f`. -/
theorem hasPrincipalLevelVector_of_model {m : ℕ} {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) W)
    (hτ : Representation.IsIrreducible τ)
    {N : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier)} {θ : N →* ℂˣ}
    (ℓ : functionals N θ τ) (Φ : (coefficientModel τ ℓ).toSubmodule) (hΦ : Φ ≠ 0) (f : ℕ)
    (hK : letI := F.canonicalTopologicalData.valuativeRel
      ∀ g, ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier m f,
        Φ.val.val (g * k) = Φ.val.val g) :
    HasPrincipalLevelVector F τ f :=
  letI := F.canonicalTopologicalData.valuativeRel
  haveI := hτ
  fixedVectors_ne_bot_of_model τ ℓ Φ hΦ _ hK

/-- An element of normalized absolute value one is an integral unit. -/
theorem isIntegralUnit_of_normalizedAbs_eq_one {x : F.Carrier}
    (hx : F.canonicalTopologicalData.normalizedAbs x = 1) :
    letI := F.canonicalTopologicalData.valuativeRel
    IsIntegralUnit x := by
  let := F.canonicalTopologicalData.valuativeRel
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, F.canonicalTopologicalData.normalizedAbs_zero] at hx
    exact zero_ne_one hx
  have hinv : F.canonicalTopologicalData.normalizedAbs x⁻¹ = 1 := by
    have h := F.canonicalTopologicalData.normalizedAbs_mul x x⁻¹
    rw [mul_inv_cancel₀ hx0, F.canonicalTopologicalData.normalizedAbs_one, hx, one_mul] at h
    exact h.symm
  exact ⟨hx0, (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers x).mp hx.le,
    (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers x⁻¹).mp hinv.le⟩

/-- (T-iv) Two characters of `Fˣ` agreeing on the integral units differ by the
`(m+1)`-th power of an unramified character: `ω₁ = ω₂ ν_y^(m+1)`. -/
theorem exists_unramified_pow_of_eq_on_units (ω₁ ω₂ : F.Carrierˣ →* ℂˣ)
    (h : letI := F.canonicalTopologicalData.valuativeRel
      ∀ z : F.Carrierˣ, IsIntegralUnit (z : F.Carrier) → ω₁ z = ω₂ z) (m : ℕ) :
    ∃ y : ℂˣ, ω₁ = ω₂ * F.canonicalTopologicalData.unramifiedCharacter y ^ (m + 1) := by
  set T := F.canonicalTopologicalData
  set χ : F.Carrierˣ →* ℂˣ := ω₂⁻¹ * ω₁ with hχ
  have hun : T.IsUnramifiedCharacter χ := by
    intro a ha
    have ha' : T.normalizedAbs (a : F.Carrier) = 1 := by
      have := congrArg (fun u : NNRealˣ => ((u : NNReal) : ℝ)) (MonoidHom.mem_ker.mp ha)
      simpa using this
    rw [MonoidHom.mem_ker, hχ, MonoidHom.mul_apply, MonoidHom.inv_apply,
      h a (isIntegralUnit_of_normalizedAbs_eq_one F ha'), inv_mul_cancel]
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((χ T.uniformizerUnit : ℂˣ) : ℂ)
    (Nat.succ_pos m)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero m)] at hy
    exact (χ T.uniformizerUnit).ne_zero hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  have hpow : T.unramifiedCharacter (Units.mk0 y hy0) ^ (m + 1) = χ := by
    have h1 : T.unramifiedCharacter (Units.mk0 y hy0) ^ (m + 1) =
        T.unramifiedCharacter (Units.mk0 y hy0 ^ (m + 1)) :=
      (map_pow T.unramifiedCharacterHom _ _).symm
    rw [h1, T.eq_unramifiedCharacter χ hun]
    congr 1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])
  rw [hpow, hχ]
  ext a
  simp

variable (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)

/-- (T-iv) Unramified determinant twists keep genericity, principal level vectors and the
central character up to `ν^(m+1)`. -/
theorem unramifiedTwist_properties {m : ℕ} {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) W)
    (hτ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ m τ)
    (ωτ : F.Carrierˣ →* ℂˣ) (hωτ : Classification.HasGLCentralCharacter F.Carrier (m + 1) τ ωτ)
    {f : ℕ} (hf : HasPrincipalLevelVector F τ f) (y : ℂˣ) :
    (letI := F.canonicalTopologicalData.topology;
      Whittaker.IsGeneric ψ m (Langlands.twist
        ((F.canonicalTopologicalData.unramifiedCharacter y).comp determinant) τ)) ∧
    HasPrincipalLevelVector F (Langlands.twist
        ((F.canonicalTopologicalData.unramifiedCharacter y).comp determinant) τ) f ∧
    Classification.HasGLCentralCharacter F.Carrier (m + 1)
      (Langlands.twist ((F.canonicalTopologicalData.unramifiedCharacter y).comp determinant) τ)
      (ωτ * F.canonicalTopologicalData.unramifiedCharacter y ^ (m + 1)) :=
  ⟨isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ
      (F.canonicalTopologicalData.unramifiedCharacterContinuous y) hτ,
    hasPrincipalLevelVector_twist_unramified F τ y hf,
    hasGLCentralCharacter_twist _ hωτ⟩

end Unramified

end Langlands.RankinSelberg.HighlyRamified
