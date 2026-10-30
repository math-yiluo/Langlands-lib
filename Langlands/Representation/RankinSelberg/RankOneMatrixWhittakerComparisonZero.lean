import Langlands.Representation.Hecke.TestFunction
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.LocalField.Normalization.Proof

/-!
# Rank-one `I₁ = I₃` at actual rank one

The `n = 0` branch of `RankOneMatrixWhittakerComparisonStatement`: a GL₁
equal-rank/Tate bridge. The subgroup `N₁` is trivial, so every compatible
quotient measure is the transported normalized Haar measure of `GL₁`; the
inverse Whittaker functions of the trivial character are the constants; vector
and `1 × 1` matrix test functions correspond through the last row; and the
complex shift `jpssShift 0` vanishes.

The file also proves two facts used by both branches: a nonzero standard
functional of a representation of Whittaker type gives the whole all-functional
Whittaker set, and at rank one every linear form is an inverse-character
functional.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section FunctionalLine

/-- In a complex line every vector is a multiple of any nonzero vector. -/
theorem exists_eq_smul_of_linearEquiv_complex {M : Type*} [AddCommGroup M] [Module ℂ M]
    (e : M ≃ₗ[ℂ] ℂ) {m₀ : M} (h₀ : m₀ ≠ 0) (m : M) : ∃ c : ℂ, m = c • m₀ := by
  have he : e m₀ ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr h₀
  refine ⟨e m / e m₀, e.injective ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ he]

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For a representation of Whittaker type, the all-functional Whittaker set is the
coefficient model of any specified nonzero standard functional. -/
theorem whittakerSet_eq_of_isOfWhittakerType {ψ : UnitaryAdditiveCharacter F} {n : ℕ}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    whittakerSet ψ n σ = (coefficientModel σ ℓ).toSubmodule := by
  obtain ⟨e⟩ := hσ.2.2
  refine whittakerSet_eq_coefficientModel ℓ fun ℓ' => ?_
  exact exists_eq_smul_of_linearEquiv_complex e (fun h => hℓ (congrArg Subtype.val h)) ℓ'

/-- In rank one every linear form is also an inverse-character functional. -/
theorem glInverseFunctionals_rankOne (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V) :
    glInverseFunctionals ψ 0 π = ⊤ := by
  have : Subsingleton (upperUnipotent (0 + 1) F) := upperUnipotent_one_subsingleton
  apply top_unique
  intro ℓ _ u v
  have hu : u = 1 := Subsingleton.elim _ _
  subst hu
  simp

/-- The inverse Whittaker functions of the trivial character of `GL₁` are exactly
the constant functions. -/
theorem mem_inverseWhittakerSet_rankOneCharacter_one_iff (ψ : UnitaryAdditiveCharacter F)
    (W' : InverseWhittakerFunctions ψ 0) :
    W' ∈ inverseWhittakerSet ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)) ↔
      ∃ c : ℂ, ∀ g, W'.val g = c := by
  constructor
  · rintro ⟨ℓ', v, rfl⟩
    refine ⟨ℓ'.val v, fun g => ?_⟩
    change ℓ'.val (rankOneCharacter (1 : Fˣ →* ℂˣ) g v) = ℓ'.val v
    simp [rankOneCharacter, characterRepresentation, twist]
  · rintro ⟨c, hc⟩
    refine ⟨⟨LinearMap.id, ?_⟩, c, ?_⟩
    · rw [glInverseFunctionals_rankOne]
      trivial
    · apply Subtype.ext
      funext g
      change rankOneCharacter (1 : Fˣ →* ℂˣ) g c = W'.val g
      rw [hc g]
      simp [rankOneCharacter, characterRepresentation, twist]

end FunctionalLine

section TestFunctions

/-- Pull back a Schwartz–Bruhat function along a homeomorphism. -/
def schwartzBruhatComap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (Φ : SchwartzBruhat Y) : SchwartzBruhat X :=
  Hecke.TestFunction.pullback e Φ

@[simp] theorem schwartzBruhatComap_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (Φ : SchwartzBruhat Y) (x : X) :
    schwartzBruhatComap e Φ x = Φ (e x) := rfl

variable (F : Type uF) [Field F] [TopologicalSpace F]

/-- A `1 × 1` matrix is its last (and only) row. -/
def oneByOneRow : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F ≃ₜ (Fin (0 + 1) → F) where
  toFun M := M (Fin.last 0)
  invFun v := fun _ => v
  left_inv M := by
    funext i j
    obtain rfl : i = Fin.last 0 := Fin.ext (by omega)
    rfl
  right_inv _ := rfl
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id

variable {F}

theorem lastRow_eq_oneByOneRow (g : Langlands.GeneralLinear (0 + 1) F) :
    lastRow g = oneByOneRow F g.val := rfl

/-- The constant inverse Whittaker function of `GL₁` with value `c`. -/
def constInverseWhittaker (ψ : UnitaryAdditiveCharacter F) (c : ℂ) :
    InverseWhittakerFunctions ψ 0 :=
  ⟨fun _ => c, by
    intro u g
    have : Subsingleton (upperUnipotent (0 + 1) F) := upperUnipotent_one_subsingleton
    obtain rfl : u = 1 := Subsingleton.elim _ _
    simp⟩

@[simp] theorem constInverseWhittaker_apply (ψ : UnitaryAdditiveCharacter F) (c : ℂ)
    (g : Langlands.GeneralLinear (0 + 1) F) :
    (constInverseWhittaker ψ c).val g = c := rfl

end TestFunctions

section RankOneIntegrals

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (0 + 1) F)]
  [MeasurableSpace (upperUnipotent (0 + 1) F)] [BorelSpace (upperUnipotent (0 + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]

/-- Every compatible quotient measure on `N₁ \ GL₁` is the transported normalized
Haar measure of `GL₁`. -/
theorem eq_rankOneQuotientHaar_of_isCompatible (μ : Measure (LeftUnipotentQuotient 0 F))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F) (generalLinearHaar F 0)
      (unipotentHaar F 0) μ) :
    μ = rankOneQuotientHaar F :=
  (unipotentQuotientHaar_unique F 0 μ hμ).trans (unipotentQuotientHaar_zero F)

variable {F} (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

omit [MeasurableSpace (upperUnipotent (0 + 1) F)] [BorelSpace (upperUnipotent (0 + 1) F)] in
/-- At rank one the equal-rank integral is an integral over `GL₁` itself. -/
theorem equalRankIntegral_rankOneQuotientHaar (W : WhittakerFunctions ψ 0)
    (W' : InverseWhittakerFunctions ψ 0) (Φ : SchwartzBruhat (Fin (0 + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ abv (rankOneQuotientHaar F) W W' Φ s =
      ∫ g, equalRankFunction ψ abv W W' Φ s g ∂generalLinearHaar F 0 :=
  integral_rankOneQuotientHaar F _

omit [MeasurableSpace (upperUnipotent (0 + 1) F)] [BorelSpace (upperUnipotent (0 + 1) F)] in
/-- At rank one equal-rank convergence is integrability over `GL₁` itself. -/
theorem equalRankConverges_rankOneQuotientHaar_iff (W : WhittakerFunctions ψ 0)
    (W' : InverseWhittakerFunctions ψ 0) (Φ : SchwartzBruhat (Fin (0 + 1) → F)) (s : ℂ) :
    EqualRankConverges ψ abv (rankOneQuotientHaar F) W W' Φ s ↔
      Integrable (equalRankFunction ψ abv W W' Φ s) (generalLinearHaar F 0) :=
  integrable_map_equiv rankOneQuotientHomeomorph.symm.toMeasurableEquiv _

end RankOneIntegrals

section Comparison

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (0 + 1) F)]
  [MeasurableSpace (upperUnipotent (0 + 1) F)] [BorelSpace (upperUnipotent (0 + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The `n = 0` comparison at the level of value sets: the rank-one character zeta
values of `σ × 1` are exactly the shifted matrix–Whittaker values of the coefficient
model of `ℓ`, for every compatible quotient measure. -/
theorem characterZetaValues_one_zero_eq (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V}
    (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
    (ℓ : glFunctionals ψ 0 σ) (hℓ : ℓ.val ≠ 0)
    (μ : Measure (LeftUnipotentQuotient 0 F))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F) (generalLinearHaar F 0)
      (unipotentHaar F 0) μ) :
    characterZetaValues q ψ abv μ (1 : Fˣ →* ℂˣ) 0 σ =
      GodementJacquet.whittakerRationalValues q ψ abv (generalLinearHaar F 0) σ ℓ := by
  obtain rfl := eq_rankOneQuotientHaar_of_isCompatible F μ hμ
  have hshift : ∀ s : ℂ, s + GodementJacquet.jpssShift 0 = s := fun s => by
    simp [GodementJacquet.jpssShift]
  ext R
  constructor
  · rintro ⟨W, hW, W', hW', Φ, ⟨a, ha⟩, hR⟩
    rw [whittakerSet_eq_of_isOfWhittakerType hσ ℓ hℓ] at hW
    obtain ⟨c, hc⟩ := (mem_inverseWhittakerSet_rankOneCharacter_one_iff ψ W').1 hW'
    let w : (glCoefficientModel ψ 0 σ ℓ).toSubmodule :=
      ⟨c • W, Submodule.smul_mem _ c hW⟩
    have hfun : ∀ s : ℂ,
        GodementJacquet.matrixIntegrand abv (schwartzBruhatComap (oneByOneRow F) Φ)
            (s + GodementJacquet.jpssShift 0) (glModelFunction ψ 0 σ ℓ w) =
          equalRankFunction ψ abv W W' Φ s := by
      intro s
      funext g
      rw [hshift]
      simp only [GodementJacquet.matrixIntegrand, equalRankFunction, glModelFunction, w,
        schwartzBruhatComap_apply, hc, ← lastRow_eq_oneByOneRow, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨schwartzBruhatComap (oneByOneRow F) Φ, w, ⟨⟨a, fun s hs => ?_⟩, ?_⟩⟩
    · rw [GodementJacquet.MatrixConverges, hfun]
      exact (equalRankConverges_rankOneQuotientHaar_iff ψ abv W W' Φ s).1 (ha s hs)
    · convert hR using 1
      funext s
      rw [GodementJacquet.matrixIntegral, hfun, equalRankIntegral_rankOneQuotientHaar]
  · rintro ⟨Φ', w, ⟨a, ha⟩, hR⟩
    let Φ := schwartzBruhatComap (oneByOneRow F).symm Φ'
    have hfun : ∀ s : ℂ,
        GodementJacquet.matrixIntegrand abv Φ' (s + GodementJacquet.jpssShift 0)
            (glModelFunction ψ 0 σ ℓ w) =
          equalRankFunction ψ abv w.val (constInverseWhittaker ψ 1) Φ s := by
      intro s
      funext g
      rw [hshift]
      simp only [GodementJacquet.matrixIntegrand, equalRankFunction, glModelFunction, Φ,
        schwartzBruhatComap_apply, lastRow_eq_oneByOneRow, Homeomorph.symm_apply_apply,
        constInverseWhittaker_apply]
      ring
    refine ⟨w.val, coefficientModel_subset_whittakerSet ℓ w.property,
      constInverseWhittaker ψ 1,
      (mem_inverseWhittakerSet_rankOneCharacter_one_iff ψ _).2 ⟨1, fun _ => rfl⟩, Φ,
      ⟨a, fun s hs => ?_⟩, ?_⟩
    · rw [equalRankConverges_rankOneQuotientHaar_iff, ← hfun]
      exact ha s hs
    · convert hR using 1
      funext s
      rw [GodementJacquet.matrixIntegral, hfun, equalRankIntegral_rankOneQuotientHaar]

end Comparison

section Padic

/-- The `n = 0` case of `RankOneMatrixWhittakerComparisonStatement`, in exactly the
form of the statement's body at `n = 0`. -/
theorem rankOneMatrixWhittakerComparison_zero (p : ℕ) [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (0 + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient 0 F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
    IsOfWhittakerType 0 (standardCharacter ψ 0) σ →
    ∀ ℓ : glFunctionals ψ 0 σ, ℓ.val ≠ 0 →
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier 0)],
    ∀ μ : Measure (LeftUnipotentQuotient 0 F.Carrier),
      IsCompatible (upperUnipotent (0 + 1) F.Carrier)
        (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ →
      zetaSpan (characterZetaValues F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μ
          (1 : F.Carrierˣ →* ℂˣ) 0 σ) =
        GodementJacquet.Padic.jpssI3 F ψ σ ℓ := by
  intro hσ ℓ hℓ _ μ hμ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (0 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
  exact congrArg zetaSpan (characterZetaValues_one_zero_eq _ ψ _ hσ ℓ hℓ μ hμ)

end Padic

end Langlands.RankinSelberg
