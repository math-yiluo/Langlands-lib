import Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction
import Langlands.HarmonicAnalysis.RowSchwartzAction
import Langlands.Representation.Filtration.InvariantBilinearBounds
import Langlands.Group.GL.Mirabolic

/-! Conditional assembly for actual row Schwartz functions and coefficient models. -/

noncomputable section

namespace Langlands.RankinSelberg.TrilinearReduction

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

section InvariantSpaces

universe uG uS

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW} {S : Type uS}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup S] [Module ℂ S]

/-- The full space of invariant trilinear forms for a supplied test representation. -/
def invariantForms (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : Representation ℂ G S) (χ : G → ℂ) :
    Submodule ℂ (Form (V := V) (W := W) (S := S)) where
  carrier := {B | Invariant ρ σ a χ B}
  zero_mem' := by intro g v w φ; simp
  add_mem' := by
    intro B C hB hC g v w φ
    change B (ρ g v) (σ g w) (a g φ) + C (ρ g v) (σ g w) (a g φ) =
      χ g * (B v w φ + C v w φ)
    rw [hB, hC, mul_add]
  smul_mem' := by
    intro c B hB g v w φ
    change c * B (ρ g v) (σ g w) (a g φ) = χ g * (c * B v w φ)
    rw [hB, mul_left_comm]

/-- Restriction of an invariant form to a stable test subspace. -/
def restrictInvariant (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : Representation ℂ G S) (χ : G → ℂ) (K : Subrepresentation a) :
    invariantForms ρ σ a χ →ₗ[ℂ] invariantForms ρ σ K.toRepresentation χ where
  toFun B := ⟨restrict K.toSubmodule B.val, fun g v w φ => B.property g v w φ.val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end InvariantSpaces

section Field

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The pointwise invariance condition used in the published target. -/
def PointwiseInvariant
    (ρ : Representation ℂ (Langlands.GeneralLinear n F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear n F) W)
    (χ : Langlands.GeneralLinear n F → ℂ)
    (B : Form (V := V) (W := W) (S := SchwartzBruhat (Fin n → F))) : Prop :=
  ∀ g v w Φ Φg, (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) →
    B (ρ g v) (σ g w) Φg = χ g * B v w Φ

/-- Pointwise invariance is equivalent to invariance for the constructed action. -/
theorem invariant_iff_pointwise
    (ρ : Representation ℂ (Langlands.GeneralLinear n F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear n F) W)
    (χ : Langlands.GeneralLinear n F → ℂ)
    (B : Form (V := V) (W := W) (S := SchwartzBruhat (Fin n → F))) :
    Invariant ρ σ rowSchwartzRepresentation χ B ↔ PointwiseInvariant ρ σ χ B := by
  constructor
  · intro h g v w Φ Φg hΦg
    rw [(eq_rowTranslate_iff g Φ Φg).mpr hΦg]
    exact h g v w Φ
  · intro h g v w Φ
    exact h g v w Φ (rowTranslate g Φ) (fun _ => rfl)

/-- Source-carrier uniqueness descends to the actual coefficient models,
including models defined by zero functionals. -/
theorem coefficientModel_uniqueness_of_source
    (ρ : Representation ℂ (Langlands.GeneralLinear n F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear n F) W)
    {N N' : Subgroup (Langlands.GeneralLinear n F)}
    {θ : N →* ℂˣ} {θ' : N' →* ℂˣ}
    (ℓ : functionals N θ ρ) (ℓ' : functionals N' θ' σ)
    (χ : Langlands.GeneralLinear n F → ℂ)
    (h : ∀ B B' : Form (V := V) (W := W) (S := SchwartzBruhat (Fin n → F)),
      Invariant ρ σ rowSchwartzRepresentation χ B →
      Invariant ρ σ rowSchwartzRepresentation χ B' →
      B ≠ 0 → ∃ c : ℂ, B' = c • B) :
    ∀ B B' : Form (V := (coefficientModel ρ ℓ).toSubmodule)
      (W := (coefficientModel σ ℓ').toSubmodule) (S := SchwartzBruhat (Fin n → F)),
      PointwiseInvariant (modelRepresentation ρ ℓ) (modelRepresentation σ ℓ') χ B →
      PointwiseInvariant (modelRepresentation ρ ℓ) (modelRepresentation σ ℓ') χ B' →
      B ≠ 0 → ∃ c : ℂ, B' = c • B := by
  intro B B' hB hB' hB0
  apply uniqueness_of_surjective ρ σ (modelRepresentation ρ ℓ) (modelRepresentation σ ℓ')
    (modelMap ρ ℓ) (modelMap σ ℓ') (modelMap_surjective ρ ℓ) (modelMap_surjective σ ℓ')
    rowSchwartzRepresentation χ h B B'
  · exact (invariant_iff_pointwise _ _ _ _).mpr hB
  · exact (invariant_iff_pointwise _ _ _ _).mpr hB'
  · exact hB0

/-- A supplied Frobenius equivalence and full mirabolic bilinear bound give
uniqueness after restriction to test functions vanishing at zero. -/
theorem restriction_uniqueness_of_bilinear_equiv
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (χ : Langlands.GeneralLinear (n + 1) F → ℂ)
    (χP : mirabolic n F → ℂ)
    (e : invariantForms (S := (rowVanishingAtZero (F := F) (n := n + 1)).toSubmodule)
      ρ σ (rowVanishingAtZero (F := F) (n := n + 1)).toRepresentation χ ≃ₗ[ℂ]
      InvariantBilinear.forms (ρ.comp (mirabolic n F).subtype)
        (σ.comp (mirabolic n F).subtype) χP)
    (h : InvariantBilinear.length (ρ.comp (mirabolic n F).subtype)
      (σ.comp (mirabolic n F).subtype) χP ≤ 1)
    (B B' : Form (V := V) (W := W) (S := SchwartzBruhat (Fin (n + 1) → F)))
    (hB : Invariant ρ σ rowSchwartzRepresentation χ B)
    (hB' : Invariant ρ σ rowSchwartzRepresentation χ B')
    (hB0 : restrict rowVanishingAtZero.toSubmodule B ≠ 0) :
    ∃ c : ℂ, restrict rowVanishingAtZero.toSubmodule B' =
      c • restrict rowVanishingAtZero.toSubmodule B := by
  let C := restrictInvariant ρ σ rowSchwartzRepresentation χ rowVanishingAtZero ⟨B, hB⟩
  let C' := restrictInvariant ρ σ rowSchwartzRepresentation χ rowVanishingAtZero ⟨B', hB'⟩
  have hC : e C ≠ 0 := by
    intro hz
    have hc : C = 0 := e.injective (hz.trans e.map_zero.symm)
    exact hB0 (congrArg Subtype.val hc)
  obtain ⟨c, hc⟩ := InvariantBilinear.exists_smul_eq_of_length_le_one _ _ χP h
    (e C) (e C') hC
  have heq : C' = c • C := e.injective (by simpa only [map_smul] using hc)
  exact ⟨c, congrArg Subtype.val heq⟩

end Field

/-- The actual row-action reduction, with its two finite exceptional sets and
its weight-shifted Frobenius equivalence left as explicit mathematical inputs. -/
theorem source_uniqueness_of_mirabolic_bound
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (∀ s : ℂ, Nonempty
      (invariantForms (S := (rowVanishingAtZero (F := F.Carrier) (n := n + 1)).toSubmodule)
        ρ σ (rowVanishingAtZero (F := F.Carrier) (n := n + 1)).toRepresentation
        (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) ≃ₗ[ℂ]
      InvariantBilinear.forms (ρ.comp (mirabolic n F.Carrier).subtype)
        (σ.comp (mirabolic n F.Carrier).subtype)
        (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)))) →
    (∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      InvariantBilinear.length (ρ.comp (mirabolic n F.Carrier).subtype)
        (σ.comp (mirabolic n F.Carrier).subtype)
        (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (1 - s)) ≤ 1) →
    (∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
        (∀ g v w, β (ρ g v) (σ g w) =
          determinantWeight (normalizedAbsoluteValue T) g (-s) * β v w) → β = 0) →
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      ∀ B B' : Form (V := V) (W := W)
        (S := SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        Invariant ρ σ rowSchwartzRepresentation
          (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B →
        Invariant ρ σ rowSchwartzRepresentation
          (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B' →
        B ≠ 0 → ∃ c : ℂ, B' = c • B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hFrob hmir hbil
  apply uniqueness_outside_finite_union ρ σ rowSchwartzRepresentation
    (fun s g => determinantWeight (normalizedAbsoluteValue T) g (-s))
    rowEvaluationAtZero (fun g φ => rowEvaluationAtZero_translate g φ)
    (spectralPoint T.residueCardinality) hbil
  obtain ⟨E, hE⟩ := hmir
  refine ⟨E, ?_⟩
  intro s hs B B' hB hB' hB0
  obtain ⟨e⟩ := hFrob s
  exact restriction_uniqueness_of_bilinear_equiv ρ σ _ _ e (hE s hs) B B' hB hB' hB0

/-- The parent target follows from a uniform source-carrier uniqueness bound.
The bound is an outstanding representation-theoretic input, not a proved fact. -/
theorem equalRankTrilinearUniqueness_of_source
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)
    (hsource :
      let := T.topology
      let := T.valuativeRel
      let := T.localField
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          ∀ B B' : Form (V := V) (W := W)
            (S := SchwartzBruhat (Fin (n + 1) → F.Carrier)),
            Invariant π σ rowSchwartzRepresentation
              (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B →
            Invariant π σ rowSchwartzRepresentation
              (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s)) B' →
            B ≠ 0 → ∃ c : ℂ, B' = c • B) :
    EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ π σ hπ hσ ℓ ℓ'
  obtain ⟨E, hE⟩ := hsource ψ V W π σ hπ hσ
  refine ⟨E, ?_⟩
  intro s hs B B' hB hB' hB0
  exact coefficientModel_uniqueness_of_source π σ ℓ ℓ'
    (fun g => determinantWeight (normalizedAbsoluteValue T) g (-s))
    (hE s hs) B B' hB hB' hB0

end Langlands.RankinSelberg.TrilinearReduction
