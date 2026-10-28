import Langlands.Representation.Classification.TemperedSmoothDualityStatement
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Category.Contragredient
import Langlands.Group.GL.CentralQuotientMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Analytic temperedness and the smooth contragredient: proof

The smooth contragredient carries the inverse central character, and its
coefficients against bidual vectors are the original coefficients composed with
inversion. Inversion pushes a Borel Haar measure on `GL_n(F) / Z` to a Borel Haar
measure, because that measure is right invariant. Admissible reflexivity then
gives both implications.
-/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uF uV

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

namespace UnitaryCentralCharacter

variable {ρ : Representation ℂ G V}

/-- The inverse unitary central character, acting on the smooth contragredient. -/
def contragredient (c : UnitaryCentralCharacter ρ) :
    UnitaryCentralCharacter (smoothContragredient ρ) where
  character := c.character⁻¹
  isOpen_ker := by
    have h : (c.character⁻¹).ker = c.character.ker := by
      ext z
      simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    rw [h]
    exact c.isOpen_ker
  norm_eq_one z := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, c.norm_eq_one, inv_one]
  acts z ℓ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change ℓ.val (ρ (z : G)⁻¹ v) = ((c.character⁻¹ z : ℂˣ) : ℂ) * ℓ.val v
    have hz : ((z : G)⁻¹) = ((z⁻¹ : Subgroup.center G) : G) := rfl
    rw [hz, c.acts, map_smul, map_inv, MonoidHom.inv_apply, smul_eq_mul]

theorem contragredient_character (c : UnitaryCentralCharacter ρ)
    (z : Subgroup.center G) :
    c.contragredient.character z = (c.character z)⁻¹ := rfl

end UnitaryCentralCharacter

variable {ρ : Representation ℂ G V}

/-- The coefficient of the smooth contragredient against the bidual image of a
vector is the original coefficient at the inverse element. -/
theorem matrixCoefficient_smoothContragredient_smoothBidual (hρ : IsSmooth ρ)
    (v : V) (ℓ : SmoothDual ρ) (g : G) :
    matrixCoefficient (smoothContragredient ρ)
        ((smoothBidual hρ v : SmoothDual (smoothContragredient ρ)) :
          Module.Dual ℂ (SmoothDual ρ)) ℓ g =
      matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v g⁻¹ := rfl

/-- On the central quotient, each absolute coefficient of the smooth
contragredient against a bidual vector is an original absolute coefficient
composed with inversion, for any choice of the two central-character data. -/
theorem UnitaryCentralCharacter.coefficientNorm_smoothBidual
    (c : UnitaryCentralCharacter ρ) (d : UnitaryCentralCharacter (smoothContragredient ρ))
    (hρ : IsSmooth ρ) (v : V) (ℓ : SmoothDual ρ) :
    d.coefficientNorm
        ((smoothBidual hρ v : SmoothDual (smoothContragredient ρ)) :
          Module.Dual ℂ (SmoothDual ρ)) ℓ =
      c.coefficientNorm (ℓ : Module.Dual ℂ V) v ∘ (·⁻¹) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => rfl

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

/-- Temperedness for the inverted measure gives temperedness of the smooth
contragredient for the original measure, when compact open subgroups are cofinal. -/
theorem IsTemperedModCenter.smoothContragredient_of_inv
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.inv.IsHaarMeasure]
    (h : IsTemperedModCenter ρ μ.inv) :
    IsTemperedModCenter (smoothContragredient ρ) μ := by
  obtain ⟨hρ, c, hc⟩ := h
  refine ⟨isAdmissible_smoothContragredient_of_compact_cofinal hcofinal ρ hρ,
    c.contragredient, ?_⟩
  intro Ψ ℓ ε hε
  obtain ⟨v, rfl⟩ := smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ Ψ
  rw [c.coefficientNorm_smoothBidual c.contragredient hρ.1 v ℓ]
  exact (hc ℓ v ε hε).comp_of_map measurable_inv.aemeasurable

end Generic

/-- Inversion maps a right-invariant Haar measure to a Haar measure. -/
theorem Measure.isHaarMeasure_inv_of_isMulRightInvariant {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    μ.inv.IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsMulLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Inversion pushes every Borel Haar measure on the actual central quotient of
`GL_n(F)` to a Borel Haar measure. -/
theorem centralQuotientHaar_inv (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.centralQuotientMeasurableSpace n
    ∀ (μ : Measure (GeneralLinear n F.Carrier ⧸
        Subgroup.center (GeneralLinear n F.Carrier))) [μ.IsHaarMeasure],
      μ.inv.IsHaarMeasure := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro μ _
  have := T.centralQuotientHaar_rightInvariant n μ
  exact Measure.isHaarMeasure_inv_of_isMulRightInvariant μ

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Forward implication: the smooth contragredient of a tempered representation
of `GL_n(F)` is tempered. -/
theorem IsTempered.smoothContragredient {T : F.TopologicalData}
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (h : T.IsTempered ρ) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup n
    T.IsTempered (smoothContragredient ρ) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro μ _
  have := T.centralQuotientHaar_inv n μ
  exact IsTemperedModCenter.smoothContragredient_of_inv
    (GeneralLinear.compactOpen_cofinal F T n) μ (h μ.inv)

end PadicField.TopologicalData

namespace Classification

/-- For admissible representations of `GL_n(F)`, analytic temperedness is
invariant under the smooth contragredient. -/
theorem padicTemperedSmoothDuality :
    PadicTemperedSmoothDualityStatement.{uF, uV} := by
  intro p _ F T n _
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ
  have hcofinal := GeneralLinear.compactOpen_cofinal F T n
  let e : ρ.Equiv (smoothContragredient (smoothContragredient ρ)) :=
    (smoothBidual hρ.1).ofBijective
      ⟨smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ.1,
        smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ⟩
  constructor
  · intro h
    exact (PadicField.TopologicalData.isTempered_iff_of_equiv e).mpr h.smoothContragredient
  · intro h
    exact h.smoothContragredient

end Classification

end Langlands
