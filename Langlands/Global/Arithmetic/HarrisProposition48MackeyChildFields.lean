import Langlands.Global.Arithmetic.HarrisProposition48StepSelection
import Langlands.Global.Arithmetic.HarrisPlaceFromEmbedding
import Langlands.Global.Arithmetic.CMSubfield
import Langlands.Global.AdeleQuotientCompactProof

/-! # The fields and auxiliary places of an actual raw Mackey child -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension

namespace MackeyChild

variable (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
  (a : Q.L ≃ₐ[Q.E] Q.L)

/-- The actual compositum, regarded as an intermediate field over `D`. -/
abbrev inducingField : IntermediateField D Q.L :=
  IntermediateField.extendScalars (show D ≤ Q.mackeyField D a from le_sup_left)

/-- The actual normal closure of the compositum over `D` inside the parent closure. -/
abbrev closure : IntermediateField D Q.L :=
  IntermediateField.normalClosure D (inducingField Q D a) Q.L

variable {Q D a}

theorem isNormalClosure [IsGalois Q.E Q.L] :
    IsNormalClosure D (inducingField Q D a) (closure Q D a) := by
  have : IsGalois D Q.L := IsGalois.tower_top_of_isGalois Q.E D Q.L
  infer_instance

theorem degree_lt (hp : (Module.finrank Q.E D).Prime) :
    Module.finrank D (closure Q D a) < Q.inductionDegree := by
  have hle : Module.finrank D (closure Q D a) ≤ Module.finrank D Q.L :=
    IntermediateField.finrank_le_of_le_right (show closure Q D a ≤ ⊤ from le_top)
      |>.trans_eq IntermediateField.finrank_top'
  apply hle.trans_lt
  rw [Proposition48Problem.inductionDegree, ← Module.finrank_mul_finrank Q.E D Q.L]
  simpa only [one_mul] using
    (mul_lt_mul_of_pos_right hp.one_lt (Module.finrank_pos (R := D) (M := Q.L)))

variable (Q D a)

/-- The image of the parent's split imaginary quadratic field inside the child base. -/
def quadraticField : IntermediateField ℚ D :=
  Q.K₀.map (IsScalarTower.toAlgHom ℚ Q.E D)

theorem quadraticField_split (h : IsSplitImaginaryQuadratic Q.p Q.K₀) :
    IsSplitImaginaryQuadratic Q.p (quadraticField Q D) := by
  obtain ⟨hr, hC, v₁, v₂, hne, h₁, h₂⟩ := h
  let e : Q.K₀ ≃ₐ[ℚ] quadraticField Q D :=
    IntermediateField.equivMap Q.K₀ (IsScalarTower.toAlgHom ℚ Q.E D)
  let eₚ := finitePlaceEquiv e.symm.toRingEquiv
  let : Algebra Q.K₀ (quadraticField Q D) := e.toRingEquiv.toRingHom.toAlgebra
  refine ⟨e.toLinearEquiv.finrank_eq.symm.trans hr,
    isTotallyComplex_of_algebra Q.K₀ (quadraticField Q D),
    eₚ v₁, eₚ v₂, eₚ.injective.ne hne, ?_, ?_⟩
  · simpa only [eₚ, finitePlaceEquiv_mem, map_natCast] using h₁
  · simpa only [eₚ, finitePlaceEquiv_mem, map_natCast] using h₂

theorem quadraticField_range :
    Set.range (fun x : quadraticField Q D ↦ ((x : D) : Q.L)) =
      Set.range (fun x : Q.K₀ ↦ algebraMap Q.E Q.L (x : Q.E)) := by
  rw [Set.range_comp' (fun x : D ↦ (x : Q.L)), Subtype.range_val, quadraticField,
    IntermediateField.coe_map, Set.image_image]
  rw [Set.range_comp' (algebraMap Q.E Q.L), Subtype.range_val]
  rfl

/-- The restriction of the selected top place to the child base. -/
abbrev basePlace : FinitePlace D := Q.Ps.vTilde.under (𝓞 D)

/-- The restriction of the selected top place to the inducing field. -/
abbrev inducingPlace : FinitePlace (inducingField Q D a) :=
  Q.Ps.vTilde.under (𝓞 (inducingField Q D a))

/-- The restriction of the selected top place to the relative normal closure. -/
abbrev closurePlace : FinitePlace (closure Q D a) :=
  Q.Ps.vTilde.under (𝓞 (closure Q D a))

instance basePlace_liesOver : (basePlace Q D).asIdeal.LiesOver Q.Ps.v.asIdeal :=
  MackeyCompletion.under_liesOver Q.Ps.v Q.Ps.vTilde D

instance inducingPlace_liesOver :
    (inducingPlace Q D a).asIdeal.LiesOver (basePlace Q D).asIdeal := by
  constructor
  exact (Ideal.under_under Q.Ps.vTilde.asIdeal).symm

instance closurePlace_liesOver' :
    (closurePlace Q D a).asIdeal.LiesOver (inducingPlace Q D a).asIdeal := by
  constructor
  exact (Ideal.under_under Q.Ps.vTilde.asIdeal).symm

instance closurePlace_liesOver :
    (closurePlace Q D a).asIdeal.LiesOver (basePlace Q D).asIdeal :=
  Ideal.LiesOver.trans _ (inducingPlace Q D a).asIdeal _

theorem prime_mem_basePlace (hp : (Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal) :
    (Q.p : 𝓞 D) ∈ (basePlace Q D).asIdeal := by
  have h := (Ideal.LiesOver.over (P := (basePlace Q D).asIdeal) (p := Q.Ps.v.asIdeal))
  rwa [h, Ideal.mem_under, map_natCast] at hp

theorem uniqueAbove_basePlace (h : HasUniquePlaceAbove Q.L Q.Ps.v) :
    HasUniquePlaceAbove (closure Q D a) (basePlace Q D) :=
  MackeyCompletion.uniqueAboveBase (MackeyCompletion.uniqueAboveMiddle h (basePlace Q D))

theorem uniqueAbove_conjPlace [IsCMField D] [IsCMField (closure Q D a)]
    (h : HasUniquePlaceAbove Q.L Q.Ps.v) :
    HasUniquePlaceAbove (closure Q D a) (conjPlace D (basePlace Q D)) :=
  FieldRealization.hasUniquePlaceAbove_finitePlaceEquiv (IsCMField.complexConj D).toRingEquiv
    (IsCMField.complexConj (closure Q D a)).toRingEquiv
    (fun x => (CMRealization.algebraMap_complexConj (M := closure Q D a) x).symm)
    (uniqueAbove_basePlace Q D a h)

end MackeyChild
end Langlands.Global.Harris
