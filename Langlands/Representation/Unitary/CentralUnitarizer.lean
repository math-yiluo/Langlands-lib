import Langlands.Group.PositiveCharacterExtension
import Langlands.Representation.Twist.RealPower
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Positive twists making the actual central character unitary
-/

noncomputable section

open scoped NNReal

namespace Langlands

universe uG uA uV

namespace PositiveCharacter

variable {H : Type*} [Group H]

/-- The modulus of a complex-unit-valued character as a positive character. -/
def normCharacter (χ : H →* ℂˣ) : H →* ℝ≥0ˣ :=
  (Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom).comp χ

@[simp]
theorem normCharacter_apply (χ : H →* ℂˣ) (h : H) :
    (normCharacter χ h : ℝ≥0) = ‖(χ h : ℂ)‖₊ := rfl

theorem isOpen_ker_normCharacter [TopologicalSpace H] [SeparatelyContinuousMul H]
    (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H)) :
    IsOpen ((normCharacter χ).ker : Set H) := by
  apply Subgroup.isOpen_mono (H₁ := χ.ker) ?_ hχ
  intro h hh
  change χ h = 1 at hh
  change Units.map (nnnormHom : ℂ →*₀ ℝ≥0).toMonoidHom (χ h) = 1
  rw [hh, map_one]

@[simp]
theorem norm_positiveUnitsToComplex (x : ℝ≥0ˣ) :
    ‖(positiveUnitsToComplex x : ℂ)‖ = ((x : ℝ≥0) : ℝ) := by
  rw [coe_positiveUnitsToComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (x : ℝ≥0).coe_nonneg]

end PositiveCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [CommGroup A]

namespace CentralUnitarization

private def centerMap (q : G →* A) : Subgroup.center G →* A :=
  q.comp (Subgroup.center G).subtype

private theorem normCharacter_ker_le (q : G →* A)
    (hK : IsCompact ((centerMap q).ker : Set (Subgroup.center G)))
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G))) :
    (centerMap q).ker ≤ (PositiveCharacter.normCharacter χ).ker := by
  intro z hz
  exact PositiveCharacter.eq_one_on_compact (PositiveCharacter.normCharacter χ)
    (PositiveCharacter.isOpen_ker_normCharacter χ hχ) (centerMap q).ker hK ⟨z, hz⟩

/-- Descend the modulus of the actual central character to the central image.
The compact kernel is killed by the positive character with open kernel. -/
def normOnImage (q : G →* A)
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G))) :
    (q.comp (Subgroup.center G).subtype).range →* ℝ≥0ˣ :=
  (centerMap q).rangeRestrict.liftOfSurjective
    (centerMap q).rangeRestrict_surjective
    ⟨PositiveCharacter.normCharacter χ, by
      simpa only [MonoidHom.ker_rangeRestrict] using normCharacter_ker_le q hK χ hχ⟩

@[simp]
theorem normOnImage_apply (q : G →* A)
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G))) (z : Subgroup.center G) :
    normOnImage q hK χ hχ ((q.comp (Subgroup.center G).subtype).rangeRestrict z) =
      PositiveCharacter.normCharacter χ z := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Pull back the inverse of the unique positive extension of the central
modulus through the supplied abelian quotient. -/
def centralUnitarizer (q : G →* A)
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    [(q.comp (Subgroup.center G).subtype).range.FiniteIndex]
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G))) : G →* ℝ≥0ˣ :=
  ((PositiveCharacter.finiteIndexExtension
    (q.comp (Subgroup.center G).subtype).range (normOnImage q hK χ hχ)).comp q)⁻¹

@[simp]
theorem centralUnitarizer_restrict (q : G →* A)
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    [(q.comp (Subgroup.center G).subtype).range.FiniteIndex]
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G))) (z : Subgroup.center G) :
    centralUnitarizer q hK χ hχ z = (PositiveCharacter.normCharacter χ z)⁻¹ := by
  change (PositiveCharacter.finiteIndexExtension
    (q.comp (Subgroup.center G).subtype).range (normOnImage q hK χ hχ)
    ((q.comp (Subgroup.center G).subtype).rangeRestrict z : A))⁻¹ = _
  rw [PositiveCharacter.finiteIndexExtension_restrict, normOnImage_apply]

theorem isOpen_ker_centralUnitarizer (q : G →* A)
    (hq : IsOpen (q.ker : Set G))
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    [(q.comp (Subgroup.center G).subtype).range.FiniteIndex]
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G))) :
    IsOpen ((centralUnitarizer q hK χ hχ).ker : Set G) := by
  apply Subgroup.isOpen_mono (H₁ := q.ker) ?_ hq
  intro g hg
  change q g = 1 at hg
  change (PositiveCharacter.finiteIndexExtension _ _ (q g))⁻¹ = 1
  rw [hg, map_one, inv_one]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A positive open-kernel twist with a unitary scalar action on the full
actual center. No topology on the representation carrier is used. -/
def unitaryCentralCharacter (q : G →* A)
    (hq : IsOpen (q.ker : Set G))
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    [(q.comp (Subgroup.center G).subtype).range.FiniteIndex]
    (ρ : Representation ℂ G V) (χ : Subgroup.center G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center G)))
    (hact : ∀ (z : Subgroup.center G) (v : V), ρ z v = (χ z : ℂ) • v) :
    UnitaryCentralCharacter
      (twist (positiveUnitsToComplex.comp (centralUnitarizer q hK χ hχ)) ρ) where
  character := ((positiveUnitsToComplex.comp (centralUnitarizer q hK χ hχ)).comp
    (Subgroup.center G).subtype) * χ
  isOpen_ker := by
    have hu : IsOpen
        ((positiveUnitsToComplex.comp (centralUnitarizer q hK χ hχ)).ker : Set G) := by
      apply Subgroup.isOpen_mono (H₁ := (centralUnitarizer q hK χ hχ).ker) ?_
        (isOpen_ker_centralUnitarizer q hq hK χ hχ)
      intro g hg
      change centralUnitarizer q hK χ hχ g = 1 at hg
      change positiveUnitsToComplex (centralUnitarizer q hK χ hχ g) = 1
      rw [hg, map_one]
    apply Subgroup.isOpen_mono (H₁ :=
      ((positiveUnitsToComplex.comp (centralUnitarizer q hK χ hχ)).comp
        (Subgroup.center G).subtype).ker ⊓ χ.ker) ?_
      ((hu.preimage continuous_subtype_val).inter hχ)
    intro z hz
    change positiveUnitsToComplex (centralUnitarizer q hK χ hχ z) * χ z = 1
    have hz1 := hz.1
    have hz2 := hz.2
    change positiveUnitsToComplex (centralUnitarizer q hK χ hχ z) = 1 at hz1
    change χ z = 1 at hz2
    rw [hz1, hz2, one_mul]
  norm_eq_one := by
    intro z
    change ‖(positiveUnitsToComplex (centralUnitarizer q hK χ hχ z) : ℂ) *
      (χ z : ℂ)‖ = 1
    rw [norm_mul, PositiveCharacter.norm_positiveUnitsToComplex,
      centralUnitarizer_restrict]
    rw [Units.val_inv_eq_inv_val, NNReal.coe_inv,
      PositiveCharacter.normCharacter_apply, coe_nnnorm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (χ z).ne_zero)
  acts := by
    intro z v
    change (positiveUnitsToComplex (centralUnitarizer q hK χ hχ z) : ℂ) • ρ z v =
      ((positiveUnitsToComplex (centralUnitarizer q hK χ hχ z) : ℂ) * (χ z : ℂ)) • v
    rw [hact, smul_smul]

/-- The actual Schur character provides the scalar input for this construction
for any irreducible admissible complex representation. -/
theorem exists_positive_twist_unitaryCentralCharacter (q : G →* A)
    (hq : IsOpen (q.ker : Set G))
    (hK : IsCompact ((q.comp (Subgroup.center G).subtype).ker :
      Set (Subgroup.center G)))
    [(q.comp (Subgroup.center G).subtype).range.FiniteIndex]
    (ρ : Representation ℂ G V) (ha : IsAdmissible ρ) (hi : Representation.IsIrreducible ρ) :
    ∃ ν : G →* ℝ≥0ˣ, IsOpen (ν.ker : Set G) ∧
      Nonempty (UnitaryCentralCharacter (twist (positiveUnitsToComplex.comp ν) ρ)) := by
  obtain ⟨χ, ⟨hlc, hact⟩, _⟩ := admissibleSchur_centralCharacter ρ ha hi
  have hχ : IsOpen (χ.ker : Set (Subgroup.center G)) := hlc.isOpen_fiber 1
  exact ⟨centralUnitarizer q hK χ hχ, isOpen_ker_centralUnitarizer q hq hK χ hχ,
    ⟨unitaryCentralCharacter q hq hK ρ χ hχ hact⟩⟩

end CentralUnitarization
end Langlands
