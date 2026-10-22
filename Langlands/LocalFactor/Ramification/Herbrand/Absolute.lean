import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Langlands.ClassFieldTheory.Local.Galois

/-!
# Actual absolute upper ramification groups

Intersect restriction preimages over all actual finite Galois subextensions.
The abelianized group is the image under the continuous quotient projection.
-/

noncomputable section

namespace Langlands.Ramification.Padic

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- An actual finite Galois intermediate field, packaged without changing its
carrier, operations, or specified algebra maps. The ambient universe is independent. -/
abbrev finiteGaloisPadicField {Ω : Type v} [Field Ω] [Algebra F.Carrier Ω]
    [Algebra (Padic p) Ω] [IsScalarTower (Padic p) F.Carrier Ω]
    (L : FiniteGaloisIntermediateField F.Carrier Ω) : PadicField.{v} p where
  Carrier := L
  finiteDimensional := FiniteDimensional.trans (Padic p) F.Carrier L

/-- The same actual subfield of the algebraic closure as a p-adic field. -/
abbrev absoluteFiniteExtension
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    PadicField.{u} p := finiteGaloisPadicField F L

/-- Actual restriction, continuous for the existing Krull topologies. -/
def absoluteFiniteRestriction
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    Field.absoluteGaloisGroup F.Carrier →ₜ* Gal(L/F.Carrier) where
  toMonoidHom := AlgEquiv.restrictNormalHom (F := F.Carrier)
    (K₁ := AlgebraicClosure F.Carrier) L
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField

/-- Absolute upper numbering as the intersection of all finite restriction preimages. -/
def absoluteUpperRamificationGroup (v : ℝ) :
    Subgroup (Field.absoluteGaloisGroup F.Carrier) :=
  ⨅ L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
    (canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v).comap
      (absoluteFiniteRestriction F L).toMonoidHom

/-- Exact elementwise meaning of the intersection. -/
theorem mem_absoluteUpperRamificationGroup_iff (v : ℝ)
    (σ : Field.absoluteGaloisGroup F.Carrier) :
    σ ∈ absoluteUpperRamificationGroup F v ↔
      ∀ L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
        absoluteFiniteRestriction F L σ ∈
          canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v := by
  simp only [absoluteUpperRamificationGroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

/-- Finite evaluation explicitly uses the canonical integer-ring lower group
at the ceiling of the inverse Herbrand parameter. -/
theorem mem_absoluteUpperRamificationGroup_iff_lower (v : ℝ)
    (σ : Field.absoluteGaloisGroup F.Carrier) :
    σ ∈ absoluteUpperRamificationGroup F v ↔
      ∀ L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
        absoluteFiniteRestriction F L σ ∈
          lowerRamificationGroupInt (absoluteFiniteExtension F L).canonicalTopologicalData
            F.Carrier
            ⌈herbrandPsi (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier v⌉ :=
  mem_absoluteUpperRamificationGroup_iff F v σ

/-- Every element evaluates into each finite upper group. -/
theorem absoluteUpperRamificationGroup_le_comap (v : ℝ)
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    absoluteUpperRamificationGroup F v ≤
      (canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v).comap
        (absoluteFiniteRestriction F L).toMonoidHom :=
  iInf_le _ L

/-- Image containment is elementary; equality is a separate arithmetic theorem. -/
theorem absoluteUpperRamificationGroup_map_restriction_le (v : ℝ)
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    (absoluteUpperRamificationGroup F v).map (absoluteFiniteRestriction F L).toMonoidHom ≤
      canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v :=
  (Subgroup.map_le_iff_le_comap).mpr (absoluteUpperRamificationGroup_le_comap F v L)

instance absoluteUpperRamificationGroup_normal (v : ℝ) :
    (absoluteUpperRamificationGroup F v).Normal := by
  apply Subgroup.normal_iInf_normal
  intro L
  exact Subgroup.Normal.comap
    (upperRamificationGroup_normal
      (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier v) _

/-- Closedness follows from continuous restriction into finite discrete groups. -/
theorem absoluteUpperRamificationGroup_isClosed (v : ℝ) :
    IsClosed (absoluteUpperRamificationGroup F v : Set (Field.absoluteGaloisGroup F.Carrier)) := by
  unfold absoluteUpperRamificationGroup
  rw [Subgroup.coe_iInf]
  apply isClosed_iInter
  intro L
  exact (isClosed_discrete _).preimage (absoluteFiniteRestriction F L).continuous

/-- The real-indexed absolute filtration is decreasing. -/
theorem absoluteUpperRamificationGroup_antitone : Antitone (absoluteUpperRamificationGroup F) := by
  intro v w hvw σ hσ
  rw [mem_absoluteUpperRamificationGroup_iff] at hσ ⊢
  intro L
  exact upperRamificationGroup_antitone
    (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier hvw (hσ L)

@[simp] theorem absoluteUpperRamificationGroup_neg_one :
    absoluteUpperRamificationGroup F (-1) = ⊤ := by
  simp [absoluteUpperRamificationGroup, canonicalUpperRamificationGroup]

/-- The full group is retained for indices below Serre's domain as well. -/
theorem absoluteUpperRamificationGroup_of_le_neg_one {v : ℝ} (hv : v ≤ -1) :
    absoluteUpperRamificationGroup F v = ⊤ := by
  apply top_unique
  simpa using absoluteUpperRamificationGroup_antitone F hv

/-- The local abelianized upper group is the actual image under the published
continuous closed-commutator quotient projection. -/
def localAbelianUpperRamificationGroup (v : ℝ) :
    Subgroup (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
  (absoluteUpperRamificationGroup F v).map
    (LocalClassField.localAbelianGaloisProjection F).toMonoidHom

/-- Exact witness characterization of the abelianized image. -/
theorem mem_localAbelianUpperRamificationGroup_iff (v : ℝ)
    (a : Field.absoluteGaloisGroupAbelianization F.Carrier) :
    a ∈ localAbelianUpperRamificationGroup F v ↔
      ∃ σ ∈ absoluteUpperRamificationGroup F v,
        LocalClassField.localAbelianGaloisProjection F σ = a :=
  Subgroup.mem_map

/-- Expanding the image witnesses exposes all finite Galois conditions. -/
theorem mem_localAbelianUpperRamificationGroup_iff_finite (v : ℝ)
    (a : Field.absoluteGaloisGroupAbelianization F.Carrier) :
    a ∈ localAbelianUpperRamificationGroup F v ↔
      ∃ σ : Field.absoluteGaloisGroup F.Carrier,
        (∀ L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
          absoluteFiniteRestriction F L σ ∈
            canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v) ∧
        LocalClassField.localAbelianGaloisProjection F σ = a := by
  simp only [mem_localAbelianUpperRamificationGroup_iff,
    mem_absoluteUpperRamificationGroup_iff]

theorem localAbelianUpperRamificationGroup_antitone :
    Antitone (localAbelianUpperRamificationGroup F) := by
  intro v w hvw
  exact Subgroup.map_mono (absoluteUpperRamificationGroup_antitone F hvw)

end Langlands.Ramification.Padic
