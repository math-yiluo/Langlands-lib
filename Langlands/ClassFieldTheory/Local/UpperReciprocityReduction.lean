import Langlands.ClassFieldTheory.Local.UpperReciprocityStatement
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityExistenceProof

/-! Elementary consequences of the actual finite real unit-image equality. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.LocalClassField

universe u

/-- The integer image formula is a specialization of the nonnegative real formula. -/
theorem finiteReciprocityHigherUnitImages_of_realImages
    (himages : FiniteReciprocityRealUnitImages.{u}) :
    FiniteReciprocityHigherUnitImages.{u} := by
  intro p hp F T
  let := T.topology
  intro r hr L S
  letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  intro n
  simpa only [Nat.ceil_natCast] using
    himages p F T r hr L S (n : ℝ) (Nat.cast_nonneg n)

/-- Existence of reciprocity removes any candidate from the norm-level criterion. -/
theorem finiteAbelianNormUpperLevels_of_higherImages
    (himages : FiniteReciprocityHigherUnitImages.{u}) :
    FiniteAbelianNormUpperLevels.{u} := by
  intro p hp F T L S
  let := T.topology
  letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  intro n
  obtain ⟨r, hr, _⟩ := profiniteReciprocityExistenceUniqueness p F T
  rw [← himages p F T r hr L S n, Subgroup.map_eq_bot_iff,
    (hr.1.2.1 L).1]

/-- A finite character kills an image precisely when its composite kills the source. -/
theorem finiteCharacterUpperConductorLevels_of_realImages
    (himages : FiniteReciprocityRealUnitImages.{u}) :
    FiniteCharacterUpperConductorLevels.{u} := by
  intro p hp F T
  let := T.topology
  intro r hr L S χ
  letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  intro v hv
  rw [← himages p F T r hr L S v hv,
    T.multiplicativeConductor_le_iff_unitFiltration_le_ker]
  constructor
  · intro h σ hσ
    obtain ⟨a, ha, rfl⟩ := hσ
    exact h ha
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩

/-- The conductor-level criterion determines the last real upper break. -/
theorem finiteCharacterLastUpperBreak_of_conductorLevels
    (hlevels : FiniteCharacterUpperConductorLevels.{u}) :
    FiniteCharacterLastUpperBreak.{u} := by
  intro p hp F T
  let := T.topology
  intro r hr L S χ
  letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  intro n
  have hn : T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) ≤ n ↔
      ∀ σ ∈ Ramification.Padic.upperRamificationGroup S F.Carrier (n : ℝ),
        χ σ = 1 := by
    simpa only [Nat.ceil_natCast] using
      hlevels p F T r hr L S χ (n : ℝ) (Nat.cast_nonneg n)
  constructor
  · intro ha
    constructor
    · by_contra h
      push Not at h
      have hle := hn.mpr h
      omega
    · intro v hv
      apply (hlevels p F T r hr L S χ v ((Nat.cast_nonneg n).trans hv.le)).mp
      rw [ha]
      exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr hv)
  · rintro ⟨⟨σ, hσ, hχ⟩, hafter⟩
    have hgt : n < T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) :=
      Nat.lt_of_not_ge (fun h => hχ (hn.mp h σ hσ))
    have hle : T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) ≤ n + 1 := by
      have hv : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
      have h := (hlevels p F T r hr L S χ ((n + 1 : ℕ) : ℝ)
        (Nat.cast_nonneg _)).mpr (hafter _ hv)
      simpa only [Nat.ceil_natCast] using h
    omega

/-- All five finite assertions follow from the one arithmetic real image input. -/
theorem finiteUpperReciprocityTheorems_of_realImages
    (himages : FiniteReciprocityRealUnitImages.{u}) :
    FiniteUpperReciprocityTheorems.{u} := by
  have hhigher := finiteReciprocityHigherUnitImages_of_realImages himages
  have hlevels := finiteCharacterUpperConductorLevels_of_realImages himages
  exact ⟨hhigher, himages, finiteAbelianNormUpperLevels_of_higherImages hhigher,
    hlevels, finiteCharacterLastUpperBreak_of_conductorLevels hlevels⟩

/-- The real image clause carries exactly the information in the full finite
upper reciprocity conjunction. -/
def finiteUpperReciprocityRealEquiv :
    FiniteUpperReciprocityTheorems.{u} ≃ FiniteReciprocityRealUnitImages.{u} where
  toFun h := h.2.1
  invFun := finiteUpperReciprocityTheorems_of_realImages
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end Langlands.LocalClassField
