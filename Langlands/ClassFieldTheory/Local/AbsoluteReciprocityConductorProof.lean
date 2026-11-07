import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityStatement
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityCompletionProof

/-! Conductor consequences of actual absolute reciprocity unit images. -/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- Restriction of actual reciprocity identifies each unit level with its absolute upper image. -/
def reciprocityUnitLevelEquiv (himages : AbsoluteReciprocityRealUnitImages.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier),
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (v : ℝ), 0 ≤ v →
          T.unitFiltration ⌈v⌉₊ ≃*
            Ramification.Padic.localAbelianUpperRamificationGroup F v := by
  letI := T.topology
  intro r hr v hv
  exact ((T.unitFiltration ⌈v⌉₊).equivMapOfInjective r.toMonoidHom
    (profiniteReciprocityCompletion p F T r hr).1).trans
      (MulEquiv.subgroupCongr (himages p F T r hr v hv))

@[simp]
theorem reciprocityUnitLevelEquiv_coe (himages : AbsoluteReciprocityRealUnitImages.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier)
      (hr : GeometricProfiniteReciprocityRelation F T r) (v : ℝ) (hv : 0 ≤ v)
      (x : T.unitFiltration ⌈v⌉₊),
      (reciprocityUnitLevelEquiv himages F T r hr v hv x :
        Field.absoluteGaloisGroupAbelianization F.Carrier) = r x := by
  let := T.topology
  intro r hr v hv x
  rfl

/-- Every continuous complex quasicharacter has the asserted absolute conductor-level criterion. -/
theorem absoluteQuasicharacterConductorLevels_of_realImages
    (himages : AbsoluteReciprocityRealUnitImages.{u}) :
    AbsoluteQuasicharacterConductorLevels.{u} := by
  intro p hp F T
  let := T.topology
  intro r hr χ v hv
  rw [← himages p F T r hr v hv,
    T.multiplicativeConductor_le_iff_unitFiltration_le_ker χ ⌈v⌉₊]
  exact (Subgroup.map_le_map_iff_of_injective
    (profiniteReciprocityCompletion p F T r hr).1).symm

/-- The successor conductor is characterized by its last real upper break, including the tame case. -/
theorem absoluteQuasicharacterLastUpperBreak_of_conductorLevels
    (hlevels : AbsoluteQuasicharacterConductorLevels.{u}) :
    AbsoluteQuasicharacterLastUpperBreak.{u} := by
  intro p hp F T
  let := T.topology
  intro r hr χ n
  have hn : T.multiplicativeConductor χ ≤ n ↔
      Ramification.Padic.localAbelianUpperRamificationGroup F (n : ℝ) ≤
        χ.toMonoidHom.ker.map r.toMonoidHom := by
    simpa only [Nat.ceil_natCast] using
      hlevels p F T r hr χ (n : ℝ) (Nat.cast_nonneg n)
  constructor
  · intro ha
    constructor
    · intro h
      have hle := hn.mpr h
      omega
    · intro v hv
      apply (hlevels p F T r hr χ v ((Nat.cast_nonneg n).trans hv.le)).mp
      rw [ha]
      exact Nat.succ_le_of_lt (Nat.lt_ceil.mpr hv)
  · rintro ⟨hnot, hafter⟩
    have hgt : n < T.multiplicativeConductor χ := Nat.lt_of_not_ge (fun h => hnot (hn.mp h))
    have hle : T.multiplicativeConductor χ ≤ n + 1 := by
      have hv : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
      have h := (hlevels p F T r hr χ ((n + 1 : ℕ) : ℝ)
        (Nat.cast_nonneg _)).mpr (hafter _ hv)
      simpa only [Nat.ceil_natCast] using h
    omega

/-- The two conductor clauses follow from the literal absolute real unit-image equality. -/
theorem absoluteReciprocityConductorConsequences_of_realImages
    (himages : AbsoluteReciprocityRealUnitImages.{u}) :
    AbsoluteQuasicharacterConductorLevels.{u} ∧ AbsoluteQuasicharacterLastUpperBreak.{u} := by
  have hlevels := absoluteQuasicharacterConductorLevels_of_realImages himages
  exact ⟨hlevels, absoluteQuasicharacterLastUpperBreak_of_conductorLevels hlevels⟩

end Langlands.LocalClassField
