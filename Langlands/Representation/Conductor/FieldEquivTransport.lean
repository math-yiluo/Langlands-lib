import Langlands.LocalField.ContinuousIntegerTransport
import Langlands.Representation.Conductor.ClassLevel
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Fixed-level conductors under change of local field

An isomorphism of local fields preserving the valuation rings takes the
actual conductor subgroups to one another by entrywise application.
-/

namespace Langlands.Conductor

open Matrix

universe u v uK uV

variable {F : Type u} [Field F] [ValuativeRel F]
variable {E : Type v} [Field E] [ValuativeRel E]

private theorem map_mem_levelSubgroup_of_integers (e : F ≃+* E)
    (he : ∀ x : F, x ∈ (ValuativeRel.valuation F).integer ↔
      e x ∈ (ValuativeRel.valuation E).integer)
    {n a : ℕ} {g : GeneralLinearGroup (Fin (n + 1)) F} (hg : g ∈ levelSubgroup F n a) :
    GeneralLinearGroup.map e.toRingHom g ∈ levelSubgroup E n a := by
  let OF := (ValuativeRel.valuation F).integer
  let OE := (ValuativeRel.valuation E).integer
  let eO := e.restrict OF OE he
  obtain ⟨h, hh, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.map eO.toRingHom h, ?_, ?_⟩
  · change GeneralLinearGroup.map eO.toRingHom h ∈
      integralCongruence n (IsLocalRing.maximalIdeal OE ^ a)
    rw [mem_integralCongruence]
    intro j
    have hj := (mem_integralCongruence n (IsLocalRing.maximalIdeal OF ^ a) h).mp hh j
    have hj' := Ideal.mem_map_of_mem eO.toRingHom hj
    have hideal : Ideal.map eO.toRingHom (IsLocalRing.maximalIdeal OF) =
        IsLocalRing.maximalIdeal OE := IsLocalRing.map_ringEquiv_maximalIdeal eO
    rw [Ideal.map_pow, hideal] at hj'
    have h1 : eO ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) OF) (Fin.last n) j) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) OE) (Fin.last n) j := by
      by_cases hEq : Fin.last n = j <;> simp [Matrix.one_apply, hEq]
    change eO (h (Fin.last n) j - (1 : Matrix _ _ OF) (Fin.last n) j) ∈ _ at hj'
    change eO (h (Fin.last n) j) - (1 : Matrix _ _ OE) (Fin.last n) j ∈ _
    rwa [map_sub, h1] at hj'
  · ext i j
    rfl

private theorem map_levelSubgroup_of_integers (e : F ≃+* E)
    (he : ∀ x : F, x ∈ (ValuativeRel.valuation F).integer ↔
      e x ∈ (ValuativeRel.valuation E).integer) (n a : ℕ) :
    (levelSubgroup F n a).map (GeneralLinearGroup.map e.toRingHom) = levelSubgroup E n a := by
  apply le_antisymm
  · rintro g ⟨h, hh, rfl⟩
    exact map_mem_levelSubgroup_of_integers e he hh
  · intro g hg
    have he' (x : E) : x ∈ (ValuativeRel.valuation E).integer ↔
        e.symm x ∈ (ValuativeRel.valuation F).integer := by
      simpa only [RingEquiv.apply_symm_apply] using (he (e.symm x)).symm
    refine ⟨GeneralLinearGroup.map e.symm.toRingHom g,
      map_mem_levelSubgroup_of_integers e.symm he' hg, ?_⟩
    ext i j
    exact e.apply_symm_apply (g i j)

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {K : Type uK} [CommRing K] {V : Type uV} [AddCommGroup V] [Module K V] {n : ℕ}

/-- Entrywise pullback by a bicontinuous field isomorphism preserves each
fixed space for the actual newvector subgroups. -/
theorem levelFixedVectors_comp_fieldEquiv (e : F ≃+* E)
    (he : Continuous e) (he' : Continuous e.symm)
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) E) V) (a : ℕ) :
    levelFixedVectors (ρ.comp (GeneralLinearGroup.map e.toRingHom)) a =
      levelFixedVectors ρ a := by
  have himage := map_levelSubgroup_of_integers e
    ((LocalFieldData.ofInstances F).mem_integers_iff_of_continuous_ringEquiv
      (LocalFieldData.ofInstances E) e he he') n a
  ext x
  rw [mem_levelFixedVectors, mem_levelFixedVectors]
  constructor
  · intro hx g hg
    have hg' : g ∈ (levelSubgroup F n a).map (GeneralLinearGroup.map e.toRingHom) :=
      himage.symm ▸ hg
    obtain ⟨h, hh, rfl⟩ := hg'
    exact hx h hh
  · intro hx g hg
    have hg' : GeneralLinearGroup.map e.toRingHom g ∈
        (levelSubgroup F n a).map (GeneralLinearGroup.map e.toRingHom) := ⟨g, hg, rfl⟩
    exact hx _ (himage ▸ hg')

/-- The finite newvector conductor is preserved by entrywise field transport. -/
theorem isNewvectorConductor_comp_fieldEquiv_iff (e : F ≃+* E)
    (he : Continuous e) (he' : Continuous e.symm)
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) E) V) (a : ℕ) :
    IsNewvectorConductor (ρ.comp (GeneralLinearGroup.map e.toRingHom)) a ↔
      IsNewvectorConductor ρ a := by
  simp only [IsNewvectorConductor, levelFixedVectors_comp_fieldEquiv e he he']

/-- The total first fixed level is preserved by entrywise field transport. -/
theorem firstFixedLevel_comp_fieldEquiv (e : F ≃+* E)
    (he : Continuous e) (he' : Continuous e.symm)
    (ρ : Representation K (GeneralLinearGroup (Fin (n + 1)) E) V) :
    firstFixedLevel (ρ.comp (GeneralLinearGroup.map e.toRingHom)) = firstFixedLevel ρ := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro a
  have hlevel := firstFixedLevel_le_iff (ρ.comp (GeneralLinearGroup.map e.toRingHom)) a
  rw [levelFixedVectors_comp_fieldEquiv e he he' ρ a] at hlevel
  exact hlevel.trans (firstFixedLevel_le_iff ρ a).symm

end Langlands.Conductor
