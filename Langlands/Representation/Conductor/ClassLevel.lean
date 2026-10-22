import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.Conductor.Definitions

/-!
# The least nonzero newvector level on actual isomorphism classes

The total value is infinity when no finite level exists. Equality with an
epsilon-factor conductor remains a separate representation-theoretic assertion.
-/

noncomputable section

open CategoryTheory Matrix

namespace Langlands

universe uK uF uV uW

namespace Conductor

variable {k : Type uK} [CommRing k] {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]
  {n : ℕ}
  {ρ : Representation k (GeneralLinearGroup (Fin (n + 1)) F) V}
  {σ : Representation k (GeneralLinearGroup (Fin (n + 1)) F) W}

/-- Having some nonzero last-row-congruence fixed space is invariant under equivalence. -/
theorem hasNewvectorLevel_iff_of_equiv (e : ρ.Equiv σ) :
    HasNewvectorLevel ρ ↔ HasNewvectorLevel σ := by
  exact exists_congr fun a => fixedVectors_ne_bot_iff_of_equiv e (levelSubgroup F n a)

/-- The intrinsic least-level condition is invariant, including its minimality clause. -/
theorem isNewvectorConductor_iff_of_equiv (e : ρ.Equiv σ) (a : ℕ) :
    IsNewvectorConductor ρ a ↔ IsNewvectorConductor σ a := by
  have hn (b : ℕ) :
      levelFixedVectors ρ b ≠ ⊥ ↔ levelFixedVectors σ b ≠ ⊥ :=
    fixedVectors_ne_bot_iff_of_equiv e (levelSubgroup F n b)
  have hz (b : ℕ) :
      levelFixedVectors ρ b = ⊥ ↔ levelFixedVectors σ b = ⊥ := by
    simpa only [not_not] using not_congr (hn b)
  exact and_congr (hn a) (forall_congr' fun b => forall_congr' fun _ => hz b)

/-- The total first nonzero level is independent of the representation's model. -/
theorem firstFixedLevel_eq_of_equiv (e : ρ.Equiv σ) :
    firstFixedLevel ρ = firstFixedLevel σ := by
  classical
  by_cases hρ : HasNewvectorLevel ρ
  · have hσ := (hasNewvectorLevel_iff_of_equiv e).mp hρ
    rw [firstFixedLevel_of_hasNewvectorLevel ρ hρ,
      firstFixedLevel_of_hasNewvectorLevel σ hσ]
    congr 1
    exact (newvectorConductor_spec ρ hρ).unique
      ((isNewvectorConductor_iff_of_equiv e _).mpr (newvectorConductor_spec σ hσ))
  · have hσ : ¬ HasNewvectorLevel σ :=
      fun h => hρ ((hasNewvectorLevel_iff_of_equiv e).mpr h)
    rw [(firstFixedLevel_eq_top_iff ρ).mpr hρ,
      (firstFixedLevel_eq_top_iff σ).mpr hσ]

/-- Bounding the first nonzero level is exactly nonvanishing at the bound. -/
theorem firstFixedLevel_le_iff (ρ :
    Representation k (GeneralLinearGroup (Fin (n + 1)) F) V) (b : ℕ) :
    firstFixedLevel ρ ≤ (b : WithTop ℕ) ↔ levelFixedVectors ρ b ≠ ⊥ := by
  classical
  by_cases h : HasNewvectorLevel ρ
  · rw [firstFixedLevel_of_hasNewvectorLevel ρ h]
    change WithTop.some (newvectorConductor ρ h) ≤ WithTop.some b ↔ _
    rw [WithTop.coe_le_coe]
    constructor
    · intro hle hb
      apply (newvectorConductor_spec ρ h).1
      apply le_bot_iff.mp
      rw [← hb]
      exact levelFixedVectors_mono ρ hle
    · intro hb
      exact Nat.find_min' h hb
  · rw [(firstFixedLevel_eq_top_iff ρ).mpr h]
    change (⊤ : WithTop ℕ) ≤ WithTop.some b ↔ _
    simp only [WithTop.top_le_iff, WithTop.coe_ne_top, false_iff]
    exact fun hb => h ⟨b, hb⟩

end Conductor

namespace SmoothDualClass

variable {k : Type uK} [Field k] {F : Type uF} [Field F] [ValuativeRel F]
  [TopologicalSpace F] {n : ℕ}

/-- The actual first nonzero last-row level of an irreducible admissible class.
Infinity records failure of finite-level existence. -/
def firstFixedLevel :
    SmoothDualClass.{uK, uF, uV}
      (k := k) (G := GeneralLinearGroup (Fin (n + 1)) F) → WithTop ℕ :=
  Quotient.lift (fun A => Conductor.firstFixedLevel A.obj.representation) (by
    rintro A B ⟨e⟩
    exact Conductor.firstFixedLevel_eq_of_equiv
      (SmoothRep.equivOfIso
        ((irreducibleAdmissibleProperty (k := k)
          (G := GeneralLinearGroup (Fin (n + 1)) F)).ι.mapIso e)))

@[simp]
theorem firstFixedLevel_ofRep
    (A : IrreducibleAdmissibleRep.{uK, uF, uV}
      (k := k) (G := GeneralLinearGroup (Fin (n + 1)) F)) :
    firstFixedLevel (ofRep A) = Conductor.firstFixedLevel A.obj.representation := rfl

/-- A finite class-level bound is precisely a nonzero fixed vector for that level. -/
theorem firstFixedLevel_le_iff
    (a : SmoothDualClass.{uK, uF, uV}
      (k := k) (G := GeneralLinearGroup (Fin (n + 1)) F)) (b : ℕ) :
    firstFixedLevel a ≤ (b : WithTop ℕ) ↔
      HasFixedVector (Conductor.levelSubgroup F n b) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Conductor.firstFixedLevel_le_iff A.obj.representation b

/-- The fixed-center, bounded-first-level stratum of the actual smooth dual.
This set is not declared finite for arbitrary irreducible classes. -/
def centralLevelStratum
    (χ : Subgroup.center (GeneralLinearGroup (Fin (n + 1)) F) →* kˣ) (b : ℕ) :
    Set (SmoothDualClass.{uK, uF, uV}
      (k := k) (G := GeneralLinearGroup (Fin (n + 1)) F)) :=
  {a | HasCentralCharacter χ a ∧ firstFixedLevel a ≤ (b : WithTop ℕ)}

end SmoothDualClass
end Langlands
