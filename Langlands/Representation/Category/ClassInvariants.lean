import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.FixedVectors.Definitions

/-!
# Central-character and fixed-vector conditions on actual smooth classes

These quotient constructions are prerequisites for finite-stratum statements.
They assert no finiteness, central-character existence, or classification theorem.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uW

section FixedVectors

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

private theorem fixedVectors_ne_bot_of_equiv (e : ρ.Equiv σ) (K : Subgroup G)
    (h : fixedVectors ρ K ≠ ⊥) : fixedVectors σ K ≠ ⊥ := by
  obtain ⟨v, hv, hne⟩ := (fixedVectors ρ K).ne_bot_iff.mp h
  refine (fixedVectors σ K).ne_bot_iff.mpr ⟨e v, ?_, ?_⟩
  · exact (fixedVectorsEquiv e K ⟨v, hv⟩).property
  · intro hz
    apply hne
    exact e.injective (hz.trans (map_zero e).symm)

/-- A representation equivalence preserves nonzero subgroup-fixed spaces. -/
theorem fixedVectors_ne_bot_iff_of_equiv (e : ρ.Equiv σ) (K : Subgroup G) :
    fixedVectors ρ K ≠ ⊥ ↔ fixedVectors σ K ≠ ⊥ :=
  ⟨fixedVectors_ne_bot_of_equiv e K, fixedVectors_ne_bot_of_equiv e.symm K⟩

end FixedVectors

namespace SmoothRep

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] {A B : SmoothRep.{uR, uG, uV} R G}

/-- Prescribed scalar action on the center is invariant under isomorphism. -/
theorem hasCentralCharacter_iff_of_iso (e : A ≅ B)
    (χ : Subgroup.center G →* Rˣ) :
    A.HasCentralCharacter χ ↔ B.HasCentralCharacter χ := by
  have forward {A B : SmoothRep.{uR, uG, uV} R G}
      (e : A ≅ B) (h : A.HasCentralCharacter χ) : B.HasCentralCharacter χ := by
    intro z w
    obtain ⟨v, rfl⟩ := (equivOfIso e).surjective w
    calc
      B.representation (z : G) ((equivOfIso e) v) =
          (equivOfIso e) (A.representation (z : G) v) :=
        (congrArg (fun f : A →ₗ[R] B => f v)
          ((equivOfIso e).isIntertwining' (z : G))).symm
      _ = (χ z : R) • (equivOfIso e) v := by rw [h z v, map_smul]
  exact ⟨forward e, forward e.symm⟩

end SmoothRep

namespace SmoothDualClass

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The class of an actual irreducible admissible smooth representation. -/
def ofRep (A : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)) :
    SmoothDualClass.{uR, uG, uV} (k := k) (G := G) :=
  Quotient.mk _ A

/-- A prescribed central character on the actual quotient by isomorphism. -/
def HasCentralCharacter (χ : Subgroup.center G →* kˣ) :
    SmoothDualClass.{uR, uG, uV} (k := k) (G := G) → Prop :=
  Quotient.lift (fun A => A.obj.HasCentralCharacter χ) (by
    rintro A B ⟨e⟩
    apply propext
    exact SmoothRep.hasCentralCharacter_iff_of_iso
      ((irreducibleAdmissibleProperty (k := k) (G := G)).ι.mapIso e) χ)

/-- The existence of a nonzero vector fixed by the specified subgroup. -/
def HasFixedVector (K : Subgroup G) :
    SmoothDualClass.{uR, uG, uV} (k := k) (G := G) → Prop :=
  Quotient.lift (fun A => fixedVectors A.obj.representation K ≠ ⊥) (by
    rintro A B ⟨e⟩
    apply propext
    exact fixedVectors_ne_bot_iff_of_equiv
      (SmoothRep.equivOfIso
        ((irreducibleAdmissibleProperty (k := k) (G := G)).ι.mapIso e)) K)

@[simp]
theorem hasCentralCharacter_ofRep
    (χ : Subgroup.center G →* kˣ)
    (A : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)) :
    HasCentralCharacter χ (ofRep A) ↔ A.obj.HasCentralCharacter χ := Iff.rfl

@[simp]
theorem hasFixedVector_ofRep (K : Subgroup G)
    (A : IrreducibleAdmissibleRep.{uR, uG, uV} (k := k) (G := G)) :
    HasFixedVector K (ofRep A) ↔ fixedVectors A.obj.representation K ≠ ⊥ := Iff.rfl

/-- A fixed-center, fixed-subgroup stratum of the genuine smooth dual.
Its finiteness is not built into this set. -/
def centralFixedStratum (χ : Subgroup.center G →* kˣ) (K : Subgroup G) :
    Set (SmoothDualClass.{uR, uG, uV} (k := k) (G := G)) :=
  {a | HasCentralCharacter χ a ∧ HasFixedVector K a}

end SmoothDualClass
end Langlands
