import Langlands.Representation.Filtration.IrreducibleMultiplicityStatement
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.Filtration.MultiplicityIndependenceProof

/-! Actual one-factor series and exact constituent counts for irreducible objects. -/

namespace Langlands

universe uK uG uA uT

namespace IrreducibleMultiplicityProof

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

/-- The sole quotient of the published zero-to-whole chain is the ambient object. -/
noncomputable def oneStepGradedEquiv (A : Rep.{uA} k G) :
    ((LengthTwo.oneStep A.ρ).gradedRepresentation 0).ρ.Equiv A.ρ := by
  let L : A →ₗ[k] (⊤ : Subrepresentation A.ρ).toSubmodule :=
    { toFun := fun v => ⟨v, Submodule.mem_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f : A.ρ.IntertwiningMap
      ((LengthTwo.oneStep A.ρ).gradedRepresentation 0).ρ :=
    { toLinearMap := (LengthCriterionProof.lower
        (⊥ : Subrepresentation A.ρ) ⊤).mkQ ∘ₗ L
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        rfl }
  refine (f.ofBijective ⟨?_, ?_⟩).symm
  · intro v w h
    change Submodule.Quotient.mk (L v) = Submodule.Quotient.mk (L w) at h
    have h' := (Submodule.Quotient.eq _).mp h
    change v - w ∈ (⊥ : Submodule k A) at h'
    exact sub_eq_zero.mp ((Submodule.mem_bot k).mp h')
  · intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective
      (LengthCriterionProof.lower (⊥ : Subrepresentation A.ρ) ⊤) x
    exact ⟨v, rfl⟩

/-- Irreducibility makes the actual zero-to-whole chain a composition series. -/
theorem compositionSeries :
    IrreducibleCompositionSeriesStatement.{uK, uG, uA} := by
  intro k _ G _ A hA
  have := hA
  exact ⟨LengthTwo.oneStep A.ρ, LengthTwo.oneStep_hasSimpleFactors bot_covBy_top,
    ⟨oneStepGradedEquiv A⟩⟩

/-- Counting the actual singleton factor-index type gives one or zero. -/
theorem oneStep_factorMultiplicity (A : Rep.{uA} k G) (τ : Rep.{uT} k G) :
    (Nonempty (A.ρ.Equiv τ.ρ) →
      (LengthTwo.oneStep A.ρ).factorMultiplicity τ = 1) ∧
    (¬ Nonempty (A.ρ.Equiv τ.ρ) →
      (LengthTwo.oneStep A.ρ).factorMultiplicity τ = 0) := by
  unfold ObjectRepFiltration.factorMultiplicity
  have h (i : Fin 1) :
      Nonempty (((LengthTwo.oneStep A.ρ).gradedRepresentation i).ρ.Equiv τ.ρ) ↔
        Nonempty (A.ρ.Equiv τ.ρ) := by
    fin_cases i
    let e := oneStepGradedEquiv A
    exact ⟨fun ⟨p⟩ => ⟨e.symm.trans p⟩, fun ⟨p⟩ => ⟨e.trans p⟩⟩
  constructor
  · intro he
    have : Nonempty {i : Fin 1 //
        Nonempty (((LengthTwo.oneStep A.ρ).gradedRepresentation i).ρ.Equiv τ.ρ)} :=
      ⟨⟨0, (h 0).mpr he⟩⟩
    exact Nat.card_unique
  · intro he
    have : IsEmpty {i : Fin 1 //
        Nonempty (((LengthTwo.oneStep A.ρ).gradedRepresentation i).ρ.Equiv τ.ρ)} :=
      ⟨fun i => he ((h i.val).mp i.prop)⟩
    exact Nat.card_of_isEmpty

/-- Compare every actual series witness with the explicit one-factor series. -/
theorem multiplicity :
    IrreducibleJordanHolderMultiplicityStatement.{uK, uG, uA, uT} := by
  intro k _ G _ A τ hA m
  have := hA
  have hs := LengthTwo.oneStep_hasSimpleFactors (ρ := A.ρ) bot_covBy_top
  rcases oneStep_factorMultiplicity A τ with ⟨h1, h0⟩
  by_cases he : Nonempty (A.ρ.Equiv τ.ρ)
  · have hc : HasJordanHolderMultiplicity A τ 1 :=
      ⟨1, LengthTwo.oneStep A.ρ, hs, h1 he⟩
    have hiff : HasJordanHolderMultiplicity A τ m ↔ m = 1 := by
      constructor
      · intro hm
        exact hm.unique hc
      · intro hm
        simpa only [← hm] using hc
    simpa [he] using hiff
  · have hc : HasJordanHolderMultiplicity A τ 0 :=
      ⟨1, LengthTwo.oneStep A.ρ, hs, h0 he⟩
    have hiff : HasJordanHolderMultiplicity A τ m ↔ m = 0 := by
      constructor
      · intro hm
        exact hm.unique hc
      · intro hm
        simpa only [← hm] using hc
    simpa [he] using hiff

end IrreducibleMultiplicityProof

/-- Actual one-factor series and exact counts for irreducible objects. -/
theorem irreducibleMultiplicity :
    IrreducibleMultiplicityStatement.{uK, uG, uA, uT} :=
  ⟨IrreducibleMultiplicityProof.compositionSeries,
    IrreducibleMultiplicityProof.multiplicity⟩

end Langlands
