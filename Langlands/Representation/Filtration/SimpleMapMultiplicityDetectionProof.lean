import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionStatement
import Langlands.Representation.Filtration.IrreducibleMultiplicityProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! Actual finite-series multiplicity detection by nonzero simple maps. -/

namespace Langlands

universe uK uG uA uB uT

namespace SimpleMapMultiplicityDetectionProof

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

/-- A nonzero map to or from a simple test object forces every supplied
actual-series count of that test object to be positive. -/
theorem positive_of_simple_map
    {B : Rep.{uB} k G} {τ : Rep.{uT} k G}
    (hτ : Representation.IsIrreducible τ.ρ)
    (m : ℕ) (hm : HasJordanHolderMultiplicity B τ m)
    (hf : (∃ f : τ.ρ.IntertwiningMap B.ρ, f ≠ 0) ∨
      (∃ f : B.ρ.IntertwiningMap τ.ρ, f ≠ 0)) :
    0 < m := by
  let := hτ
  have hself : HasJordanHolderMultiplicity τ τ 1 :=
    (irreducibleMultiplicity.2 k G τ τ hτ 1).mpr
      (Or.inl ⟨⟨Representation.Equiv.refl τ.ρ⟩, rfl⟩)
  rcases hf with ⟨f, hf⟩ | ⟨f, hf⟩
  · have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
    exact lt_of_lt_of_le Nat.zero_lt_one
      (jordanHolderInjectiveMonotonicity k G τ B τ f hi 1 m hself hm)
  · have hq := (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
    exact lt_of_lt_of_le Nat.zero_lt_one
      (jordanHolderSurjectiveMonotonicity k G B τ τ f hq m 1 hm hself)

end SimpleMapMultiplicityDetectionProof

/-- The actual range short exact sequence supplies the subobject's finite
series; a nonzero simple map forces its count to be positive. -/
theorem jordanHolderSubobjectSimpleMapDetection :
    JordanHolderSubobjectSimpleMapDetectionStatement.{uK, uG, uA, uB, uT} := by
  intro k _ G _ A B τ hτ i hi M hA hf
  let C : Rep.{uA} k G :=
    Rep.of (A.ρ.quotient i.range.toSubmodule
      (fun g _ hx => i.range.apply_mem_toSubmodule g hx))
  let q : A.ρ.IntertwiningMap C.ρ :=
    { toLinearMap := i.range.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    change i.range.toSubmodule = LinearMap.ker i.range.toSubmodule.mkQ
    exact (Submodule.ker_mkQ _).symm
  obtain ⟨m, c, hm, -, hsum⟩ :=
    jordanHolderShortExactDecomposition k G B A C τ i q hi
      (Submodule.mkQ_surjective _) hex M hA
  exact ⟨m, hm,
    SimpleMapMultiplicityDetectionProof.positive_of_simple_map hτ m hm hf,
    by omega⟩

/-- The actual kernel short exact sequence supplies the quotient's finite
series; a nonzero simple map forces its count to be positive. -/
theorem jordanHolderQuotientSimpleMapDetection :
    JordanHolderQuotientSimpleMapDetectionStatement.{uK, uG, uA, uB, uT} := by
  intro k _ G _ A B τ hτ q hq M hA hf
  let K : Rep.{uA} k G := Rep.of q.ker.toRepresentation
  let i : K.ρ.IntertwiningMap A.ρ :=
    { toLinearMap := q.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap :=
    Submodule.range_subtype _
  obtain ⟨a, m, -, hm, hsum⟩ :=
    jordanHolderShortExactDecomposition k G K A B τ i q
      (Submodule.injective_subtype _) hq hex M hA
  exact ⟨m, hm,
    SimpleMapMultiplicityDetectionProof.positive_of_simple_map hτ m hm hf,
    by omega⟩

/-- Both simple-map detection clauses with all five universes independent. -/
theorem jordanHolderSimpleMapDetection :
    JordanHolderSimpleMapDetectionStatement.{uK, uG, uA, uB, uT} :=
  ⟨jordanHolderSubobjectSimpleMapDetection, jordanHolderQuotientSimpleMapDetection⟩

end Langlands
