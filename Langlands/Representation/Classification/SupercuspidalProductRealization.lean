import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Induction.BlockEquivalence

/-! # Independently small supercuspidal factors in actual normalized products -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

/-- An actual supercuspidal representation has an equivalent realization in
any independently prescribed carrier universe. -/
theorem exists_supercuspidal_realization
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    letI := T.topology
    ∃ B : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n),
      Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  let := T.topology
  obtain ⟨B, hB, ⟨e⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uV, uW} p F T n A.obj A.property.1
  exact ⟨⟨B, hB, GeneralLinear.isSupercuspidal_of_equiv e A.property.2⟩, ⟨e⟩⟩

/-- A chosen supercuspidal model with carrier in the prescribed universe. -/
def supercuspidalRealization
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    letI := T.topology
    GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n) :=
  (T.exists_supercuspidal_realization A).choose

/-- The actual intertwining equivalence to the chosen small model. -/
def supercuspidalRealizationEquiv
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n)) :
    letI := T.topology
    A.obj.representation.Equiv
      (T.supercuspidalRealization.{uF, uV, uW} A).obj.representation :=
  (T.exists_supercuspidal_realization A).choose_spec.some

/-- Unitarizability is preserved by the actual carrier equivalence. -/
theorem isUnitarizable_supercuspidalRealization
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n))
    (hA : letI := T.topology; IsUnitarizable A.obj.representation) :
    letI := T.topology
    IsUnitarizable
      (T.supercuspidalRealization.{uF, uV, uW} A).obj.representation :=
  (isUnitarizable_iff_of_equiv (T.supercuspidalRealizationEquiv A)).mp hA

/-- Replacing every supercuspidal block by its small model transports the
entire normalized upper product, without changing its block shape. -/
def supercuspidalProductRealizationEquiv (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i)) :
    letI := T.topology
    (T.normalizedProductInduced B (fun i => (A i).obj.representation)).Equiv
      (T.normalizedProductInduced B
        (fun i => (T.supercuspidalRealization.{uF, uV, uW} (A i)).obj.representation)) :=
  T.normalizedProductInducedEquiv B (fun i => T.supercuspidalRealizationEquiv (A i))

/-- An equivalence from an original action to a unitary supercuspidal product
can use block carriers in any prescribed universe, keeping the source action. -/
theorem exists_unitary_supercuspidal_product_equiv (B : GeneralLinear.BlockShape n)
    (A : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (hA : letI := T.topology; ∀ i, IsUnitarizable (A i).obj.representation)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (e : letI := T.topology
      ρ.Equiv (T.normalizedProductInduced B (fun i => (A i).obj.representation))) :
    letI := T.topology
    ∃ C : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uW}
        (F := F.Carrier) (n := B.size i),
      (∀ i, IsUnitarizable (C i).obj.representation) ∧
        Nonempty (ρ.Equiv
          (T.normalizedProductInduced B (fun i => (C i).obj.representation))) := by
  let := T.topology
  exact ⟨fun i => T.supercuspidalRealization (A i),
    fun i => T.isUnitarizable_supercuspidalRealization (A i) (hA i),
    ⟨e.trans (T.supercuspidalProductRealizationEquiv B A)⟩⟩

end Langlands.PadicField.TopologicalData
