import Langlands.Representation.Classification.SquareIntegrableBlockInductionProof
import Langlands.Representation.Classification.SegmentSpecialSquareIntegrabilityCriterionProof
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleClassification
import Langlands.Representation.Unitary.CentralCharacterProof

/-!
# Tempered induction of unitarizable supercuspidal blocks

The canonical local bridge used after Henniart's Theorem 2.4: the actual
normalized product induction of unitarizable supercuspidal blocks is tempered.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A positive-rank unitarizable supercuspidal object is square-integrable
modulo its full center for the canonical topological data. -/
theorem unitarizableSupercuspidal_isSquareIntegrable {n : ℕ} (hn : 0 < n)
    (σ : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := n))
    (hu : letI := F.canonicalTopologicalData.topology
      IsUnitarizable σ.obj.representation) :
    letI := F.canonicalTopologicalData.topology
    F.canonicalTopologicalData.IsSquareIntegrable σ.obj.representation := by
  let T := F.canonicalTopologicalData
  let := T.topology
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hn)
  | succ n =>
    have := T.generalLinearTopologicalGroup (n + 1)
    let hi : σ.obj.representation.IsIrreducible := σ.property.1
    let : Nontrivial σ.obj :=
      IsSimpleModule.nontrivial
        (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)) σ.obj.representation.asModule
    obtain ⟨c⟩ := unitarizableCentralCharacter σ.obj.representation
      σ.property.2.1 hi hu
    exact isSquareIntegrable_of_essential_of_unitaryCentralCharacter T hn
      (RankinSelberg.supercuspidal_isEssentiallySquareIntegrable F n σ.obj
        hi σ.property.2) c

/-- The actual normalized product induction of positive-rank unitarizable
supercuspidal blocks is analytically tempered, with the canonical topology. -/
theorem unitarizableSupercuspidalProduct_isTempered {n : ℕ} (hn : 0 < n)
    (B : GeneralLinear.BlockShape n)
    (σ : letI := F.canonicalTopologicalData.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := B.size i))
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ i, IsUnitarizable (σ i).obj.representation) :
    letI := F.canonicalTopologicalData.topology
    F.canonicalTopologicalData.IsTempered
      (F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => (σ i).obj.representation)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  exact (squareIntegrableBlockInduction.{uF, uV} F T n hn B
    (fun i => (σ i).obj) (fun i => ⟨(σ i).property.1,
      unitarizableSupercuspidal_isSquareIntegrable F (B.positive i) (σ i) (hu i),
      hu i⟩)).2.2

/-- Transfer the temperedness of a normalized supercuspidal product to any
equivalent action, without a restriction on the latter's carrier universe. -/
theorem isTempered_of_equiv_unitarizableSupercuspidalProduct
    {n : ℕ} (hn : 0 < n) (B : GeneralLinear.BlockShape n)
    (σ : letI := F.canonicalTopologicalData.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := B.size i))
    (hu : letI := F.canonicalTopologicalData.topology
      ∀ i, IsUnitarizable (σ i).obj.representation)
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (e : letI := F.canonicalTopologicalData.topology
      π.Equiv (F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => (σ i).obj.representation))) :
    F.canonicalTopologicalData.IsTempered π :=
  (PadicField.TopologicalData.isTempered_iff_of_equiv e).mpr
    (unitarizableSupercuspidalProduct_isTempered F hn B σ hu)

/-- The local temperedness bridge, uniformly over the field and carrier
universes. The topology is the field's canonical one throughout. -/
def UnitarizableSupercuspidalInductionTemperedStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    {n : ℕ} (_hn : 0 < n) (B : GeneralLinear.BlockShape n),
    letI := F.canonicalTopologicalData.topology
    ∀ (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV}
        (F := F.Carrier) (n := B.size i))
      (_hu : ∀ i, IsUnitarizable (σ i).obj.representation)
      {V : Type uW} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F.Carrier) V)
      (_e : π.Equiv (F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => (σ i).obj.representation))),
      F.canonicalTopologicalData.IsTempered π

/-- The proved uniform version of the local temperedness bridge. -/
theorem unitarizableSupercuspidalInductionTempered :
    UnitarizableSupercuspidalInductionTemperedStatement.{uF, uV, uW} := by
  intro p hp F n hn B
  let := F.canonicalTopologicalData.topology
  intro σ hu V _ _ π e
  exact isTempered_of_equiv_unitarizableSupercuspidalProduct F hn B σ hu π e

end Langlands.Classification
