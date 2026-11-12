import Langlands.Topology.ClosedCoverQuotientComponents
import Mathlib.Topology.Constructible
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Pi

/-! # Constructibility of finite incidence quotient counts -/

noncomputable section

universe u v w z

open Topology

namespace Langlands.Topology

variable {P : Type u} {ι : Type v} [TopologicalSpace P] [Finite ι]

/-- The parameter cell on which the family of relations has the fixed truth pattern `Q`. -/
def finiteRelationPattern (R : P → ι → ι → Prop) (Q : ι → ι → Prop) : Set P :=
  {p | ∀ i j, R p i j ↔ Q i j}

/-- Every fixed truth pattern of a finite family of constructible predicates is constructible. -/
theorem isConstructible_finite_relationPattern (R : P → ι → ι → Prop)
    (hR : ∀ i j, IsConstructible {p | R p i j}) (Q : ι → ι → Prop) :
    IsConstructible (finiteRelationPattern R Q) := by
  classical
  have hcell (i j : ι) : IsConstructible {p | R p i j ↔ Q i j} := by
    by_cases h : Q i j
    · simpa only [h, iff_true] using hR i j
    · simpa only [h, iff_false, Set.compl_ofPred] using (hR i j).compl
  have heq : finiteRelationPattern R Q =
      ⋂ i, ⋂ j, {p | R p i j ↔ Q i j} := by
    ext p
    simp only [finiteRelationPattern, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact IsConstructible.iInter fun i => IsConstructible.iInter (hcell i)

/-- Constructible edges of a relation on a fixed finite set give constructible loci
for every cardinality of its generated quotient. No Noetherian hypothesis is needed. -/
theorem isConstructible_finite_incidenceQuotient_count (R : P → ι → ι → Prop)
    (hR : ∀ i j, IsConstructible {p | R p i j}) (n : ℕ) :
    IsConstructible {p | ENat.card (Quot (R p)) = n} := by
  classical
  let good : Set (ι → ι → Prop) := {Q | ENat.card (Quot Q) = n}
  have heq : {p | ENat.card (Quot (R p)) = n} =
      ⋃ Q ∈ good, finiteRelationPattern R Q := by
    ext p
    constructor
    · intro hp
      exact Set.mem_iUnion₂.mpr ⟨R p, hp, fun _ _ => Iff.rfl⟩
    · intro hp
      obtain ⟨Q, hQ, hpQ⟩ := Set.mem_iUnion₂.mp hp
      have hc : ENat.card (Quot (R p)) = ENat.card (Quot Q) :=
        ENat.card_congr (Quot.congr (Equiv.refl ι) hpQ)
      exact hc.trans hQ
  rw [heq]
  exact IsConstructible.biUnion (Set.toFinite good) fun Q _ =>
    isConstructible_finite_relationPattern R hR Q

/-- If actual component counts are computed by a finite incidence quotient, only
constructibility of its finitely many edge predicates remains to be checked. -/
theorem isConstructible_componentCount_of_finite_incidence
    {B : P → Type w} [∀ p, TopologicalSpace (B p)]
    (R : P → ι → ι → Prop)
    (hR : ∀ i j, IsConstructible {p | R p i j})
    (hcount : ∀ p, ENat.card (ConnectedComponents (B p)) = ENat.card (Quot (R p)))
    (n : ℕ) :
    IsConstructible {p | ENat.card (ConnectedComponents (B p)) = n} := by
  have heq : {p | ENat.card (ConnectedComponents (B p)) = n} =
      {p | ENat.card (Quot (R p)) = n} := by
    ext p
    simp only [Set.mem_ofPred_eq, hcount p]
  rw [heq]
  exact isConstructible_finite_incidenceQuotient_count R hR n

/-- A family of quotient maps with finite connected closed covers has constructible
component-count loci whenever the image-incidence predicates are constructible. -/
theorem isConstructible_componentCount_of_closedCoverIncidence
    {A : P → Type w} {B : P → Type z}
    [∀ p, TopologicalSpace (A p)] [∀ p, TopologicalSpace (B p)]
    (f : ∀ p, A p → B p) (hf : ∀ p, IsQuotientMap (f p))
    (s : ∀ p, ι → Set (A p))
    (hclosed : ∀ p i, IsClosed (s p i))
    (hconn : ∀ p i, IsConnected (s p i))
    (hcover : ∀ p, (⋃ i, s p i) = Set.univ)
    (hincidence : ∀ i j, IsConstructible {p | coverFibreRelation (f p) (s p) i j})
    (n : ℕ) :
    IsConstructible {p | ENat.card (ConnectedComponents (B p)) = n} :=
  isConstructible_componentCount_of_finite_incidence
    (fun p => coverFibreRelation (f p) (s p)) hincidence
    (fun p => componentCount_eq_closedCoverIncidence
      (f p) (hf p) (s p) (hclosed p) (hconn p) (hcover p)) n

end Langlands.Topology
