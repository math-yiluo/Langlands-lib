import Langlands.Automorphic.OperatorSubquotientSubspaces
import Langlands.Automorphic.OperatorZeroDenominator
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Positive-rank irreducible actual automorphic operator quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type uF) [Field F] [NumberField F]

local instance irreducibleQuotientRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance irreducibleQuotientContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance irreducibleQuotientSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance irreducibleQuotientFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance irreducibleQuotientStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance irreducibleQuotientRealizationGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- An actual positive-rank numerator/denominator quotient with irreducible whole action. -/
structure IrreducibleOperatorSubquotient (r : ℕ) where
  subquotient : OperatorSubquotient F (r + 1)
  irreducible : subquotient.IsIrreducible

namespace IrreducibleOperatorSubquotient

variable {F} {r : ℕ} (S T : IrreducibleOperatorSubquotient F r)

abbrev Space := S.subquotient.Space

abbrev representation := S.subquotient.representation

instance representation_isIrreducible : S.representation.IsIrreducible := S.irreducible

/-- Nontriviality is part of irreducibility, rather than an extra existence assumption. -/
instance space_nontrivial : Nontrivial S.Space := by
  have : Nontrivial S.representation.asModule :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (automorphicOperatorAlgebra F (r + 1)))
      S.representation.asModule
  exact S.representation.asModuleEquiv.symm.toEquiv.nontrivial

/-- The actual denominator is maximal proper among whole-operator invariant subspaces. -/
theorem lower_isCoatom : IsCoatom S.subquotient.lower :=
  S.subquotient.isIrreducible_iff_isCoatom.mp S.irreducible

theorem lower_ne_top : S.subquotient.lower ≠ ⊤ := S.lower_isCoatom.1

set_option synthInstance.maxHeartbeats 100000 in
/-- A supplied maximal proper denominator constructs a genuine irreducible module quotient. -/
def ofCoatom (upper : OperatorRealization F (r + 1))
    (lower : Subrepresentation upper.representation) (h : IsCoatom lower) :
    IrreducibleOperatorSubquotient F r where
  subquotient := ⟨upper, lower⟩
  irreducible := (OperatorSubquotient.isIrreducible_iff_isCoatom
    (⟨upper, lower⟩ : OperatorSubquotient F (r + 1))).mpr h

set_option maxHeartbeats 800000 in
/-- Nonzero quotient vectors have actual numerator representatives outside the denominator. -/
theorem exists_representative_not_mem_lower :
    ∃ f : S.subquotient.upper.Space, f ∉ S.subquotient.lower := by
  obtain ⟨v, hv⟩ := exists_ne (0 : S.Space)
  obtain ⟨f, hfv⟩ := S.subquotient.projection_surjective v
  refine ⟨f, fun hf => hv ?_⟩
  exact hfv.symm.trans ((S.subquotient.projection_eq_zero_iff f).mpr hf)

/-- Equivalence concerns all concrete operators on the actual quotient carriers. -/
abbrev Equivalence := S.subquotient.Equivalence T.subquotient

variable (F r)

def equivalenceSetoid : Setoid (IrreducibleOperatorSubquotient F r) where
  r S T := Nonempty (S.Equivalence T)
  iseqv :=
    ⟨fun S => ⟨Representation.Equiv.refl S.representation⟩,
      fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Classes identify whole representations, without identifying quotient presentations. -/
def IsoClass := Quotient (equivalenceSetoid F r)

variable {F r}

def isoClass (S : IrreducibleOperatorSubquotient F r) : IsoClass F r :=
  Quotient.mk (equivalenceSetoid F r) S

theorem isoClass_eq_iff : S.isoClass = T.isoClass ↔ Nonempty (S.Equivalence T) :=
  Quotient.eq

/-- Forget irreducibility while retaining the actual whole-action quotient class. -/
def IsoClass.toSubquotientClass (c : IsoClass F r) :
    OperatorSubquotient.IsoClass F (r + 1) :=
  Quotient.lift (s := equivalenceSetoid F r) (fun S => S.subquotient.isoClass)
    (fun S T h => (S.subquotient.isoClass_eq_iff T.subquotient).mpr h) c

@[simp] theorem toSubquotientClass_isoClass :
    S.isoClass.toSubquotientClass = S.subquotient.isoClass := rfl

theorem IsoClass.toSubquotientClass_injective :
    Function.Injective (toSubquotientClass (F := F) (r := r)) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro S T h
  exact (S.isoClass_eq_iff T).mpr
    ((S.subquotient.isoClass_eq_iff T.subquotient).mp h)

def IsoClass.toSubquotientClassEmbedding :
    IsoClass F r ↪ OperatorSubquotient.IsoClass F (r + 1) :=
  ⟨toSubquotientClass, toSubquotientClass_injective⟩

/-- Finite forgetting retains smoothness, without asserting finite irreducibility. -/
def IsoClass.finiteClass (c : IsoClass F r) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteAdelicGL F (r + 1)) :=
  c.toSubquotientClass.finiteClass

@[simp] theorem finiteClass_isoClass :
    S.isoClass.finiteClass = Langlands.SmoothRep.isoClass S.subquotient.smoothRepresentation :=
  rfl

theorem IsoClass.exists_representative (c : IsoClass F r) :
    ∃ S : IrreducibleOperatorSubquotient F r, S.isoClass = c :=
  Quotient.exists_rep c

end IrreducibleOperatorSubquotient

/-- The rank is retained when irreducible quotient classes of different ranks are combined. -/
def PositiveRankIrreducibleSubquotientClass :=
  Σ r : ℕ, IrreducibleOperatorSubquotient.IsoClass F r

namespace PositiveRankIrreducibleSubquotientClass

variable {F}

def rankIndex (c : PositiveRankIrreducibleSubquotientClass F) : ℕ := c.1

def rank (c : PositiveRankIrreducibleSubquotientClass F) : ℕ := c.rankIndex + 1

theorem rank_pos (c : PositiveRankIrreducibleSubquotientClass F) : 0 < c.rank :=
  Nat.zero_lt_succ _

def ofFixedRank {r : ℕ} (c : IrreducibleOperatorSubquotient.IsoClass F r) :
    PositiveRankIrreducibleSubquotientClass F := ⟨r, c⟩

@[simp] theorem rank_ofFixedRank {r : ℕ}
    (c : IrreducibleOperatorSubquotient.IsoClass F r) :
    (ofFixedRank c).rank = r + 1 := rfl

theorem ofFixedRank_injective (r : ℕ) :
    Function.Injective (ofFixedRank (F := F) (r := r)) := by
  intro c d h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem ofFixedRank_isoClass_eq_iff {r : ℕ}
    (S T : IrreducibleOperatorSubquotient F r) :
    ofFixedRank S.isoClass = ofFixedRank T.isoClass ↔ Nonempty (S.Equivalence T) := by
  rw [ofFixedRank_injective r |>.eq_iff, S.isoClass_eq_iff T]

theorem ne_of_rank_ne {c d : PositiveRankIrreducibleSubquotientClass F}
    (h : c.rank ≠ d.rank) : c ≠ d :=
  fun he => h (congrArg rank he)

end PositiveRankIrreducibleSubquotientClass

namespace CuspidalOperatorRealization

variable {F} [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (S T : CuspidalOperatorRealization F r)

/-- The actual zero-denominator quotient of an existing irreducible cusp realization. -/
def toIrreducibleSubquotient : IrreducibleOperatorSubquotient F r where
  subquotient := S.realization.toSubquotient
  irreducible := (S.realization.toSubquotient_isIrreducible_iff).mpr S.irreducible

/-- This bridge is induced by the genuine canonical projection, on the whole action. -/
def toIrreducibleSubquotientEquiv :
    S.realization.representation.Equiv S.toIrreducibleSubquotient.representation :=
  OperatorRealization.toSubquotientEquiv F (r + 1) S.realization

@[simp] theorem toIrreducibleSubquotientEquiv_apply (f : S.Space) :
    S.toIrreducibleSubquotientEquiv f =
      S.toIrreducibleSubquotient.subquotient.projection f := rfl

theorem toIrreducibleSubquotient_equivalence_iff :
    Nonempty (S.toIrreducibleSubquotient.Equivalence T.toIrreducibleSubquotient) ↔
      Nonempty (S.Equivalence T) :=
  OperatorRealization.toSubquotient_equivalence_iff S.realization T.realization

/-- Pass from actual irreducible cusp classes to actual irreducible quotient classes. -/
def IsoClass.toIrreducibleSubquotient (c : IsoClass F r) :
    IrreducibleOperatorSubquotient.IsoClass F r :=
  Quotient.lift (s := equivalenceSetoid F r) (fun S => S.toIrreducibleSubquotient.isoClass)
    (fun S T h => (S.toIrreducibleSubquotient.isoClass_eq_iff
      T.toIrreducibleSubquotient).mpr
        ((S.toIrreducibleSubquotient_equivalence_iff T).mpr h)) c

@[simp] theorem toIrreducibleSubquotient_isoClass :
    S.isoClass.toIrreducibleSubquotient = S.toIrreducibleSubquotient.isoClass := rfl

theorem IsoClass.toIrreducibleSubquotient_injective :
    Function.Injective (toIrreducibleSubquotient (F := F) (r := r)) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro S T h
  exact (S.isoClass_eq_iff T).mpr
    ((S.toIrreducibleSubquotient_equivalence_iff T).mp
      ((S.toIrreducibleSubquotient.isoClass_eq_iff
        T.toIrreducibleSubquotient).mp h))

def IsoClass.toIrreducibleSubquotientEmbedding :
    IsoClass F r ↪ IrreducibleOperatorSubquotient.IsoClass F r :=
  ⟨toIrreducibleSubquotient, toIrreducibleSubquotient_injective⟩

/-- Forgetting to all quotient classes agrees with the published zero-denominator bridge. -/
@[simp] theorem IsoClass.toSubquotientClass_toIrreducibleSubquotient (c : IsoClass F r) :
    c.toIrreducibleSubquotient.toSubquotientClass = c.toOperatorClass.toSubquotient := by
  refine Quotient.inductionOn c ?_
  intro S
  rfl

/-- The class bridge commutes with forgetting to the actual finite smooth class. -/
@[simp] theorem IsoClass.finiteClass_toIrreducibleSubquotient (c : IsoClass F r) :
    c.toIrreducibleSubquotient.finiteClass = c.finiteClass := by
  change c.toIrreducibleSubquotient.toSubquotientClass.finiteClass =
    c.toOperatorClass.finiteClass
  rw [toSubquotientClass_toIrreducibleSubquotient,
    OperatorRealization.IsoClass.finiteClass_toSubquotient]

end CuspidalOperatorRealization
end Langlands.Automorphic
