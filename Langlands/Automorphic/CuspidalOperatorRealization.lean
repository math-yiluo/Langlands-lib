import Langlands.Automorphic.OperatorEquivalence

/-! # Positive-rank irreducible cuspidal operator realizations and their classes -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- An actual positive-rank form subspace with full-operator irreducibility and
vanishing of the actual proper constant terms. No existence is asserted. -/
structure CuspidalOperatorRealization (r : ℕ) where
  realization : OperatorRealization F (r + 1)
  irreducible : realization.IsIrreducible
  cuspidal : realization.IsCuspidal

namespace CuspidalOperatorRealization

variable {F} {r : ℕ} (S T : CuspidalOperatorRealization F r)

abbrev Space := S.realization.Space

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Irreducibility excludes the zero carrier. -/
instance space_nontrivial : Nontrivial S.Space := by
  have : S.realization.representation.IsIrreducible := S.irreducible
  have : Nontrivial S.realization.representation.asModule :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (automorphicOperatorAlgebra F (r + 1)))
      S.realization.representation.asModule
  exact S.realization.representation.asModuleEquiv.symm.toEquiv.nontrivial

/-- The actual finite image is nonzero, for later tensor presentations. -/
theorem finiteRealization_ne_bot : S.realization.toFiniteRealization ≠ ⊥ := by
  intro h
  obtain ⟨f, hf⟩ := exists_ne (0 : S.Space)
  have hm : S.realization.formInclusion f ∈ S.realization.toFiniteRealization := ⟨f, rfl⟩
  rw [h] at hm
  change S.realization.formInclusion f = 0 at hm
  exact hf (S.realization.formInclusion_injective (hm.trans (map_zero _).symm))

/-- Every represented vector is a genuine cuspidal function. -/
theorem isCuspidal_vector (f : S.Space) :
    Langlands.Automorphic.IsCuspidal F (r + 1) (S.realization.toContinuous f) :=
  S.realization.isCuspidal_iff.mp S.cuspidal f

/-- Constant terms use the inherited normalized Haar convention. -/
theorem constantTerm_eq_zero {a b : ℕ} (h : a + b = r + 1)
    (ha : 0 < a) (hb : 0 < b) (f : S.Space) (g : AdelicGL F (r + 1)) :
    constantTerm F (r + 1) h (S.realization.toContinuous f) g = 0 :=
  S.realization.constantTerm_eq_zero S.cuspidal h ha hb f g

/-- A prescribed central character remains a condition on this actual embedding. -/
abbrev HasCentralCharacter (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) : Prop :=
  S.realization.HasCentralCharacter χ

/-- Equivalence keeps all finite, compact and differential operators. -/
abbrev Equivalence := S.realization.Equivalence T.realization

variable (F r)

/-- The relation is restricted to actual irreducible cuspidal objects. -/
def equivalenceSetoid : Setoid (CuspidalOperatorRealization F r) where
  r S T := Nonempty (S.Equivalence T)
  iseqv :=
    ⟨fun S => ⟨Representation.Equiv.refl S.realization.representation⟩,
      fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Classes of actual irreducible cuspidal realizations of rank r+1. -/
def IsoClass := Quotient (equivalenceSetoid F r)

variable {F r}

def isoClass (S : CuspidalOperatorRealization F r) : IsoClass F r :=
  Quotient.mk (equivalenceSetoid F r) S

theorem isoClass_eq_iff : S.isoClass = T.isoClass ↔ Nonempty (S.Equivalence T) :=
  Quotient.eq

/-- Forget the cusp/irreducibility witnesses, retaining the whole operator class. -/
def IsoClass.toOperatorClass (c : IsoClass F r) : OperatorRealization.IsoClass F (r + 1) :=
  Quotient.lift (s := equivalenceSetoid F r) (fun S => S.realization.isoClass)
    (fun S T h => (S.realization.isoClass_eq_iff T.realization).mpr h) c

@[simp]
theorem toOperatorClass_isoClass : S.isoClass.toOperatorClass = S.realization.isoClass := rfl

/-- Both quotients use the same full equivalence relation on the selected objects. -/
theorem IsoClass.toOperatorClass_injective :
    Function.Injective (toOperatorClass (F := F) (r := r)) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro S T h
  exact (S.isoClass_eq_iff T).mpr ((S.realization.isoClass_eq_iff T.realization).mp h)

/-- Finite forgetting is well-defined; no injectivity is asserted. -/
def IsoClass.finiteClass (c : IsoClass F r) :
    Langlands.SmoothRep.IsoClass.{0, u, u} ℂ (FiniteAdelicGL F (r + 1)) :=
  c.toOperatorClass.finiteClass

@[simp]
theorem finiteClass_isoClass :
    S.isoClass.finiteClass = S.realization.toFiniteRealization.isoClass := rfl

/-- The quotient retains existence of an actual irreducible cuspidal representative. -/
theorem IsoClass.exists_representative (c : IsoClass F r) :
    ∃ S : CuspidalOperatorRealization F r, S.isoClass = c :=
  Quotient.exists_rep c

end CuspidalOperatorRealization

/-- Mixed positive ranks, with the rank index retained as part of each class. -/
def PositiveRankCuspidalClass := Σ r : ℕ, CuspidalOperatorRealization.IsoClass F r

namespace PositiveRankCuspidalClass

variable {F}

def rankIndex (c : PositiveRankCuspidalClass F) : ℕ := c.1

def rank (c : PositiveRankCuspidalClass F) : ℕ := c.rankIndex + 1

theorem rank_pos (c : PositiveRankCuspidalClass F) : 0 < c.rank := Nat.zero_lt_succ _

def ofFixedRank {r : ℕ} (c : CuspidalOperatorRealization.IsoClass F r) :
    PositiveRankCuspidalClass F := ⟨r, c⟩

@[simp]
theorem rank_ofFixedRank {r : ℕ} (c : CuspidalOperatorRealization.IsoClass F r) :
    (ofFixedRank c).rank = r + 1 := rfl

theorem ofFixedRank_injective (r : ℕ) :
    Function.Injective (ofFixedRank (F := F) (r := r)) := by
  intro c d h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- At one rank the mixed-class equality criterion still requires full equivalence. -/
theorem ofFixedRank_isoClass_eq_iff {r : ℕ} (S T : CuspidalOperatorRealization F r) :
    ofFixedRank S.isoClass = ofFixedRank T.isoClass ↔ Nonempty (S.Equivalence T) := by
  rw [ofFixedRank_injective r |>.eq_iff, S.isoClass_eq_iff T]

/-- Classes with different ranks cannot be equal. -/
theorem ne_of_rank_ne {c d : PositiveRankCuspidalClass F} (h : c.rank ≠ d.rank) : c ≠ d :=
  fun he => h (congrArg rank he)

end PositiveRankCuspidalClass
end Langlands.Automorphic
