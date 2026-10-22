import Langlands.Representation.Filtration.Definitions
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! Actual object filtrations and multiplicity-sensitive composition factors. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]

/-- The constant functor on one object, used to reuse the actual natural
filtration construction for a single representation. -/
abbrev objectRepresentationFunctor (A : Rep.{uV} R G) :
    Discrete PUnit.{1} ⥤ Rep.{uV} R G :=
  (Functor.const (Discrete PUnit.{1})).obj A

/-- An invariant subspace gives a subfunctor of the constant functor.
All maps of a constant functor are identity maps, so stability is intrinsic. -/
def objectRepresentationSubfunctor (A : Rep.{uV} R G)
    (S : Subrepresentation A.ρ) :
    RepSubfunctor (objectRepresentationFunctor A) where
  obj _ := S
  map_mem := by
    intro X Y f v hv
    exact hv

/-- A finite zero-to-full filtration of one actual representation.
Its quotient objects reuse the published natural-filtration construction. -/
abbrev ObjectRepFiltration (A : Rep.{uV} R G) (n : ℕ) :=
  RepFunctorFiltration (objectRepresentationFunctor A) n

namespace ObjectRepFiltration

variable {A : Rep.{uV} R G} {n : ℕ}

/-- Build a filtration from the usual chain of invariant subspaces.
There is no additional naturality assumption on the input chain. -/
def ofSubrepresentations
    (step : Fin (n + 1) → Subrepresentation A.ρ)
    (hmono : Monotone step) (hzero : step 0 = ⊥)
    (htop : step (Fin.last n) = ⊤) : ObjectRepFiltration A n where
  step i := objectRepresentationSubfunctor A (step i)
  monotone _ := hmono
  zero _ := hzero
  top _ := htop

/-- The ith actual invariant subspace in the filtration. -/
def subrepresentation (s : ObjectRepFiltration A n) (i : Fin (n + 1)) :
    Subrepresentation A.ρ :=
  (s.step i).obj (Discrete.mk PUnit.unit)

theorem monotone_subrepresentation (s : ObjectRepFiltration A n) :
    Monotone s.subrepresentation :=
  s.monotone (Discrete.mk PUnit.unit)

@[simp]
theorem subrepresentation_zero (s : ObjectRepFiltration A n) :
    s.subrepresentation 0 = ⊥ :=
  s.zero (Discrete.mk PUnit.unit)

@[simp]
theorem subrepresentation_last (s : ObjectRepFiltration A n) :
    s.subrepresentation (Fin.last n) = ⊤ :=
  s.top (Discrete.mk PUnit.unit)

@[simp]
theorem ofSubrepresentations_subrepresentation
    (step : Fin (n + 1) → Subrepresentation A.ρ)
    (hmono : Monotone step) (hzero : step 0 = ⊥)
    (htop : step (Fin.last n) = ⊤) (i : Fin (n + 1)) :
    (ofSubrepresentations step hmono hzero htop).subrepresentation i = step i := rfl

/-- The actual quotient of the next invariant subspace by the current one. -/
def gradedRepresentation (s : ObjectRepFiltration A n) (i : Fin n) :
    Rep.{uV} R G :=
  (s.graded i).obj (Discrete.mk PUnit.unit)

/-- The actual surjection from the upper step onto its graded quotient. -/
def gradedProjection (s : ObjectRepFiltration A n) (i : Fin n) :
    Rep.of (s.subrepresentation i.succ).toRepresentation ⟶ s.gradedRepresentation i :=
  ((s.step i.castSucc).quotientNatProjection (s.step i.succ)).app
    (Discrete.mk PUnit.unit)

theorem gradedProjection_surjective (s : ObjectRepFiltration A n) (i : Fin n) :
    Function.Surjective (s.gradedProjection i).hom :=
  (s.step i.castSucc).quotientProjection_surjective (s.step i.succ) _

end ObjectRepFiltration

section Field

variable {k : Type uR} [Field k]

/-- Every graded quotient is irreducible, hence nonzero. -/
def ObjectRepFiltration.HasSimpleFactors {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) : Prop :=
  ∀ i, Representation.IsIrreducible (s.gradedRepresentation i).ρ

/-- Existence of an actual composition series of the specified length.
This is not a choice of a series or an assumption of its existence. -/
def HasCompositionSeriesLength (A : Rep.{uV} k G) (n : ℕ) : Prop :=
  ∃ s : ObjectRepFiltration A n, s.HasSimpleFactors

/-- A finite composition series whose number of factors is bounded by b. -/
def HasCompositionLengthAtMost (A : Rep.{uV} k G) (b : ℕ) : Prop :=
  ∃ n, n ≤ b ∧ HasCompositionSeriesLength A n

/-- Equality of composition factors with multiplicities, witnessed by actual
finite composition series and an isomorphism of each corresponding quotient.
The representations may have carriers in independent universes. -/
def HaveSameJordanHolderFactors (A : Rep.{uV} k G) (B : Rep.{uW} k G) : Prop :=
  ∃ (n : ℕ) (s : ObjectRepFiltration A n) (t : ObjectRepFiltration B n),
    s.HasSimpleFactors ∧ t.HasSimpleFactors ∧
    ∃ e : Equiv.Perm (Fin n),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv (t.gradedRepresentation (e i)).ρ)

/-- The bound predicate records an actual finite composition series. -/
theorem HasCompositionSeriesLength.lengthAtMost
    {A : Rep.{uV} k G} {n b : ℕ}
    (h : HasCompositionSeriesLength A n) (hn : n ≤ b) :
    HasCompositionLengthAtMost A b :=
  ⟨n, hn, h⟩

/-- Any given composition series matches itself, with the identity permutation. -/
theorem haveSameJordanHolderFactors_self {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hs : s.HasSimpleFactors) :
    HaveSameJordanHolderFactors A A := by
  refine ⟨n, s, s, hs, hs, 1, ?_⟩
  intro i
  exact ⟨Representation.Equiv.refl _⟩

/-- Reverse the matching permutation and each actual representation equivalence. -/
theorem haveSameJordanHolderFactors_symm {A : Rep.{uV} k G} {B : Rep.{uW} k G}
    (h : HaveSameJordanHolderFactors A B) : HaveSameJordanHolderFactors B A := by
  obtain ⟨n, s, t, hs, ht, e, he⟩ := h
  refine ⟨n, t, s, ht, hs, e.symm, ?_⟩
  intro i
  obtain ⟨f⟩ := he (e.symm i)
  rw [e.apply_symm_apply] at f
  exact ⟨f.symm⟩

end Field

end Langlands
