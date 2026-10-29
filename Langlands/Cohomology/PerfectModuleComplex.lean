import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Perfect complexes of modules and scalar extension of representatives

Bounded finite projective and finite free cochain complexes of modules over a
commutative ring, perfect objects of the actual derived category, and ordinary
degreewise extension of scalars of complexes. No derived tensor is defined.
-/

universe u v

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

variable {R : Type u} [CommRing R]

/-- A bounded cochain complex whose terms are finite projective modules. -/
def IsStrictlyPerfect (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
    ∀ i : ℤ, Module.Finite R (K.X i) ∧ Module.Projective R (K.X i)

/-- A bounded cochain complex whose terms are finite free modules. -/
def IsFiniteFree (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
    ∀ i : ℤ, Module.Finite R (K.X i) ∧ Module.Free R (K.X i)

/-- Perfection in the actual derived category means existence of a bounded
finite projective representative, up to isomorphism in that category. -/
def IsPerfect [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    (E : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
    IsStrictlyPerfect K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- Ordinary degreewise extension of scalars on cochain complexes. -/
def baseChange {S : Type u} [CommRing S] (φ : R →+* S) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- A finite free representative is in particular finite projective. -/
lemma isStrictlyPerfect_of_isFiniteFree
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (h : IsFiniteFree K) :
    IsStrictlyPerfect K := by
  refine ⟨h.1, fun i ↦ ?_⟩
  have := (h.2 i).1
  have := (h.2 i).2
  exact ⟨inferInstance, inferInstance⟩

/-- A strictly perfect complex represents a perfect derived object. -/
lemma isPerfect_Q_obj [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (h : IsStrictlyPerfect K) :
    IsPerfect (DerivedCategory.Q.obj K) :=
  ⟨K, h, ⟨Iso.refl _⟩⟩

/-- Perfection is invariant under actual derived isomorphism. -/
lemma isPerfect_iff_of_iso [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    {E F : DerivedCategory (ModuleCat.{u} R)} (e : E ≅ F) :
    IsPerfect E ↔ IsPerfect F := by
  constructor
  · rintro ⟨K, hK, ⟨a⟩⟩
    exact ⟨K, hK, ⟨a ≪≫ e⟩⟩
  · rintro ⟨K, hK, ⟨a⟩⟩
    exact ⟨K, hK, ⟨a ≪≫ e.symm⟩⟩

end Langlands.Cohomology.ModuleComplex
