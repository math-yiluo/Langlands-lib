import Langlands.Automorphic.OperatorEquivalence
import Langlands.Representation.Unitary.Basic

/-! # Positive forms on actual finite, compact and differential realizations -/

noncomputable section
universe uF uV uW uG uK uX
set_option autoImplicit false

namespace Langlands.Automorphic

/-- Inverse covariance of a linear equivalence intertwining two operators. -/
theorem inverse_operator
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (A : Module.End ℂ V) (B : Module.End ℂ W)
    (he : ∀ v, B (e v) = e (A v)) (w : W) :
    e.symm (B w) = A (e.symm w) := by
  obtain ⟨v, rfl⟩ := e.surjective w
  exact (congrArg e.symm (he v)).trans (e.symm_apply_apply (A v)) |>.trans
    (congrArg A (e.symm_apply_apply v)).symm

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance unitaryFormRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance unitaryFormContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance unitaryFormSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance unitaryFormFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance unitaryFormStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- A positive form for two group actions and a family of infinitesimal operators.
The actual automorphic form below specializes every action and operator. -/
structure OperatorUnitaryFormCore {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {G : Type uG} [Monoid G] {K : Type uK} [Monoid K] {X : Type uX}
    (ρ : Representation ℂ G V) (κ : Representation ℂ K V) (D : X → Module.End ℂ V) where
  finiteForm : Langlands.InvariantPositiveForm ρ
  compact_invariant (k : K) (f g : V) :
    finiteForm.inner (κ k f) (κ k g) = finiteForm.inner f g
  real_skew (x : X) (f g : V) :
    finiteForm.inner (D x f) g + finiteForm.inner f (D x g) = 0

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance unitaryFormSourceGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance unitaryFormTargetGroup : AddCommGroup T.Space := Submodule.addCommGroup _

/-- One positive definite Hermitian form, invariant under finite and compact
translations and infinitesimally invariant under every actual real Lie direction. -/
abbrev UnitaryForm :=
  OperatorUnitaryFormCore S.finiteRepresentation S.compactRepresentation
    (fun X : ArchimedeanGL.RealLieAlgebra F n => S.envelopingAction
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)))

/-- Algebraic unitarizability of this actual realization, retaining the genuine
real Lie action. No Hilbert globalization or occurrence is asserted. -/
def IsUnitarizable : Prop := Nonempty S.UnitaryForm

namespace UnitaryForm

variable {S T}

/-- The single Hermitian form used by all three invariance conditions. -/
abbrev inner (b : S.UnitaryForm) : S.Space → S.Space → ℂ := b.finiteForm.inner

/-- The same positive form is invariant for the actual compact restriction. -/
def compactForm (b : S.UnitaryForm) :
    Langlands.InvariantPositiveForm S.compactRepresentation where
  toInnerProductCore := b.finiteForm.toInnerProductCore
  invariant := b.compact_invariant

@[simp] theorem compactForm_inner (b : S.UnitaryForm) (f g : S.Space) :
    b.compactForm.inner f g = b.inner f g := rfl

/-- Pull back the same form along an injective intertwiner of every operator. -/
def comap (b : T.UnitaryForm) (L : S.Intertwiner T) (hL : Function.Injective L) :
    S.UnitaryForm where
  finiteForm := b.finiteForm.comap L.finiteRestriction hL
  compact_invariant k f g := by
    exact (congrArg₂ (fun u v : T.Space => b.inner u v)
      (L.compact k f) (L.compact k g)).trans
        (b.compact_invariant k (L f) (L g))
  real_skew X f g := by
    exact (congrArg₂ (fun u v : T.Space => b.inner u (L g) + b.inner (L f) v)
      (L.differential
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) f)
      (L.differential
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) g)).trans
          (b.real_skew X (L f) (L g))

@[simp] theorem comap_inner (b : T.UnitaryForm) (L : S.Intertwiner T)
    (hL : Function.Injective L) (f g : S.Space) :
    (b.comap L hL).inner f g = b.inner (L f) (L g) := rfl

/-- Transport a form through a genuine whole-operator equivalence. -/
def ofEquivalence (b : T.UnitaryForm) (e : S.Equivalence T) : S.UnitaryForm :=
  b.comap e.toIntertwiningMap e.toLinearEquiv.injective

@[simp] theorem ofEquivalence_inner (b : T.UnitaryForm) (e : S.Equivalence T)
    (f g : S.Space) :
    (b.ofEquivalence e).inner f g = b.inner (e f) (e g) := rfl

end UnitaryForm

namespace IsUnitarizable

variable {S T}

theorem of_injective (hT : T.IsUnitarizable)
    (L : S.Intertwiner T) (hL : Function.Injective L) : S.IsUnitarizable := by
  obtain ⟨b⟩ := hT
  exact ⟨b.comap L hL⟩

/-- Forgetting the compact and differential conditions preserves the finite form. -/
theorem finite (hS : S.IsUnitarizable) :
    Langlands.IsUnitarizable S.finiteRepresentation := by
  obtain ⟨b⟩ := hS
  exact ⟨b.finiteForm⟩

theorem compact (hS : S.IsUnitarizable) :
    Langlands.IsUnitarizable S.compactRepresentation := by
  obtain ⟨b⟩ := hS
  exact ⟨b.compactForm⟩

/-- The finite form is transported to the actual embedded form image. -/
theorem finiteImage (hS : S.IsUnitarizable) :
    Langlands.IsUnitarizable S.toFiniteRealization.representation :=
  (Langlands.isUnitarizable_iff_of_equiv S.finiteEquiv).mp hS.finite

end IsUnitarizable

theorem isUnitarizable_iff_of_equivalence (e : S.Equivalence T) :
    S.IsUnitarizable ↔ T.IsUnitarizable := by
  constructor
  · rintro ⟨b⟩
    exact ⟨b.ofEquivalence e.symm⟩
  · rintro ⟨b⟩
    exact ⟨b.ofEquivalence e⟩

/-- Unitarizability is a property of the actual whole-operator isomorphism class. -/
def IsoClass.IsUnitarizable (c : IsoClass F n) : Prop :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun S : OperatorRealization F n => S.IsUnitarizable)
    (fun S T (h : Nonempty (S.Equivalence T)) =>
      h.elim (fun e => propext (isUnitarizable_iff_of_equivalence S T e))) c

@[simp] theorem isUnitarizable_isoClass :
    S.isoClass.IsUnitarizable ↔ S.IsUnitarizable := Iff.rfl

end OperatorRealization
end Langlands.Automorphic
