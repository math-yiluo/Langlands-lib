import Langlands.Automorphic.OperatorUnitaryFormComparison
import Langlands.Automorphic.OperatorHilbertCompletion
import Langlands.Representation.Unitary.CompletionSimilarity

/-! # Hilbert equivalences for independently supplied positive forms -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.InvariantPositiveForm

universe uG uM uV uW

/-- Retain the representation-equivalence coercion across the generic extension
boundary before specializing its algebraic carriers. -/
theorem exists_hilbertEquivalence_of_operator_inner
    {G : Type uG} [Group G] {M : Type uM} [Monoid M]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ M V} {ξ : Representation ℂ M W}
    (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ)
    (e : τ.Equiv ξ) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ v w, c.inner (e v) (e w) = (a : ℂ) * b.inner v w) :
    ∃ E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion,
      (∀ v, E (b.toHilbert v) = c.toHilbert (e v)) ∧
      (∀ x y, Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y) :=
  b.exists_hilbertEquivalence_of_inner c e.toLinearEquiv a ha hinner

/-- A covariance identity extends for continuous functions with the prescribed
values on the canonical dense embeddings. -/
theorem hilbertEquivalence_covariant_function
    {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ)
    (e : V → W) (E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion)
    (hE : ∀ v, E (b.toHilbert v) = c.toHilbert (e v))
    (A : V → V) (D : W → W)
    (Ac : b.HilbertCompletion → b.HilbertCompletion)
    (Dc : c.HilbertCompletion → c.HilbertCompletion)
    (hAc : Continuous Ac) (hDc : Continuous Dc)
    (hA : ∀ v, Ac (b.toHilbert v) = b.toHilbert (A v))
    (hD : ∀ w, Dc (c.toHilbert w) = c.toHilbert (D w))
    (he : ∀ v, e (A v) = D (e v)) (x : b.HilbertCompletion) :
    E (Ac x) = Dc (E x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq (E.continuous.comp hAc) (hDc.comp E.continuous)
  · intro v
    exact (congrArg E (hA v)).trans
      ((hE (A v)).trans ((congrArg c.toHilbert (he v)).trans
        ((hD (e v)).symm.trans (congrArg Dc (hE v)).symm)))

universe uI uJ

/-- Package comparison and two further covariance families before specializing
the algebraic carriers. Each completed action is an explicit continuous input. -/
theorem exists_hilbertEquivalence_of_operator_comparison
    {G : Type uG} [Group G] {M : Type uM} [Monoid M]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ M V} {ξ : Representation ℂ M W}
    {I : Type uI} {J : Type uJ}
    (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ) (e : τ.Equiv ξ)
    (hcompare : ∃ a : ℝ, 0 < a ∧ ∀ v w,
      c.inner (e v) (e w) = (a : ℂ) * b.inner v w)
    (A : I → V → V) (D : I → W → W)
    (Ac : I → b.HilbertCompletion → b.HilbertCompletion)
    (Dc : I → c.HilbertCompletion → c.HilbertCompletion)
    (hAc : ∀ i, Continuous (Ac i)) (hDc : ∀ i, Continuous (Dc i))
    (hA : ∀ i v, Ac i (b.toHilbert v) = b.toHilbert (A i v))
    (hD : ∀ i w, Dc i (c.toHilbert w) = c.toHilbert (D i w))
    (he : ∀ i v, e (A i v) = D i (e v))
    (B : J → V → V) (Q : J → W → W)
    (Bc : J → b.HilbertCompletion → b.HilbertCompletion)
    (Qc : J → c.HilbertCompletion → c.HilbertCompletion)
    (hBc : ∀ j, Continuous (Bc j)) (hQc : ∀ j, Continuous (Qc j))
    (hB : ∀ j v, Bc j (b.toHilbert v) = b.toHilbert (B j v))
    (hQ : ∀ j w, Qc j (c.toHilbert w) = c.toHilbert (Q j w))
    (heB : ∀ j v, e (B j v) = Q j (e v)) :
    ∃ (a : ℝ) (E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion),
      0 < a ∧ (∀ v, E (b.toHilbert v) = c.toHilbert (e v)) ∧
      (∀ x y, Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y) ∧
      (∀ i x, E (Ac i x) = Dc i (E x)) ∧
      (∀ j x, E (Bc j x) = Qc j (E x)) := by
  obtain ⟨a, ha, hinner⟩ := hcompare
  obtain ⟨E, hE, hEi⟩ := b.exists_hilbertEquivalence_of_operator_inner c e a ha hinner
  exact ⟨a, E, ha, hE, hEi,
    fun i => b.hilbertEquivalence_covariant_function c e E hE
      (A i) (D i) (Ac i) (Dc i) (hAc i) (hDc i) (hA i) (hD i) (he i),
    fun j => b.hilbertEquivalence_covariant_function c e E hE
      (B j) (Q j) (Bc j) (Qc j) (hBc j) (hQc j) (hB j) (hQ j) (heB j)⟩

end Langlands.InvariantPositiveForm

namespace Langlands.Automorphic.OperatorUnitaryFormCore

universe uG uK uM uV uW uX uY

/-- A continuous extension on the independently supplied completions, retaining
a positive inner-product ratio and both prescribed completed action families. -/
def HilbertFormComparison
    {G : Type uG} [Group G] {K : Type uK} [Group K] {M : Type uM} [Monoid M]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {X : Type uX} {Y : Type uY}
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {κ : Representation ℂ K V} {κ' : Representation ℂ K W}
    {D : X → Module.End ℂ V} {Q : Y → Module.End ℂ W}
    {τ : Representation ℂ M V} {ξ : Representation ℂ M W}
    (b : OperatorUnitaryFormCore ρ κ D) (c : OperatorUnitaryFormCore σ κ' Q)
    (e : τ.Equiv ξ) : Prop :=
    ∃ (a : ℝ)
      (E : b.finiteForm.HilbertCompletion ≃L[ℂ] c.finiteForm.HilbertCompletion),
      0 < a ∧
      (∀ v, E (b.finiteForm.toHilbert v) = c.finiteForm.toHilbert (e v)) ∧
      (∀ x y, Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y) ∧
      (∀ d x, E (b.completedFiniteOperator d x) = c.completedFiniteOperator d (E x)) ∧
      (∀ k x, E (b.completedCompactOperator k x) = c.completedCompactOperator k (E x))

/-- Independent positive cores with a scalar comparison give one continuous
extension intertwining the finite and compact completed actions. -/
theorem exists_hilbertEquivalence_of_comparison
    {G : Type uG} [Group G] {K : Type uK} [Group K] {M : Type uM} [Monoid M]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {X : Type uX} {Y : Type uY}
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {κ : Representation ℂ K V} {κ' : Representation ℂ K W}
    {D : X → Module.End ℂ V} {Q : Y → Module.End ℂ W}
    {τ : Representation ℂ M V} {ξ : Representation ℂ M W}
    (b : OperatorUnitaryFormCore ρ κ D) (c : OperatorUnitaryFormCore σ κ' Q)
    (e : τ.Equiv ξ)
    (hcompare : ∃ a : ℝ, 0 < a ∧ ∀ v w,
      c.finiteForm.inner (e v) (e w) = (a : ℂ) * b.finiteForm.inner v w)
    (heG : ∀ d v, e (ρ d v) = σ d (e v))
    (heK : ∀ k v, e (κ k v) = κ' k (e v)) :
    HilbertFormComparison b c e :=
  b.finiteForm.exists_hilbertEquivalence_of_operator_comparison c.finiteForm e hcompare
    (fun d v => ρ d v) (fun d w => σ d w)
    (fun d x => b.completedFiniteOperator d x) (fun d x => c.completedFiniteOperator d x)
    (fun d => (b.completedFiniteOperator d).continuous)
    (fun d => (c.completedFiniteOperator d).continuous)
    (fun d => b.completedFiniteOperator_toHilbert d)
    (fun d => c.completedFiniteOperator_toHilbert d) heG
    (fun k v => κ k v) (fun k w => κ' k w)
    (fun k x => b.completedCompactOperator k x) (fun k x => c.completedCompactOperator k x)
    (fun k => (b.completedCompactOperator k).continuous)
    (fun k => (c.completedCompactOperator k).continuous)
    (fun k => b.completedCompactOperator_toHilbert k)
    (fun k => c.completedCompactOperator_toHilbert k) heK

end Langlands.Automorphic.OperatorUnitaryFormCore

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance hilbertComparisonRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertComparisonContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertComparisonSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertComparisonFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertComparisonStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertComparisonSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S T : OperatorRealization F n}

/-- Completed finite translation respects every continuous extension of the
supplied full equivalence that agrees on the dense carriers. -/
theorem hilbertEquivalence_finite (b : S.UnitaryForm) (c : T.UnitaryForm)
    (e : S.Equivalence T)
    (E : b.finiteForm.HilbertCompletion ≃L[ℂ] c.finiteForm.HilbertCompletion)
    (hE : ∀ f, E (b.finiteForm.toHilbert f) = c.finiteForm.toHilbert (e f))
    (d : FiniteAdelicGL F n) (x : b.finiteForm.HilbertCompletion) :
    E (b.completedFiniteOperator d x) = c.completedFiniteOperator d (E x) :=
  b.finiteForm.hilbertEquivalence_covariant c.finiteForm e.toLinearEquiv E hE
    (S.finiteRepresentation d) (T.finiteRepresentation d)
    (b.finiteForm.completedLinearMap d) (c.finiteForm.completedLinearMap d)
    (b.finiteForm.completedLinearMap_toHilbert d)
    (c.finiteForm.completedLinearMap_toHilbert d)
    (OperatorRealization.Intertwiner.finite e.toIntertwiningMap d) x

/-- The same Hilbert equivalence intertwines completed compact translation. -/
theorem hilbertEquivalence_compact (b : S.UnitaryForm) (c : T.UnitaryForm)
    (e : S.Equivalence T)
    (E : b.finiteForm.HilbertCompletion ≃L[ℂ] c.finiteForm.HilbertCompletion)
    (hE : ∀ f, E (b.finiteForm.toHilbert f) = c.finiteForm.toHilbert (e f))
    (k : standardInfiniteCompact F n) (x : b.finiteForm.HilbertCompletion) :
    E (b.completedCompactOperator k x) = c.completedCompactOperator k (E x) :=
  b.finiteForm.hilbertEquivalence_covariant c.finiteForm e.toLinearEquiv E hE
    (S.compactRepresentation k) (T.compactRepresentation k)
    (b.compactForm.completedLinearMap k) (c.compactForm.completedLinearMap k)
    (b.compactForm.completedLinearMap_toHilbert k)
    (c.compactForm.completedLinearMap_toHilbert k)
    (OperatorRealization.Intertwiner.compact e.toIntertwiningMap k) x

/-- Pullback comparison, with the images retained explicitly. -/
theorem exists_pos_scalar_of_equivalence (b : S.UnitaryForm) (c : T.UnitaryForm)
    (e : S.Equivalence T) (hS : S.IsIrreducible) (hA : S.IsJointlyAdmissible) :
    ∃ a : ℝ, 0 < a ∧ ∀ f g : S.Space,
      c.inner (e f) (e g) =
        (a : ℂ) * b.inner f g := by
  have h := b.exists_pos_scalar (c.ofEquivalence e) hS hA
  simpa only [ofEquivalence_inner] using h


/-- A supplied algebraic similarity extends on the actual form completions. -/
theorem exists_hilbertEquivalence_of_inner_actual (b : S.UnitaryForm) (c : T.UnitaryForm)
    (e : S.Equivalence T) (a : ℝ) (ha : 0 < a)
    (hinner : ∀ f g : S.Space, c.inner (e f) (e g) =
      (a : ℂ) * b.inner f g) :
    ∃ E : b.finiteForm.HilbertCompletion ≃L[ℂ] c.finiteForm.HilbertCompletion,
      (∀ f, E (b.finiteForm.toHilbert f) = c.finiteForm.toHilbert (e f)) ∧
      (∀ x y, Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y) :=
  b.finiteForm.exists_hilbertEquivalence_of_operator_inner c.finiteForm e a ha hinner

/-- Independent forms on an irreducible jointly admissible realization permit
extension of every supplied full operator equivalence. -/
theorem exists_hilbertEquivalence (b : S.UnitaryForm) (c : T.UnitaryForm)
    (e : S.Equivalence T) (hS : S.IsIrreducible) (hA : S.IsJointlyAdmissible) :
    OperatorUnitaryFormCore.HilbertFormComparison b c e :=
  OperatorUnitaryFormCore.exists_hilbertEquivalence_of_comparison
    (G := FiniteAdelicGL F n) (K := standardInfiniteCompact F n)
    (M := automorphicOperatorAlgebra F n) (V := S.Space) (W := T.Space)
    (X := ArchimedeanGL.RealLieAlgebra F n) (Y := ArchimedeanGL.RealLieAlgebra F n)
    (ρ := S.finiteRepresentation) (σ := T.finiteRepresentation)
    (κ := S.compactRepresentation) (κ' := T.compactRepresentation)
    (D := fun X => S.envelopingAction
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)))
    (Q := fun X => T.envelopingAction
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)))
    (τ := S.representation) (ξ := T.representation) b c e
    (b.exists_pos_scalar_of_equivalence c e hS hA)
    (OperatorRealization.Intertwiner.finite e.toIntertwiningMap)
    (OperatorRealization.Intertwiner.compact e.toIntertwiningMap)

end OperatorRealization.UnitaryForm
/-- The actual full equivalence extends between arbitrary independently supplied
positive forms, retaining the positive inner-product scale and both group actions. -/
def OperatorHilbertFormComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) (S T : OperatorRealization F n),
    S.IsIrreducible → S.IsJointlyAdmissible → ∀ (b : S.UnitaryForm) (c : T.UnitaryForm)
      (e : S.Equivalence T),
      OperatorUnitaryFormCore.HilbertFormComparison b c e

/-- Hilbert form comparison for actual operator equivalences. -/
theorem operatorHilbertFormComparison : OperatorHilbertFormComparisonStatement.{u} := by
  intro F _ _ n S T hS hA b c e
  exact b.exists_hilbertEquivalence c e hS hA

end Langlands.Automorphic
