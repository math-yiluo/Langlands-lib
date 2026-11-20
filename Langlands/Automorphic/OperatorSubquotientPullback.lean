import Langlands.Automorphic.IrreducibleOperatorSubquotient
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Filtration.LengthTwoMatching
import Mathlib.Algebra.FreeAlgebra

/-! # Descending a quotient from a common operator algebra -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe uF uA uV

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- One formal generator for each translation and differential operator. -/
abbrev OperatorIndex :=
  (FiniteAdelicGL F n ⊕ standardInfiniteCompact F n) ⊕ ArchimedeanGL.EnvelopingAlgebra F n

/-- A common algebra for operator actions before relation descent. -/
abbrev FreeOperatorAlgebra := FreeAlgebra ℂ (OperatorIndex F n)

/-- The actual operator corresponding to each formal generator. -/
def operatorOfIndex : OperatorIndex F n → automorphicOperatorAlgebra F n :=
  Sum.elim (Sum.elim (finiteOperator F n) (compactOperator F n)) (differentialOperator F n)

/-- Evaluate the formal generators as actual adelic operators. -/
def freeOperatorProjection : FreeOperatorAlgebra F n →ₐ[ℂ] automorphicOperatorAlgebra F n :=
  FreeAlgebra.lift ℂ (operatorOfIndex F n)

@[simp]
theorem freeOperatorProjection_ι (i : OperatorIndex F n) :
    freeOperatorProjection F n (FreeAlgebra.ι ℂ i) = operatorOfIndex F n i :=
  FreeAlgebra.lift_ι_apply _ _

theorem freeOperatorProjection_surjective :
    Function.Surjective (freeOperatorProjection F n) := by
  let project := (automorphicOperatorAlgebra F n).val.comp (freeOperatorProjection F n)
  let gen : OperatorIndex F n → FiniteSmoothEnd F n := fun i => (operatorOfIndex F n i).val
  have hproject : project = FreeAlgebra.lift ℂ gen := by
    apply FreeAlgebra.hom_ext
    funext i
    change (freeOperatorProjection F n (FreeAlgebra.ι ℂ i)).val =
      FreeAlgebra.lift ℂ gen (FreeAlgebra.ι ℂ i)
    rw [freeOperatorProjection_ι, FreeAlgebra.lift_ι_apply]
  have hgen : Set.range gen = automorphicOperatorGenerators F n := by
    ext a
    constructor
    · rintro ⟨(⟨d⟩ | ⟨k⟩) | u, rfl⟩
      · exact Or.inl (Or.inl ⟨d, rfl⟩)
      · exact Or.inl (Or.inr ⟨k, rfl⟩)
      · exact Or.inr ⟨u, rfl⟩
    · rintro ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
      · exact ⟨Sum.inl (Sum.inl d), rfl⟩
      · exact ⟨Sum.inl (Sum.inr k), rfl⟩
      · exact ⟨Sum.inr u, rfl⟩
  have hrange : project.range = automorphicOperatorAlgebra F n := by
    rw [hproject, ← Algebra.adjoin_range_eq_range_freeAlgebra_lift, hgen]
    rfl
  intro a
  have ha : a.val ∈ project.range := hrange.symm ▸ a.property
  obtain ⟨x, hx⟩ := ha
  exact ⟨x, Subtype.ext hx⟩

variable {F}

/-- A surjective intertwiner for a common operator monoid produces an actual
irreducible automorphic quotient when the monoid covers the concrete algebra.
The equivalence uses the given finite action through the lifts of its operators. -/
theorem exists_irreducibleOperatorSubquotient_of_pullback {r : ℕ}
    {A : Type uA} [Monoid A] (π : A →* automorphicOperatorAlgebra F (r + 1))
    (hπ : Function.Surjective π)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ A V}
    (hρ : ρ.IsIrreducible)
    (S : Subrepresentation ((stableAutomorphicAction F (r + 1)).comp π))
    (f : S.toRepresentation.IntertwiningMap ρ) (hf : Function.Surjective f)
    (fin : FiniteAdelicGL F (r + 1) → A) (hfin : ∀ d, π (fin d) = finiteOperator F (r + 1) d)
    (ρfin : Representation ℂ (FiniteAdelicGL F (r + 1)) V) (hρfin : ∀ d, ρ (fin d) = ρfin d) :
    ∃ Q : IrreducibleOperatorSubquotient F r, Nonempty (Q.subquotient.finiteRepresentation.Equiv ρfin) := by
  let upper : OperatorRealization F (r + 1) :=
    CuspidalSupport.subrepresentationCompOrderIso (stableAutomorphicAction F (r + 1)) π hπ S
  let lower : Subrepresentation upper.representation :=
    CuspidalSupport.subrepresentationCompOrderIso upper.representation π hπ f.ker
  let Q : OperatorSubquotient F (r + 1) := ⟨upper, lower⟩
  let pulledBack : Representation ℂ A Q.Space := Q.representation.comp π
  let e : pulledBack.Equiv ρ :=
    Representation.Equiv.mk (f.toLinearMap.quotKerEquivOfSurjective hf) (fun a => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ f a v)
  have hQ : Q.IsIrreducible :=
    (CuspidalSupport.isIrreducible_comp_iff Q.representation π hπ).mp
      (LengthTwo.isIrreducible_of_equiv e.symm hρ)
  have efin : Q.finiteRepresentation.Equiv ρfin :=
    Representation.Equiv.mk e.toLinearEquiv fun d => by
      calc
        _ = e.toLinearEquiv.toLinearMap.comp (pulledBack (fin d)) :=
          congrArg (fun a => e.toLinearEquiv.toLinearMap.comp (Q.representation a))
            (hfin d).symm
        _ = (ρ (fin d)).comp e.toLinearEquiv.toLinearMap := e.isIntertwining' (fin d)
        _ = _ := congrArg (fun a => a.comp e.toLinearEquiv.toLinearMap) (hρfin d)
  exact ⟨⟨Q, hQ⟩, ⟨efin⟩⟩

end Langlands.Automorphic
