import Langlands.Representation.Classification.UnitaryWeylRigidityStatement
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generic fine-twist Weyl self-association counts

The support and finite-cardinality consequences of real exponent rigidity.
This module defines a proposition; its proof is separate.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Every actual minimal self-association of a relatively generic fine twist
belongs to the coarse block Weyl group, so restricting to that group preserves
the finite cardinality. -/
def GLRelativeGenericWeylCountStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ω : Representation ℂ ((B.flatten S).Levi F.Carrier) V),
      ω.IsIrreducible → IsAdmissible ω → IsUnitarizable ω →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        IsRelativeGenericParameter (B.flatten S) B v₀ t →
        let C := B.flatten S
        let σ := T.leviRealPowerTwist C
          (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω
        (∀ w : CuspidalSupport.AssociatingPermutations C C σ σ,
          w.val.val.val ∈ blockWeyl B) ∧
        Nat.card {w : CuspidalSupport.AssociatingPermutations C C σ σ //
          w.val.val.val ∈ blockWeyl B} =
          Nat.card (CuspidalSupport.AssociatingPermutations C C σ σ)

end Langlands
