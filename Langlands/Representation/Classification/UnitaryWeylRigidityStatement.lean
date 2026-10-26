import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Classification.RelativeGenericityStatement
import Langlands.Representation.Twist.LeviRealPower
import Langlands.Representation.Unitary.Basic

/-!
# Real determinant exponents under unitary Weyl association

Derived coordinate rigidity and its relative-generic self-association consequence.
This proposition definition assumes neither its own proof nor a classification theorem.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW

/-- Actual Levi conjugation preserves block partitions and sizes; actual Weyl
association of real determinant twists of irreducible admissible unitarizable
representations identifies every coordinate exponent. In particular a generic
fine twist has no self-association outside the coarse block Weyl group. -/
def GLUnitaryWeylRealExponentRigidityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : BlockShape n,
      (∀ (C : BlockShape n) (w : Equiv.Perm (Fin n)),
        CuspidalSupport.ConjugatesLevi (F := F.Carrier) B C w →
        (∀ a b : Fin n,
          blockIndex C (w a) = blockIndex C (w b) ↔
            blockIndex B a = blockIndex B b) ∧
        ∀ a : Fin n, C.size (blockIndex C (w a)) = B.size (blockIndex B a)) ∧
      (∀ (C : BlockShape n) (V : Type uV) (W : Type uW)
        [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
        (ω : Representation ℂ (B.Levi F.Carrier) V)
        (η : Representation ℂ (C.Levi F.Carrier) W),
        ω.IsIrreducible → IsAdmissible ω → IsUnitarizable ω →
        η.IsIrreducible → IsAdmissible η → IsUnitarizable η →
        ∀ (s : Fin B.length → ℝ) (t : Fin C.length → ℝ)
          (w : Equiv.Perm (Fin n))
          (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) B C w),
          Nonempty ((CuspidalSupport.transport B C w hw
            (T.leviRealPowerTwist B s ω)).Equiv (T.leviRealPowerTwist C t η)) →
          ∀ a : Fin n, t (blockIndex C (w a)) = s (blockIndex B a)) ∧
      (∀ (S : BlockRefinement B) (V : Type uV)
        [AddCommGroup V] [Module ℂ V]
        (ω : Representation ℂ ((B.flatten S).Levi F.Carrier) V),
        ω.IsIrreducible → IsAdmissible ω → IsUnitarizable ω →
        ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
          IsRelativeGenericParameter (B.flatten S) B v₀ t →
          let C := B.flatten S
          let e : Fin C.length → ℝ :=
            fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1
          ∀ (w : Equiv.Perm (Fin n))
            (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C C w),
            Nonempty ((CuspidalSupport.transport C C w hw
              (T.leviRealPowerTwist C e ω)).Equiv (T.leviRealPowerTwist C e ω)) →
            w ∈ blockWeyl B)

end Langlands
