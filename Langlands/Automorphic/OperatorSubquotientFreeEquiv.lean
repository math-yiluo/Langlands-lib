import Langlands.Automorphic.OperatorSubquotientPullback
import Langlands.Automorphic.OperatorSubquotientLieAction
import Langlands.Automorphic.OperatorSubquotientPlaceAction

/-! # Descent preserving the full operator action -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped TensorProduct

universe uF uA uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance freeEquivRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance freeEquivContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance freeEquivSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance freeEquivFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance freeEquivStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- Descent along a surjective operator map retains equivariance for the entire
common monoid on the original model space. -/
theorem exists_irreducibleOperatorSubquotient_with_pullbackEquiv {r : ℕ}
    {A : Type uA} [Monoid A] (π : A →* automorphicOperatorAlgebra F (r + 1))
    (hπ : Function.Surjective π)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ A V}
    (hρ : ρ.IsIrreducible)
    (S : Subrepresentation ((stableAutomorphicAction F (r + 1)).comp π))
    (f : S.toRepresentation.IntertwiningMap ρ) (hf : Function.Surjective f) :
    ∃ Q : IrreducibleOperatorSubquotient F r,
      Nonempty (Representation.Equiv (Q.subquotient.representation.comp π) ρ) := by
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
  exact ⟨⟨Q, hQ⟩, ⟨e⟩⟩

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- Pull back the actual quotient action to the common free operator algebra. -/
abbrev freeRepresentation : Representation ℂ (FreeOperatorAlgebra F n) Q.Space :=
  Q.representation.comp (freeOperatorProjection F n).toMonoidHom

@[simp] theorem freeRepresentation_generator (i : OperatorIndex F n) :
    Q.freeRepresentation (FreeAlgebra.ι ℂ i) = Q.representation (operatorOfIndex F n i) := by
  change Q.representation (freeOperatorProjection F n (FreeAlgebra.ι ℂ i)) = _
  rw [freeOperatorProjection_ι]

@[simp] theorem freeRepresentation_finite (g : FiniteAdelicGL F n) :
    Q.freeRepresentation (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) = Q.finiteRepresentation g :=
  Q.freeRepresentation_generator _

@[simp] theorem freeRepresentation_realPlaceCompact
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    Q.freeRepresentation (FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (realPlaceCompactInclusion F n v k)))) =
      Q.realPlaceCompactRepresentation v k :=
  Q.freeRepresentation_generator _

@[simp] theorem freeRepresentation_complexPlaceCompact
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v})
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Q.freeRepresentation (FreeAlgebra.ι ℂ (Sum.inl (Sum.inr (complexPlaceCompactInclusion F n v k)))) =
      Q.complexPlaceCompactRepresentation v k :=
  Q.freeRepresentation_generator _

@[simp] theorem freeRepresentation_realPlaceLie
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    Q.freeRepresentation (FreeAlgebra.ι ℂ
      (Sum.inr (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)))) =
      Q.realPlaceLieAction v X :=
  Q.freeRepresentation_generator _

@[simp] theorem freeRepresentation_complexPlaceLie
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v})
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    Q.freeRepresentation (FreeAlgebra.ι ℂ
      (Sum.inr (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)))) =
      Q.complexPlaceLieAction v X :=
  Q.freeRepresentation_generator _

end OperatorSubquotient
end Langlands.Automorphic
