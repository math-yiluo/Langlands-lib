import Langlands.Automorphic.FiniteTensorDeterminantTwist
import Langlands.Automorphic.HeckeTwist.FiniteTail
import Langlands.Automorphic.HeckeTwist.FiniteLocalTwist
import Langlands.Automorphic.TensorPresentation

/-! # Finite tensor presentations after multiplication by any Hecke determinant character

A finite tensor presentation of a finite realization yields one of its twist by
`χ ∘ det` for an arbitrary Hecke character `χ`: the local factors are twisted by the local
determinant characters, and the exceptional set is enlarged by the full integral tail of
`Langlands.Automorphic.HeckeTwist.FiniteTail`. This is the finite-order-free version of
`Langlands.Automorphic.FiniteTensorDeterminantTwist`.
-/

noncomputable section
open scoped Classical TensorProduct
universe uF uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance heckeTensorTwistRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorTwistContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorTwistSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTensorTwistFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

private def tensorChangeEquiv
    (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
    (E E' : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (he' : ∀ v ∉ E', ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v) :
    (tensorRepresentation F n ρ E e he).Equiv
      (tensorRepresentation F n ρ E' e he') :=
  Representation.Equiv.mk
    (Langlands.RestrictedTensor.congr E E' e e
      (fun v => LinearEquiv.refl ℂ (V v))
      (Filter.Eventually.of_forall fun _ => rfl))
    (fun g => (tensorIntertwiner F n ρ ρ E E' e e he he'
      (fun v => Representation.IntertwiningMap.id (ρ v))
      (Filter.Eventually.of_forall fun _ => rfl)).isIntertwining' g)

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}

/-- Enlarge the original tensor exceptions by the actual full character-tail bound. -/
def heckeDeterminantTwistExceptional (χ : HeckeCharacter F) :
    Finset (FinitePlace F) :=
  E ∪ χ.finiteHeckeDeterminantTail n

include he in
theorem reference_fixed_on_heckeDeterminantTwistExceptional
    (χ : HeckeCharacter F)
    (v : FinitePlace F) (hv : v ∉ heckeDeterminantTwistExceptional (E := E) (n := n) χ)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    ρ v g (e v) = e v :=
  he v (fun h => hv (Finset.mem_union_left _ h)) g hg

include he in
/-- The same reference vectors are fixed for the twisted factors outside the enlarged set. -/
theorem heckeDeterminantTwistReference_fixed
    (χ : HeckeCharacter F)
    (v : FinitePlace F) (hv : v ∉ heckeDeterminantTwistExceptional (E := E) (n := n) χ)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    determinantTwistFactors (ρ := ρ) χ v g (e v) = e v := by
  change (χ.finiteLocalDeterminant n v g : ℂ) • ρ v g (e v) = e v
  rw [χ.finiteLocalHeckeDeterminant_eq_one_outside_tail n v
    (fun h => hv (Finset.mem_union_right _ h)) g hg, Units.val_one, one_smul]
  exact reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ v hv g hg

private theorem determinantTwistRepresentation_eq
    (χ : HeckeCharacter F) :
    tensorRepresentation F n (determinantTwistFactors (ρ := ρ) χ)
      (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e
      (heckeDeterminantTwistReference_fixed (he := he) χ) =
      Langlands.twist
        ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
        (tensorRepresentation F n ρ
          (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e
          (reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ)) := by
  let H := fun v => (localIntegral F n v).toSubgroup
  let E' := heckeDeterminantTwistExceptional (E := E) (n := n) χ
  have htail : ∀ t ∈ tailReferenceSubgroup H E',
      (χ.finiteRestrictedDeterminant n).toMonoidHom t = 1 :=
    fun t ht => χ.finiteHeckeDeterminantTail_trivial n t
      (tailReferenceSubgroup_le_of_subset H Finset.subset_union_right ht)
  have hlocal : (fun v => Langlands.twist
      (localCharacter H (χ.finiteRestrictedDeterminant n).toMonoidHom v) (ρ v)) =
      determinantTwistFactors (ρ := ρ) χ := by
    funext v
    rw [HeckeCharacter.localCharacter_finiteRestrictedDeterminant]
    rfl
  have hgeneric := twistedRepresentation_eq H ρ E' e
    (reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ)
    (χ.finiteRestrictedDeterminant n).toMonoidHom htail
  have hrepresentation : representation H (determinantTwistFactors (ρ := ρ) χ) E' e
      (heckeDeterminantTwistReference_fixed (he := he) χ) =
      twistedRepresentation H ρ E' e
        (reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ)
        (χ.finiteRestrictedDeterminant n).toMonoidHom htail := by
    unfold twistedRepresentation
    congr 1
    exact hlocal.symm
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change representation H (determinantTwistFactors (ρ := ρ) χ) E' e
      (heckeDeterminantTwistReference_fixed (he := he) χ)
      (restrictedProductEquiv F n g) x =
    (χ.adelicDeterminant n (AdelicGL.ofFinite F n g) : ℂ) •
      representation H ρ E' e
        (reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ)
        (restrictedProductEquiv F n g) x
  rw [hrepresentation, hgeneric]
  change ((χ.finiteRestrictedDeterminant n) (restrictedProductEquiv F n g) : ℂ) •
    (_ : Space ℂ V E' e) = _
  rw [HeckeCharacter.finiteRestrictedDeterminant_apply]

variable (P : FiniteTensorPresentation F n ρ E e he S)

/-- Change only the cofinal finite stages of the supplied genuine presentation. -/
def heckeDeterminantTwistEnlargedEquiv (χ : HeckeCharacter F) :
    (tensorRepresentation F n ρ
      (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e
      (reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ)).Equiv
      S.representation :=
  (tensorChangeEquiv ρ _ E e
    (reference_fixed_on_heckeDeterminantTwistExceptional (he := he) χ) he).trans P.equiv

/-- The tensor of the actual twisted local factors is equivalent to the actual
determinant-multiplied finite form space. -/
def heckeDeterminantTwistEquiv (χ : HeckeCharacter F) :
    (tensorRepresentation F n (determinantTwistFactors (ρ := ρ) χ)
      (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e
      (heckeDeterminantTwistReference_fixed (he := he) χ)).Equiv
      (S.heckeDeterminantTwist χ).representation :=
  (Representation.Equiv.mk (LinearEquiv.refl ℂ _)
    (fun g => by rw [determinantTwistRepresentation_eq (he := he)]; rfl)).trans
    ((Langlands.twistEquiv
      ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
      (P.heckeDeterminantTwistEnlargedEquiv χ)).trans
      (S.heckeDeterminantTwistRepresentationEquiv χ))

@[simp]
theorem heckeDeterminantTwistEquiv_apply (χ : HeckeCharacter F)
    (x : Space ℂ V (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e) :
    P.heckeDeterminantTwistEquiv χ x =
      S.heckeDeterminantTwistEquiv χ (P.heckeDeterminantTwistEnlargedEquiv χ x) := rfl

/-- On a finite stage the change of exceptions leaves all supplied tensor entries unchanged. -/
theorem heckeDeterminantTwistEnlargedEquiv_pure
    (χ : HeckeCharacter F)
    (A : Index (heckeDeterminantTwistExceptional (E := E) (n := n) χ))
    (x : ∀ v : A.1, V v) :
    P.heckeDeterminantTwistEnlargedEquiv χ
        (pure (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e A x) =
      P.equiv (pure E e ⟨A.1, Finset.subset_union_left.trans A.2⟩ x) := by
  change P.equiv (Langlands.RestrictedTensor.map _ E e e
    (fun v => (LinearEquiv.refl ℂ (V v)).toLinearMap) _
      (pure _ e A x)) = _
  rw [map_pure_of_preserves _ E e e _ _ A
    (Finset.subset_union_left.trans A.2) (fun _ _ => rfl)]
  rfl

@[simp]
theorem evaluate_heckeDeterminantTwistEquiv
    (χ : HeckeCharacter F)
    (x : Space ℂ V (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e)
    (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      ((S.heckeDeterminantTwist χ).toContinuous (P.heckeDeterminantTwistEquiv χ x)) a =
      (χ.adelicDeterminant n a : ℂ) *
        ContinuousRationalFunctions.evaluate F n
          (S.toContinuous (P.heckeDeterminantTwistEnlargedEquiv χ x)) a := rfl

/-- A genuine twisted presentation, using the unchanged vectors and enlarged exceptions. -/
def heckeDeterminantTwist (χ : HeckeCharacter F) :
    FiniteTensorPresentation F n (determinantTwistFactors (ρ := ρ) χ)
      (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e
      (heckeDeterminantTwistReference_fixed (he := he) χ)
      (S.heckeDeterminantTwist χ) where
  reference_nonzero v hv :=
    P.reference_nonzero v (fun h => hv (Finset.mem_union_left _ h))
  equiv := P.heckeDeterminantTwistEquiv χ

theorem evaluate_heckeDeterminantTwist_pure
    (χ : HeckeCharacter F)
    (A : Index (heckeDeterminantTwistExceptional (E := E) (n := n) χ))
    (x : ∀ v : A.1, V v) (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      ((S.heckeDeterminantTwist χ).toContinuous
        ((P.heckeDeterminantTwist χ).equiv
          (pure (heckeDeterminantTwistExceptional (E := E) (n := n) χ) e A x))) a =
      (χ.adelicDeterminant n a : ℂ) *
        ContinuousRationalFunctions.evaluate F n
          (S.toContinuous (P.equiv (pure E e
            ⟨A.1, Finset.subset_union_left.trans A.2⟩ x))) a := by
  change ContinuousRationalFunctions.evaluate F n
    ((S.heckeDeterminantTwist χ).toContinuous
      (P.heckeDeterminantTwistEquiv χ (pure _ e A x))) a = _
  rw [evaluate_heckeDeterminantTwistEquiv, heckeDeterminantTwistEnlargedEquiv_pure]

end FiniteTensorPresentation
end Langlands.Automorphic
