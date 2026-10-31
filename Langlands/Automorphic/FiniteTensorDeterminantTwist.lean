import Langlands.Automorphic.FiniteDeterminantTail
import Langlands.Automorphic.TensorPresentation

/-! # Genuine finite tensor presentations after determinant multiplication -/

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

local instance tensorTwistRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorTwistContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorTwistSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorTwistFormsGroup :
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
def determinantTwistExceptional (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    Finset (FinitePlace F) :=
  E ∪ χ.finiteDeterminantTail n hχ

/-- The local actions are the existing positive scalar twists by actual local characters. -/
def determinantTwistFactors (χ : HeckeCharacter F) :
    ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v) :=
  fun v => Langlands.twist (χ.finiteLocalDeterminant n v).toMonoidHom (ρ v)

include he in
theorem reference_fixed_on_determinantTwistExceptional
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (v : FinitePlace F) (hv : v ∉ determinantTwistExceptional (E := E) (n := n) χ hχ)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    ρ v g (e v) = e v :=
  he v (fun h => hv (Finset.mem_union_left _ h)) g hg

include he in
/-- The same reference vectors are fixed for the twisted factors outside the enlarged set. -/
theorem determinantTwistReference_fixed
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (v : FinitePlace F) (hv : v ∉ determinantTwistExceptional (E := E) (n := n) χ hχ)
    (g : FiniteLocalGL F n v) (hg : g ∈ localIntegral F n v) :
    determinantTwistFactors (ρ := ρ) χ v g (e v) = e v := by
  change (χ.finiteLocalDeterminant n v g : ℂ) • ρ v g (e v) = e v
  rw [χ.finiteLocalDeterminant_eq_one_outside_tail n hχ v
    (fun h => hv (Finset.mem_union_right _ h)) g hg, Units.val_one, one_smul]
  exact reference_fixed_on_determinantTwistExceptional (he := he) χ hχ v hv g hg

private theorem determinantTwistRepresentation_eq
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    tensorRepresentation F n (determinantTwistFactors (ρ := ρ) χ)
      (determinantTwistExceptional (E := E) (n := n) χ hχ) e
      (determinantTwistReference_fixed (he := he) χ hχ) =
      Langlands.twist
        ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
        (tensorRepresentation F n ρ
          (determinantTwistExceptional (E := E) (n := n) χ hχ) e
          (reference_fixed_on_determinantTwistExceptional (he := he) χ hχ)) := by
  let H := fun v => (localIntegral F n v).toSubgroup
  let E' := determinantTwistExceptional (E := E) (n := n) χ hχ
  have htail : ∀ t ∈ tailReferenceSubgroup H E',
      (χ.finiteRestrictedDeterminant n).toMonoidHom t = 1 :=
    fun t ht => χ.finiteDeterminantTail_trivial n hχ t
      (tailReferenceSubgroup_le_of_subset H Finset.subset_union_right ht)
  have hlocal : (fun v => Langlands.twist
      (localCharacter H (χ.finiteRestrictedDeterminant n).toMonoidHom v) (ρ v)) =
      determinantTwistFactors (ρ := ρ) χ := by
    funext v
    rw [HeckeCharacter.localCharacter_finiteRestrictedDeterminant]
    rfl
  have hgeneric := twistedRepresentation_eq H ρ E' e
    (reference_fixed_on_determinantTwistExceptional (he := he) χ hχ)
    (χ.finiteRestrictedDeterminant n).toMonoidHom htail
  have hrepresentation : representation H (determinantTwistFactors (ρ := ρ) χ) E' e
      (determinantTwistReference_fixed (he := he) χ hχ) =
      twistedRepresentation H ρ E' e
        (reference_fixed_on_determinantTwistExceptional (he := he) χ hχ)
        (χ.finiteRestrictedDeterminant n).toMonoidHom htail := by
    unfold twistedRepresentation
    congr 1
    exact hlocal.symm
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change representation H (determinantTwistFactors (ρ := ρ) χ) E' e
      (determinantTwistReference_fixed (he := he) χ hχ)
      (restrictedProductEquiv F n g) x =
    (χ.adelicDeterminant n (AdelicGL.ofFinite F n g) : ℂ) •
      representation H ρ E' e
        (reference_fixed_on_determinantTwistExceptional (he := he) χ hχ)
        (restrictedProductEquiv F n g) x
  rw [hrepresentation, hgeneric]
  change ((χ.finiteRestrictedDeterminant n) (restrictedProductEquiv F n g) : ℂ) •
    (_ : Space ℂ V E' e) = _
  rw [HeckeCharacter.finiteRestrictedDeterminant_apply]

variable (P : FiniteTensorPresentation F n ρ E e he S)

/-- Change only the cofinal finite stages of the supplied genuine presentation. -/
def determinantTwistEnlargedEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (tensorRepresentation F n ρ
      (determinantTwistExceptional (E := E) (n := n) χ hχ) e
      (reference_fixed_on_determinantTwistExceptional (he := he) χ hχ)).Equiv
      S.representation :=
  (tensorChangeEquiv ρ _ E e
    (reference_fixed_on_determinantTwistExceptional (he := he) χ hχ) he).trans P.equiv

/-- The tensor of the actual twisted local factors is equivalent to the actual
determinant-multiplied finite form space. -/
def determinantTwistEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (tensorRepresentation F n (determinantTwistFactors (ρ := ρ) χ)
      (determinantTwistExceptional (E := E) (n := n) χ hχ) e
      (determinantTwistReference_fixed (he := he) χ hχ)).Equiv
      (S.determinantTwist χ hχ).representation :=
  (Representation.Equiv.mk (LinearEquiv.refl ℂ _)
    (fun g => by rw [determinantTwistRepresentation_eq (he := he)]; rfl)).trans
    ((Langlands.twistEquiv
      ((χ.adelicDeterminant n).comp (AdelicGL.ofFinite F n)).toMonoidHom
      (P.determinantTwistEnlargedEquiv χ hχ)).trans
      (S.determinantTwistRepresentationEquiv χ hχ))

@[simp]
theorem determinantTwistEquiv_apply (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (x : Space ℂ V (determinantTwistExceptional (E := E) (n := n) χ hχ) e) :
    P.determinantTwistEquiv χ hχ x =
      S.determinantTwistEquiv χ hχ (P.determinantTwistEnlargedEquiv χ hχ x) := rfl

/-- On a finite stage the change of exceptions leaves all supplied tensor entries unchanged. -/
theorem determinantTwistEnlargedEquiv_pure
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (A : Index (determinantTwistExceptional (E := E) (n := n) χ hχ))
    (x : ∀ v : A.1, V v) :
    P.determinantTwistEnlargedEquiv χ hχ
        (pure (determinantTwistExceptional (E := E) (n := n) χ hχ) e A x) =
      P.equiv (pure E e ⟨A.1, Finset.subset_union_left.trans A.2⟩ x) := by
  change P.equiv (Langlands.RestrictedTensor.map _ E e e
    (fun v => (LinearEquiv.refl ℂ (V v)).toLinearMap) _
      (pure _ e A x)) = _
  rw [map_pure_of_preserves _ E e e _ _ A
    (Finset.subset_union_left.trans A.2) (fun _ _ => rfl)]
  rfl

@[simp]
theorem evaluate_determinantTwistEquiv
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (x : Space ℂ V (determinantTwistExceptional (E := E) (n := n) χ hχ) e)
    (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      ((S.determinantTwist χ hχ).toContinuous (P.determinantTwistEquiv χ hχ x)) a =
      (χ.adelicDeterminant n a : ℂ) *
        ContinuousRationalFunctions.evaluate F n
          (S.toContinuous (P.determinantTwistEnlargedEquiv χ hχ x)) a := rfl

/-- A genuine twisted presentation, using the unchanged vectors and enlarged exceptions. -/
def determinantTwist (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    FiniteTensorPresentation F n (determinantTwistFactors (ρ := ρ) χ)
      (determinantTwistExceptional (E := E) (n := n) χ hχ) e
      (determinantTwistReference_fixed (he := he) χ hχ)
      (S.determinantTwist χ hχ) where
  reference_nonzero v hv :=
    P.reference_nonzero v (fun h => hv (Finset.mem_union_left _ h))
  equiv := P.determinantTwistEquiv χ hχ

theorem evaluate_determinantTwist_pure
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (A : Index (determinantTwistExceptional (E := E) (n := n) χ hχ))
    (x : ∀ v : A.1, V v) (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      ((S.determinantTwist χ hχ).toContinuous
        ((P.determinantTwist χ hχ).equiv
          (pure (determinantTwistExceptional (E := E) (n := n) χ hχ) e A x))) a =
      (χ.adelicDeterminant n a : ℂ) *
        ContinuousRationalFunctions.evaluate F n
          (S.toContinuous (P.equiv (pure E e
            ⟨A.1, Finset.subset_union_left.trans A.2⟩ x))) a := by
  change ContinuousRationalFunctions.evaluate F n
    ((S.determinantTwist χ hχ).toContinuous
      (P.determinantTwistEquiv χ hχ (pure _ e A x))) a = _
  rw [evaluate_determinantTwistEquiv, determinantTwistEnlargedEquiv_pure]

end FiniteTensorPresentation
end Langlands.Automorphic
