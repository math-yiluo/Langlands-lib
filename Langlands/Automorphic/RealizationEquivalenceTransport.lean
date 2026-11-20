import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.CuspidalConjugateRealization
import Langlands.Automorphic.AssociatedGammaAutomorphicTwist

/-!
# Transport of equivalences of realizations

* `OperatorRealization.nonempty_equivalence_conjugate`: equivalent realizations have
  equivalent complex conjugates; `nonempty_equivalence_conjugate_conjugate`: a realization is
  equivalent to its double conjugate.
* `OperatorRealization.nonempty_equivalence_heckeDeterminantTwist`: equivalent realizations
  have equivalent Hecke determinant twists.

The uniqueness of contragredient realizations is the Library's
`OperatorRealization.IsContragredientOf.nonempty_equivalence` (module
`Langlands.Automorphic.ContragredientUniqueness`).
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Automorphic

open NumberField Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance realizationTransportRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance realizationTransportContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance realizationTransportSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance realizationTransportFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance realizationTransportStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance realizationTransportSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

set_option maxHeartbeats 4000000 in
/-- Equivalent realizations have equivalent complex conjugates. -/
theorem nonempty_equivalence_conjugate {S T : OperatorRealization F n}
    (h : Nonempty (S.Equivalence T)) : Nonempty (S.conjugate.Equivalence T.conjugate) := by
  obtain ⟨e⟩ := h
  let e' : S.conjugate.Space ≃ₗ[ℂ] T.conjugate.Space :=
    S.conjugateEquiv.symm.trans (e.toLinearEquiv.trans T.conjugateEquiv)
  have he' : ∀ f : S.Space, e' (S.conjugateEquiv f) = T.conjugateEquiv (e f) := by
    intro f
    change T.conjugateEquiv (e (S.conjugateEquiv.symm (S.conjugateEquiv f))) = _
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨Representation.Equiv.mk e' fun a => LinearMap.ext fun y => ?_⟩
  obtain ⟨f, rfl⟩ := S.conjugateEquiv.surjective y
  change e' (S.conjugate.representation a (S.conjugateEquiv f)) =
    T.conjugate.representation a (e' (S.conjugateEquiv f))
  rw [S.conjugateEquiv_operatorAction, he', he', T.conjugateEquiv_operatorAction]
  congr 1
  exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap _ f

set_option maxHeartbeats 4000000 in
/-- A realization is equivalent to its double complex conjugate. -/
theorem nonempty_equivalence_conjugate_conjugate (S : OperatorRealization F n) :
    Nonempty (S.Equivalence S.conjugate.conjugate) := by
  let e : S.Space ≃ₗ[ℂ] S.conjugate.conjugate.Space :=
    S.conjugateEquiv.trans S.conjugate.conjugateEquiv
  refine ⟨Representation.Equiv.mk e fun a => LinearMap.ext fun f => ?_⟩
  change S.conjugate.conjugateEquiv (S.conjugateEquiv (S.representation a f)) =
    S.conjugate.conjugate.representation a (S.conjugate.conjugateEquiv (S.conjugateEquiv f))
  rw [S.conjugate.conjugateEquiv_operatorAction, S.conjugateEquiv_operatorAction,
    operatorConj_operatorConj]

set_option maxHeartbeats 4000000 in
/-- Equivalent realizations have equivalent Hecke determinant twists. -/
theorem nonempty_equivalence_heckeDeterminantTwist {S T : OperatorRealization F n}
    (χ : HeckeCharacter F) (h : Nonempty (S.Equivalence T)) :
    Nonempty ((S.heckeDeterminantTwist χ).Equivalence (T.heckeDeterminantTwist χ)) := by
  obtain ⟨e⟩ := h
  let e' : (S.heckeDeterminantTwist χ).Space ≃ₗ[ℂ] (T.heckeDeterminantTwist χ).Space :=
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv.symm.trans
      (e.toLinearEquiv.trans (T.heckeDeterminantTwistEquiv χ).toLinearEquiv)
  have he' : ∀ f : S.Space,
      e' (S.heckeDeterminantTwistEquiv χ f) = T.heckeDeterminantTwistEquiv χ (e f) := by
    intro f
    change T.heckeDeterminantTwistEquiv χ (e ((S.heckeDeterminantTwistEquiv χ).symm
      (S.heckeDeterminantTwistEquiv χ f))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨Representation.Equiv.mk e' fun a => LinearMap.ext fun y => ?_⟩
  obtain ⟨f, rfl⟩ := (S.heckeDeterminantTwistEquiv χ).surjective y
  change e' ((S.heckeDeterminantTwist χ).representation a (S.heckeDeterminantTwistEquiv χ f)) =
    (T.heckeDeterminantTwist χ).representation a (e' (S.heckeDeterminantTwistEquiv χ f))
  rw [S.heckeDeterminantTwistEquiv_operatorAction, he', he',
    T.heckeDeterminantTwistEquiv_operatorAction]
  congr 1
  exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap _ f

end OperatorRealization

end Langlands.Automorphic
