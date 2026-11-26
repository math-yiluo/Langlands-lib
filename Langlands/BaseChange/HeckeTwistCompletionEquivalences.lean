import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Representation.Twist.AlgebraProof

/-! # Local equivalences for twists of actual cuspidal presentations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Automorphic Correspondence GeneralLinear Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation

universe u uQ

local instance heckeTwistRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance heckeTwistContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance heckeTwistSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance heckeTwistFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance heckeTwistLocalGroup {K : Type u} [Field K] [NumberField K] {n : ℕ} {v : FinitePlace K}
    (A : LocalRealization K n v) : AddCommGroup A.Space := Submodule.addCommGroup _

section Local

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T : CuspidalOperatorRealization K r} (D : CuspidalSpectralPresentation.{u, uQ} T)
  (v : FinitePlace K) (ν χ : HeckeCharacter K)

/-- The actual finite component of the Hecke-twisted presentation is the
local determinant twist of the original component. -/
def heckeTwistAtCompletionEquiv :
    let η := quasicharacterBase v (ν.finiteComponent v)
    (twist (determinantQuasiCharacter (padicField v) r.succPNat η) (D.localComponent v).representation).Equiv
      ((D.heckeDeterminantTwist ν).localComponent v).representation := by
  intro η
  have hdet : determinantQuasiCharacter (padicField v) r.succPNat η =
      (ν.finiteLocalDeterminant (r + 1) v).toMonoidHom := by
    ext g : 1
    change (ν.finiteComponent v) (determinant g) = ν.finiteLocalDeterminant (r + 1) v g
    rw [HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det]
    rfl
  rw [hdet]
  exact ((D.localComponent v).heckeDeterminantTwistRepresentationEquiv ν).trans
    (D.heckeDeterminantTwistLocalComponentEquiv ν v).symm

/-- A double Hecke twist at a finite place is the twist by the product of
its two local determinant characters. -/
def heckeDoubleTwistAtCompletionEquiv :
    letI := (padicField v).canonicalTopologicalData.topology
    let η := quasicharacterBase v (ν.finiteComponent v)
    let θ := quasicharacterBase v (χ.finiteComponent v)
    (twist (determinantQuasiCharacter (padicField v) r.succPNat (θ * η))
      (D.localComponent v).representation).Equiv
      (((D.heckeDeterminantTwist ν).heckeDeterminantTwist χ).localComponent v).representation := by
  intro η θ
  let := (padicField v).canonicalTopologicalData.topology
  let d := determinantQuasiCharacter (padicField v) r.succPNat θ
  let e := determinantQuasiCharacter (padicField v) r.succPNat η
  have hdet : determinantQuasiCharacter (padicField v) r.succPNat (θ * η) = d * e :=
    MonoidHom.ext fun _ => rfl
  rw [hdet, ← twist_twist]
  exact (twistEquiv d (heckeTwistAtCompletionEquiv D v ν)).trans
    (heckeTwistAtCompletionEquiv (D.heckeDeterminantTwist ν) v χ)

/-- A character trivial at the given place preserves the original local action. -/
def heckeTwistAtCompletionEquiv_of_trivial (hν : ν.finiteComponent v = 1) :
    (D.localComponent v).representation.Equiv ((D.heckeDeterminantTwist ν).localComponent v).representation := by
  have hd : determinantQuasiCharacter (padicField v) r.succPNat (quasicharacterBase v (ν.finiteComponent v)) = 1 := by
    ext g : 1
    change (ν.finiteComponent v) (determinant g) = 1
    rw [hν]
    rfl
  simpa only [hd, twist_one] using heckeTwistAtCompletionEquiv D v ν

end Local

section Dual

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T Td Ud : CuspidalOperatorRealization K r}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (Dd : CuspidalSpectralPresentation.{u, uQ} Td)
  (Qd : CuspidalSpectralPresentation.{u, uQ} Ud)
  (hD : HasIrreducibleAdmissibleComponents D) (hDd : HasIrreducibleAdmissibleComponents Dd)
  (hQd : HasIrreducibleAdmissibleComponents Qd)
  (v : FinitePlace K) (ν : HeckeCharacter K)

include D hD hDd hQd

/-- Any actual contragredient presentation of a Hecke twist has the same
local representations as the inverse Hecke twist of an original dual. -/
theorem heckeTwistDualAtCompletionEquiv
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hUd : Ud.realization.IsContragredientOf (T.heckeDeterminantTwist ν).realization) :
    Nonempty ((((Dd.heckeDeterminantTwist ν⁻¹).localComponent v).representation).Equiv
      (Qd.localComponent v).representation) := by
  have hDt := D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ν hD
  have hDdt := Dd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ν⁻¹ hDd
  obtain ⟨a⟩ := cuspidalContragredientLocalCompatibility K r _ _ (hTd.heckeDeterminantTwist_inv ν)
    (D.heckeDeterminantTwist ν) (Dd.heckeDeterminantTwist ν⁻¹) v
    (hDt v).1 (hDt v).2 (hDdt v).1 (hDdt v).2
  obtain ⟨b⟩ := cuspidalContragredientLocalCompatibility K r _ _ hUd
    (D.heckeDeterminantTwist ν) Qd v (hDt v).1 (hDt v).2 (hQd v).1 (hQd v).2
  exact ⟨a.trans b.symm⟩

end Dual

end Langlands.BaseChange
