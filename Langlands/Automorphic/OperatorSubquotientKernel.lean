import Langlands.Automorphic.IrreducibleOperatorSubquotient
import Langlands.Representation.Filtration.LengthTwoMatching

/-! # Actual automorphic subquotients from surjective operator intertwiners -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

universe uF uV

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

private local instance rationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
private local instance continuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance smoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
private local instance formsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
private local instance stableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance realizationGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorSubquotient

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (automorphicOperatorAlgebra F n) V}
variable {S : OperatorRealization F n} (f : S.representation.IntertwiningMap ρ)

/-- Retain the actual numerator of a map and use its invariant kernel as denominator. -/
def ofIntertwinerKernel : OperatorSubquotient F n :=
  ⟨S, f.ker⟩

/-- A surjective map identifies the actual kernel quotient with its target. -/
def ofIntertwinerKernelEquiv (hf : Function.Surjective f) :
    (ofIntertwinerKernel f).representation.Equiv ρ := by
  let Q := ofIntertwinerKernel f
  let g := Q.lift f (le_refl f.ker)
  refine g.ofBijective ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨s, rfl⟩ := Q.projection_surjective x
    exact (Q.projection_eq_zero_iff s).mpr (LinearMap.mem_ker.mpr hx)
  · intro x
    obtain ⟨s, hs⟩ := hf x
    exact ⟨Q.projection s, hs⟩

@[simp]
theorem ofIntertwinerKernelEquiv_projection (hf : Function.Surjective f) (s : S.Space) :
    ofIntertwinerKernelEquiv f hf ((ofIntertwinerKernel f).projection s) = f s :=
  rfl

end OperatorSubquotient

namespace IrreducibleOperatorSubquotient

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {r : ℕ}
  {ρ : Representation ℂ (automorphicOperatorAlgebra F (r + 1)) V}
  {S : OperatorRealization F (r + 1)}

/-- A surjection onto an irreducible operator representation produces the
corresponding actual irreducible automorphic subquotient. -/
def ofSurjectiveIntertwiner (f : S.representation.IntertwiningMap ρ)
    (hf : Function.Surjective f) (hρ : ρ.IsIrreducible) :
    IrreducibleOperatorSubquotient F r where
  subquotient := OperatorSubquotient.ofIntertwinerKernel f
  irreducible := LengthTwo.isIrreducible_of_equiv
    (OperatorSubquotient.ofIntertwinerKernelEquiv f hf).symm hρ

/-- The equivalence also identifies the finite right-translation actions. -/
def ofSurjectiveIntertwinerFiniteEquiv (f : S.representation.IntertwiningMap ρ)
    (hf : Function.Surjective f) (hρ : ρ.IsIrreducible) :
    (ofSurjectiveIntertwiner f hf hρ).subquotient.finiteRepresentation.Equiv
      (ρ.comp (finiteOperator F (r + 1))) :=
  Representation.Equiv.mk
    (OperatorSubquotient.ofIntertwinerKernelEquiv f hf).toLinearEquiv
    (fun d => (OperatorSubquotient.ofIntertwinerKernelEquiv f hf).isIntertwining'
      (finiteOperator F (r + 1) d))

end IrreducibleOperatorSubquotient

end Langlands.Automorphic
