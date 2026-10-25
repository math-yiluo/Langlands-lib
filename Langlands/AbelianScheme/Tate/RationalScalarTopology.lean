import Langlands.AbelianScheme.Tate.AwayRationalScalars
import Langlands.Topology.Rationalization.Comparison

noncomputable section
open scoped TensorProduct
open Topology

namespace Langlands.Global

namespace RationalProfiniteIntegerAdeleComparison

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- The chosen normalized integral comparison, with its given topology. -/
def integralHomeomorph : ProfiniteIntegerRing ≃ₜ integralFiniteAdeles ℚ where
  toEquiv := (integralEquiv h).toEquiv
  continuous_toFun := h.choose_spec.1
  continuous_invFun := h.choose_spec.2.1

@[simp] theorem integralHomeomorph_apply (a : ProfiniteIntegerRing) :
    integralHomeomorph h a = integralEquiv h a := rfl

@[simp] theorem integralHomeomorph_symm_apply (a : integralFiniteAdeles ℚ) :
    (integralHomeomorph h).symm a = (integralEquiv h).symm a := rfl

theorem isOpenEmbedding_integralEquiv :
    IsOpenEmbedding (fun a : ProfiniteIntegerRing =>
      (integralEquiv h a : FiniteAdeles ℚ)) := by
  exact (isOpen_integralFiniteAdeles ℚ).isOpenEmbedding_subtypeVal.comp
    (integralHomeomorph h).isOpenEmbedding

local instance : TopologicalSpace (ℚ ⊗[ℤ] ProfiniteIntegerRing) :=
  Langlands.Topology.Rationalization.finalTopology ProfiniteIntegerRing

/-- The existing normalized rational comparison is a homeomorphism for the final topology. -/
def rationalHomeomorph : (ℚ ⊗[ℤ] ProfiniteIntegerRing) ≃ₜ FiniteAdeles ℚ :=
  Langlands.Topology.Rationalization.comparisonHomeomorph (rationalEquiv h)
    ((integralFiniteAdeles ℚ).subtype.comp (integralEquiv h).toRingHom)
    (isOpenEmbedding_integralEquiv h) (rationalEquiv_tmul h)

@[simp] theorem rationalHomeomorph_apply (a : ℚ ⊗[ℤ] ProfiniteIntegerRing) :
    rationalHomeomorph h a = rationalEquiv h a := rfl

@[simp] theorem rationalHomeomorph_symm_apply (a : FiniteAdeles ℚ) :
    (rationalHomeomorph h).symm a = (rationalEquiv h).symm a := rfl

theorem continuous_rationalEquiv : Continuous (rationalEquiv h) :=
  (rationalHomeomorph h).continuous

theorem continuous_rationalEquiv_symm : Continuous (rationalEquiv h).symm :=
  (rationalHomeomorph h).symm.continuous

end RationalProfiniteIntegerAdeleComparison

namespace PrimeToRationalProfiniteIntegerAdeleComparison

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- The chosen away integral comparison, with the existing coupled witness. -/
def integralHomeomorph : PrimeToProfiniteIntegerRing m ≃ₜ primeToIntegralFiniteAdeles m where
  toEquiv := (integralEquiv hAway).toEquiv
  continuous_toFun := hAway.choose_spec.1
  continuous_invFun := hAway.choose_spec.2.1

@[simp] theorem integralHomeomorph_apply (a : PrimeToProfiniteIntegerRing m) :
    integralHomeomorph hAway a = integralEquiv hAway a := rfl

@[simp] theorem integralHomeomorph_symm_apply (a : primeToIntegralFiniteAdeles m) :
    (integralHomeomorph hAway).symm a = (integralEquiv hAway).symm a := rfl

theorem isOpenEmbedding_integralEquiv :
    IsOpenEmbedding (fun a : PrimeToProfiniteIntegerRing m =>
      (integralEquiv hAway a : PrimeToFiniteAdeles m)) := by
  exact (isOpen_primeToIntegralFiniteAdeles m).isOpenEmbedding_subtypeVal.comp
    (integralHomeomorph hAway).isOpenEmbedding

local instance : TopologicalSpace (ℚ ⊗[ℤ] ProfiniteIntegerRing) :=
  Langlands.Topology.Rationalization.finalTopology ProfiniteIntegerRing

local instance : TopologicalSpace (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) :=
  Langlands.Topology.Rationalization.finalTopology (PrimeToProfiniteIntegerRing m)

/-- The existing away rational comparison is a homeomorphism for every modulus. -/
def rationalHomeomorph : (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) ≃ₜ PrimeToFiniteAdeles m :=
  Langlands.Topology.Rationalization.comparisonHomeomorph (rationalEquiv hAway)
    ((primeToIntegralFiniteAdeles m).subtype.comp (integralEquiv hAway).toRingHom)
    (isOpenEmbedding_integralEquiv hAway) (rationalEquiv_tmul hAway)

@[simp] theorem rationalHomeomorph_apply (a : ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) :
    rationalHomeomorph hAway a = rationalEquiv hAway a := rfl

@[simp] theorem rationalHomeomorph_symm_apply (a : PrimeToFiniteAdeles m) :
    (rationalHomeomorph hAway).symm a = (rationalEquiv hAway).symm a := rfl

theorem continuous_rationalEquiv : Continuous (rationalEquiv hAway) :=
  (rationalHomeomorph hAway).continuous

theorem continuous_rationalEquiv_symm : Continuous (rationalEquiv hAway).symm :=
  (rationalHomeomorph hAway).symm.continuous

/-- The topological comparisons use exactly the existing compatible scalar witnesses. -/
theorem rationalHomeomorph_restrict (a : ℚ ⊗[ℤ] ProfiniteIntegerRing) :
    rationalHomeomorph hAway (GroupScheme.Tate.rationalScalarRestrictAway m a) =
      primeToFiniteRestriction m
        (RationalProfiniteIntegerAdeleComparison.rationalHomeomorph h a) :=
  rationalEquiv_restrict hAway a

theorem rationalHomeomorph_symm_restrict (a : FiniteAdeles ℚ) :
    (rationalHomeomorph hAway).symm (primeToFiniteRestriction m a) =
      GroupScheme.Tate.rationalScalarRestrictAway m
        ((RationalProfiniteIntegerAdeleComparison.rationalHomeomorph h).symm a) :=
  rationalEquiv_symm_restrict hAway a

end PrimeToRationalProfiniteIntegerAdeleComparison

end Langlands.Global
