import Langlands.GroupScheme.MatrixRepresentation.FrobeniusSocleDetection

/-! # Cyclic detection by the actual top Frobenius distribution -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusCyclicDetection

section Algebra

variable {K A V : Type*} [Field K] [Ring A] [Algebra K A]
    [AddCommGroup V] [Module K V] (R : A →ₐ[K] Module.End K V) (v : V)

/-- Evaluation of a supplied algebra representation at its original vector. -/
def cyclicMap : A →ₗ[K] V where
  toFun a := R a v
  map_add' a b := by simp
  map_smul' c a := by simp

/-- The annihilator of a vector is a left ideal in the original algebra. -/
def cyclicKernel : Ideal A where
  carrier := {a | R a v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change R a v = 0 at ha
    change R b v = 0 at hb
    change R (a + b) v = 0
    rw [map_add, LinearMap.add_apply, ha, hb, zero_add]
  smul_mem' := by
    intro a b hb
    change R (a * b) v = 0
    rw [map_mul, Module.End.mul_apply, hb, map_zero]

/-- A nonzero action of an element meeting every nonzero left ideal makes
the original cyclic action map injective. -/
theorem cyclicMap_injective_of_leftIdeal_detection (s : A)
    (hs : R s v ≠ 0)
    (hdetect : ∀ J : Ideal A, J ≠ ⊥ → s ∈ J) :
    Function.Injective (cyclicMap R v) := by
  have hker : cyclicKernel R v = ⊥ := by
    by_contra h
    exact hs (hdetect _ h)
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro a ha
  have hmem : a ∈ cyclicKernel R v := ha
  change a = 0
  simpa only [hker, Ideal.mem_bot] using hmem

end Algebra

open FrobeniusCoordinateModel FrobeniusDistributionAlgebra FrobeniusConvolutionAction
open FrobeniusOrderedDistributions FrobeniusOriginUniversality FrobeniusSocleDetection
open FrobeniusPolynomialBox TorusUnipotence CoordinateWeights FrobeniusTopIntegral

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)
    {S : CommGroupScheme (Spec (.of k))}
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (ν : cocharacterLattice S)
    {d : ℕ} (w : Fin d → characterLattice S) (t : Fin d → CharacterUnits.Coord G)
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G))
    (htw : ∀ i, t i ∈ CoordinateWeights.weightSpace b (w i))
    (hε : ∀ i, coordCounit G (t i) = 0)
    (hw : ∀ i, 0 < latticePairing S (w i) ν)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (v : n → k)

include hS htw hw in
/-- A nonzero top action detects every distribution through its action on
the original vector, rather than through an operator image quotient. -/
theorem distributionOrbitMap_injective_of_topAction_ne_zero
    (hv : distributionAction p r ρ (topDistribution p r t ht hε).ofConv v ≠ 0) :
    Function.Injective (distributionOrbitMap p r ρ v) := by
  have hinj := cyclicMap_injective_of_leftIdeal_detection (actionAlgHom p r ρ) v
    (topDistribution p r t ht hε) hv
    (topDistribution_mem_of_ne_bot p r hS b ν w t ht htw hε hw)
  intro f g hfg
  have he : (WithConv.toConv f : DistributionAlgebra (G := G) p r) =
      WithConv.toConv g := hinj hfg
  exact congrArg WithConv.ofConv he

include hS htw hw in
/-- The entire intrinsic Frobenius-origin orbit span has the full quotient
dimension when the top distribution acts nontrivially. -/
theorem finrank_originOrbitSpan_of_topAction_ne_zero
    (hv : distributionAction p r ρ (topDistribution p r t ht hε).ofConv v ≠ 0) :
    Module.finrank k (originOrbitSpan p r ρ v) = (p ^ r) ^ d := by
  let := finite_quotientAlgebra G p r (polynomialCoordinates t ht)
    (polynomialCoordinates_origin t ht hε)
  rw [originOrbitSpan_eq_range, LinearMap.finrank_range_of_inj
    (distributionOrbitMap_injective_of_topAction_ne_zero p r hS b ν w t ht htw hε hw ρ v hv),
    Subspace.dual_finrank_eq]
  exact finrank_quotientAlgebra G p r (polynomialCoordinates t ht)
    (polynomialCoordinates_origin t ht hε)

include hS htw hw in
/-- An independent upper bound for the whole original representation turns the
top-action dimension equality into spanning by all intrinsic origin tests. -/
theorem originOrbitSpan_eq_top_of_topAction_ne_zero_of_finrank_le
    (hv : distributionAction p r ρ (topDistribution p r t ht hε).ofConv v ≠ 0)
    (hdim : Module.finrank k (n → k) ≤ (p ^ r) ^ d) :
    originOrbitSpan p r ρ v = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  rw [finrank_originOrbitSpan_of_topAction_ne_zero p r hS b ν w t ht htw hε hw ρ v hv]
  exact hdim

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusCyclicDetection
