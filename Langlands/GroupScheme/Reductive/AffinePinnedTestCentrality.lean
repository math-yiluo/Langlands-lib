import Langlands.GroupScheme.Reductive.AffinePinnedTorusPinning
import Langlands.GroupScheme.Reductive.AffinePinnedInnerTorus

/-! # Pinning rigidity on actual coefficient tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra M.ring A]

local instance : Smooth M.group.X.hom := M.reductive.smooth
local instance : IsAffineHom (M.groupOver (algebraBaseMap M.ring A)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (algebraBaseMap M.ring A)))

/-- The actual chosen vector in the scalar-extended model projects to the
coefficient extension of the original chosen vector. -/
theorem kernelBaseChangeLinearEquiv_pinning_one (s : M.basis.support) :
    Lie.kernelBaseChangeLinearEquiv M.ring A M.group A
        ((M.scalarExtension A).pinning s 1).val =
      lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val := by
  rw [scalarExtension_pinning_one, Lie.smoothSchemeScalarExtension_tmul,
    one_smul, LinearEquiv.apply_symm_apply]

/-- Scalar rigidity of the original chosen simple vectors after arbitrary
coefficient extension, including nonreduced coefficients. -/
theorem simpleVectorAt_smul_eq [Nontrivial A]
    {s t : M.basis.support} {a : A}
    (h : a • lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val =
      lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning t 1).val) :
    s = t ∧ a = 1 := by
  let : Nontrivial (M.scalarExtension A).ring := inferInstanceAs (Nontrivial A)
  have hv : a • (show Additive (lieKernel
        (M.groupOver (algebraBaseMap M.ring A)) A) from
          ((M.scalarExtension A).pinning s 1).val) =
      ((M.scalarExtension A).pinning t 1).val := by
    apply (Lie.kernelBaseChangeLinearEquiv M.ring A M.group A).injective
    rw [LinearEquiv.map_smul, kernelBaseChangeLinearEquiv_pinning_one,
      kernelBaseChangeLinearEquiv_pinning_one]
    exact h
  exact (M.scalarExtension A).simpleVector_smul_eq hv

/-- The torus point permutes the original simple vectors after actual
coefficient extension to this test algebra. -/
def TorusPermutesSimpleVectorsAt
    (t : Lie.AffinePoints (splitTorus M.base M.coordinates) A) : Prop :=
  ∃ σ : M.basis.support ≃ M.basis.support, ∀ s,
    adjoint M.group A (t ≫ M.inclusion.hom.hom)
      (lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val) =
        lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning (σ s) 1).val

/-- The simple-root unit monomials equal one on such a coefficient test. -/
theorem simpleExponentValue_eq_one_of_torusPermutesSimpleVectorsAt
    [Nontrivial A]
    {t : Lie.AffinePoints (splitTorus M.base M.coordinates) A}
    (ht : M.TorusPermutesSimpleVectorsAt A t) (s : M.basis.support) :
    (splitTorus.exponentValue M.coordinates
      (splitTorus.algebraPointsEquiv M.coordinates A t)
      (Multiplicative.ofAdd (M.rootDatum.root s)) : A) = 1 := by
  classical
  obtain ⟨σ, hσ⟩ := ht
  have hw := (M.pinning s 1).property A
    (splitTorus.algebraPointsEquiv M.coordinates A t)
  rw [MulEquiv.symm_apply_apply] at hw
  exact (M.simpleVectorAt_smul_eq A (hw.symm.trans (hσ s))).2

/-- Coefficient-test permutation forces every simple-root character equation. -/
theorem simpleRootCharactersOne_of_torusPermutesSimpleVectorsAt
    [Nontrivial A]
    {t : Lie.AffinePoints (splitTorus M.base M.coordinates) A}
    (ht : M.TorusPermutesSimpleVectorsAt A t) :
    SimpleRootCharactersOne (R := M.ring) (P := M.rootDatum) M.basis
      (Z := Corepresented.RingCoordinates.specOver (CommRingCat.of M.ring) A) t := by
  classical
  intro α hα
  let z : M.coordinates → Aˣ := splitTorus.algebraPointsEquiv M.coordinates A t
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  rw [map_one]
  have hc := Corepresented.charValue_torusPt (R := CommRingCat.of M.ring)
    (I := M.coordinates) (M.rootDatum.root α) z
  have hz : Corepresented.torusPt (R := CommRingCat.of M.ring) M.coordinates
      (CommAlgCat.of (CommRingCat.of M.ring) A) z = t :=
    (splitTorus.algebraPointsEquiv (R := CommRingCat.of M.ring)
      M.coordinates A).symm_apply_apply t
  rw [hz] at hc
  exact hc.trans
    (M.simpleExponentValue_eq_one_of_torusPermutesSimpleVectorsAt A ht ⟨α, hα⟩)

/-- Coefficient-test permutation gives full centre membership on the test. -/
theorem mem_center_of_torusPermutesSimpleVectorsAt [Nontrivial A]
    {t : Lie.AffinePoints (splitTorus M.base M.coordinates) A}
    (ht : M.TorusPermutesSimpleVectorsAt A t) :
    t ≫ M.inclusion.hom.hom ∈ (center M.group).carrier
      ((algSpec (CommRingCat.of M.ring)).obj
        (op (CommAlgCat.of (CommRingCat.of M.ring) A))) :=
  mem_center_of_simpleRootCharacters_one (R := M.ring)
    M.reductive M.maximal M.fibrewiseRootDatum M.basis t
      (M.simpleRootCharactersOne_of_torusPermutesSimpleVectorsAt A ht)

end Langlands.GroupScheme.AffinePinnedModel
