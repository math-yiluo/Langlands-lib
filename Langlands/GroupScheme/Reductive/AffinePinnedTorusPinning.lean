import Langlands.GroupScheme.Reductive.AffinePinnedScalarExtension
import Langlands.GroupScheme.Reductive.GlobalRootAnnihilatorCentrality
import Langlands.GroupScheme.Reductive.AffinePinnedPinningInverse
import Langlands.GroupScheme.Lie.ElementCentralizer

/-! # Torus conjugation and supplied simple pinning vectors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u})

local instance : Smooth M.group.X.hom := M.reductive.smooth

/-- Conjugation by this actual torus point permutes the supplied simple vectors. -/
def TorusPermutesSimpleVectors
    (t : Lie.AffinePoints (splitTorus M.base M.coordinates) M.ring) : Prop :=
  ∃ σ : M.basis.support ≃ M.basis.support, ∀ s,
    adjoint M.group M.ring (t ≫ M.inclusion.hom.hom) (M.pinning s 1).val =
      (M.pinning (σ s) 1).val

/-- A scalar multiple of one chosen simple vector can equal another only
at the same root, with scalar one. -/
theorem simpleVector_smul_eq [Nontrivial M.ring]
    {s t : M.basis.support} {a : M.ring}
    (h : a • (M.pinning s 1).val = (M.pinning t 1).val) :
    s = t ∧ a = 1 := by
  classical
  have hst : s = t := by
    by_contra hn
    have hr : M.rootDatum.root s ≠ M.rootDatum.root t := by
      intro hr
      exact hn (Subtype.ext (M.rootDatum.root.injective hr))
    have hc := congrArg (fun X =>
      splitTorus.universalAdjointCoefficients M.coordinates M.group M.inclusion X
        (M.rootDatum.root t)) h
    rw [map_smul, Finsupp.smul_apply,
      splitTorus.universalAdjointCoefficients_of_mem_exponentWeightSpace
        M.coordinates M.group M.inclusion _ _ (M.pinning s 1).property,
      splitTorus.universalAdjointCoefficients_of_mem_exponentWeightSpace
        M.coordinates M.group M.inclusion _ _ (M.pinning t 1).property,
      Finsupp.single_eq_of_ne (Ne.symm hr), Finsupp.single_eq_same, smul_zero] at hc
    have hz : M.pinning t 1 = 0 := Subtype.ext hc.symm
    have h10 : (1 : M.ring) = 0 := (M.pinning t).injective (hz.trans (map_zero _).symm)
    exact one_ne_zero h10
  subst t
  refine ⟨rfl, ?_⟩
  have hv := congrArg
    (fun v : splitTorus.exponentWeightSpace M.coordinates M.group M.inclusion
      (M.rootDatum.root s) => v.val)
    ((M.pinning s).map_smul (a : CommRingCat.of M.ring) (1 : CommRingCat.of M.ring))
  simp only [smul_eq_mul, mul_one, Submodule.coe_smul] at hv
  have he : M.pinning s a = M.pinning s 1 := Subtype.ext (hv.trans h)
  exact (M.pinning s).injective he

private theorem kernelMapLinear_self (X : Additive (lieKernel M.group M.ring)) :
    lieKernelMapLinear M.group (Algebra.ofId M.ring M.ring) X = X := by
  apply Additive.toMul.injective
  rw [lieKernelMapLinear_toMul]
  have h : Algebra.ofId M.ring M.ring = AlgHom.id M.ring M.ring := by ext
  rw [h, lieKernelMap_id]

/-- The simple-root unit monomials of such a point equal one. -/
theorem simpleExponentValue_eq_one_of_torusPermutesSimpleVectors
    [Nontrivial M.ring]
    {t : Lie.AffinePoints (splitTorus M.base M.coordinates) M.ring}
    (ht : M.TorusPermutesSimpleVectors t) (s : M.basis.support) :
    (splitTorus.exponentValue M.coordinates
      (splitTorus.algebraPointsEquiv M.coordinates M.ring t)
      (Multiplicative.ofAdd (M.rootDatum.root s)) : M.ring) = 1 := by
  classical
  obtain ⟨σ, hσ⟩ := ht
  have hw := (M.pinning s 1).property M.ring
    (splitTorus.algebraPointsEquiv M.coordinates M.ring t)
  rw [MulEquiv.symm_apply_apply, M.kernelMapLinear_self] at hw
  exact (M.simpleVector_smul_eq (hw.symm.trans (hσ s))).2

/-- A torus point permuting simple pinning vectors has every simple-root
character equal to one, without reducing the coefficient ring. -/
theorem simpleRootCharactersOne_of_torusPermutesSimpleVectors
    [Nontrivial M.ring]
    {t : Lie.AffinePoints (splitTorus M.base M.coordinates) M.ring}
    (ht : M.TorusPermutesSimpleVectors t) :
    SimpleRootCharactersOne (R := M.ring) (P := M.rootDatum) M.basis
      (Z := Corepresented.RingCoordinates.specOver (CommRingCat.of M.ring) M.ring) t := by
  classical
  intro α hα
  let z : M.coordinates → M.ringˣ :=
    splitTorus.algebraPointsEquiv M.coordinates M.ring t
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of M.ring)).hom).1
  rw [map_one]
  have hc := Corepresented.charValue_torusPt (R := CommRingCat.of M.ring)
    (I := M.coordinates) (M.rootDatum.root α) z
  have hz : Corepresented.torusPt (R := CommRingCat.of M.ring) M.coordinates
      (CommAlgCat.of (CommRingCat.of M.ring) M.ring) z = t :=
    (splitTorus.algebraPointsEquiv (R := CommRingCat.of M.ring)
      M.coordinates M.ring).symm_apply_apply t
  rw [hz] at hc
  exact hc.trans (M.simpleExponentValue_eq_one_of_torusPermutesSimpleVectors ht ⟨α, hα⟩)

/-- Permuting the supplied simple vectors forces the actual torus point to
belong to the full centre on every relative refinement. -/
theorem mem_center_of_torusPermutesSimpleVectors [Nontrivial M.ring]
    {t : Lie.AffinePoints (splitTorus M.base M.coordinates) M.ring}
    (ht : M.TorusPermutesSimpleVectors t) :
    t ≫ M.inclusion.hom.hom ∈ (center M.group).carrier
      ((algSpec (CommRingCat.of M.ring)).obj
        (op (CommAlgCat.of (CommRingCat.of M.ring) M.ring))) :=
  mem_center_of_simpleRootCharacters_one (R := M.ring)
    M.reductive M.maximal M.fibrewiseRootDatum M.basis t
      (M.simpleRootCharactersOne_of_torusPermutesSimpleVectors ht)

end Langlands.GroupScheme.AffinePinnedModel
