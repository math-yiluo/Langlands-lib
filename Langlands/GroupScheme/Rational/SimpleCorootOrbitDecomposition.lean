import Langlands.GroupScheme.Rational.SimpleCorootGaloisTransport
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality

/-! # Equivariant coordinates of rational torus points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCompatiblePinningData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

open Langlands.GroupScheme.GaloisPointComparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (D : GaloisCompatiblePinningData k K G)

/-- The inverse coordinate map multiplies the actual transported simple-coroot points. -/
theorem torusCoordinates_symm_apply (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (c : D.pinning.base.support → Kˣ) :
    (D.torusCoordinates hspan).symm c = ∏ a, D.torusCorootPoint a (c a) := by
  classical
  change D.torusPointEquiv (D.pinning.simpleCorootProduct c) = _
  simp only [SplitPinning.simpleCorootProduct, map_prod, torusCorootPoint]

/-- The simple-coroot coordinates reconstruct every point of the base changed torus. -/
theorem prod_torusCorootPoint_coordinates (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (x : rationalPoints (baseChanged k K D.torus.toGrp)) :
    (∏ a, D.torusCorootPoint a (D.torusCoordinates hspan x a)) = x := by
  rw [← D.torusCoordinates_symm_apply hspan,
    MulEquiv.symm_apply_apply]

private theorem torusCoordinates_symm_rationalConjugate
    (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (σ : K ≃ₐ[k] K) (c : D.pinning.base.support → Kˣ) :
    rationalConjugate k K D.torus.toGrp σ ((D.torusCoordinates hspan).symm c) =
      (D.torusCoordinates hspan).symm
        (fun b => Units.map σ.toMonoidHom (c ((D.action σ).symm b))) := by
  classical
  rw [D.torusCoordinates_symm_apply hspan,
    D.torusCoordinates_symm_apply hspan, map_prod]
  simp only [D.torusCorootPoint_rationalConjugate]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp (D.action σ)
      (fun b => D.torusCorootPoint b
        (Units.map σ.toMonoidHom (c ((D.action σ).symm b)))))

/-- Coordinates transform by the simple-root permutation and ordinary coefficient conjugation. -/
theorem torusCoordinates_rationalConjugate
    (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (σ : K ≃ₐ[k] K) (x : rationalPoints (baseChanged k K D.torus.toGrp))
    (a : D.pinning.base.support) :
    D.torusCoordinates hspan (rationalConjugate k K D.torus.toGrp σ x)
        (D.action σ a) =
      Units.map σ.toMonoidHom (D.torusCoordinates hspan x a) := by
  have h := D.torusCoordinates_symm_rationalConjugate hspan σ
    (D.torusCoordinates hspan x)
  rw [MulEquiv.symm_apply_apply] at h
  have hc := congrArg (fun y => D.torusCoordinates hspan y (D.action σ a)) h
  simpa only [MulEquiv.apply_symm_apply, Equiv.symm_apply_apply] using hc

/-- Simple-coroot unit coordinates of a point of the descended torus over the base field. -/
def rationalTorusCoordinates (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤) :
    rationalPoints D.torus.toGrp →* (D.pinning.base.support → Kˣ) :=
  (D.torusCoordinates hspan).toMonoidHom.comp (rationalExtend k K D.torus.toGrp)

/-- Base-field torus points have equivariant simple-coroot unit coordinates. -/
theorem torusCoordinates_rationalExtend_equivariant
    (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (t : rationalPoints D.torus.toGrp)
    (σ : K ≃ₐ[k] K) (a : D.pinning.base.support) :
    D.torusCoordinates hspan (rationalExtend k K D.torus.toGrp t) (D.action σ a) =
      Units.map σ.toMonoidHom
        (D.torusCoordinates hspan (rationalExtend k K D.torus.toGrp t) a) := by
  have hfixed :
      rationalConjugate k K D.torus.toGrp σ (rationalExtend k K D.torus.toGrp t) =
        rationalExtend k K D.torus.toGrp t := by
    apply (baseChangeCoeffEquiv k K D.torus.toGrp).injective
    simp only [baseChangeCoeffEquiv_rationalConjugate,
      baseChangeCoeffEquiv_rationalExtend, GaloisPoint.conjugate_extend]
  simpa only [hfixed] using D.torusCoordinates_rationalConjugate hspan σ
    (rationalExtend k K D.torus.toGrp t) a

/-- Each base-field torus point has equivariant unit coordinates and the actual coroot product. -/
theorem exists_equivariant_torusCorootProduct
    (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (t : rationalPoints D.torus.toGrp) :
    ∃ c : D.pinning.base.support → Kˣ,
      (∀ (σ : K ≃ₐ[k] K) (a : D.pinning.base.support),
        (c (D.action σ a) : K) = σ (c a)) ∧
      rationalExtend k K D.torus.toGrp t = ∏ a, D.torusCorootPoint a (c a) := by
  refine ⟨D.torusCoordinates hspan (rationalExtend k K D.torus.toGrp t), ?_, ?_⟩
  · intro σ a
    exact congrArg (fun z : Kˣ => (z : K))
      (D.torusCoordinates_rationalExtend_equivariant hspan t σ a)
  · exact (D.prod_torusCorootPoint_coordinates hspan _).symm

private theorem rationalExtend_inclusion (t : rationalPoints D.torus.toGrp) :
    rationalExtend k K G (rationalPoints.map D.inclusion t) =
      rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
        (rationalExtend k K D.torus.toGrp t) := by
  exact rationalExtend_map k K D.inclusion t

private theorem inclusion_torusPointEquiv
    (x : rationalPoints D.pinning.torus.toGrp) :
    rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
        (D.torusPointEquiv x) =
      rationalPoints.map D.pinning.inclusion x := by
  change (x ≫ (CommGroupScheme.groupHom D.torusIso.hom).hom.hom) ≫
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion).hom.hom =
    x ≫ D.pinning.inclusion.hom.hom
  rw [D.inclusion_eq]
  rfl

/-- The image of every base-field torus point is an equivariant simple-coroot product
in the actual pinned torus, followed by its actual inclusion. -/
theorem exists_equivariant_simpleCorootProduct
    (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
    (t : rationalPoints D.torus.toGrp) :
    ∃ c : D.pinning.base.support → Kˣ,
      (∀ (σ : K ≃ₐ[k] K) (a : D.pinning.base.support),
        (c (D.action σ a) : K) = σ (c a)) ∧
      rationalExtend k K G (rationalPoints.map D.inclusion t) =
        rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) := by
  obtain ⟨c, hc, ht⟩ := D.exists_equivariant_torusCorootProduct hspan t
  refine ⟨c, hc, ?_⟩
  rw [D.rationalExtend_inclusion, ht]
  have hp : (∏ a, D.torusCorootPoint a (c a)) =
      D.torusPointEquiv (D.pinning.simpleCorootProduct c) := by
    classical
    simp only [SplitPinning.simpleCorootProduct, map_prod, torusCorootPoint]
  rw [hp, D.inclusion_torusPointEquiv]

end Langlands.GroupScheme.GaloisCompatiblePinningData
