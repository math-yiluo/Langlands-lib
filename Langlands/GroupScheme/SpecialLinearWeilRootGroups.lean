import Langlands.GroupScheme.SpecialLinearRootGroups
import Langlands.GroupScheme.Rational.AffineWeilPoints

/-! # Actual coordinate-root maps of Weil-restricted split special linear groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SpecialLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})

instance locallyOfFiniteType_groupScheme :
    LocallyOfFiniteType (groupScheme n R).X.hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing n R))))
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end Langlands.GroupScheme.SpecialLinear


namespace Langlands.GroupScheme.SpecialLinear.WeilRoot

variable {n : Type} [Fintype n] [DecidableEq n]
  (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

local instance specialLinear_affine :
    IsAffine (SpecialLinear.groupScheme n (CommRingCat.of E)).X.left :=
  SpecialLinear.isAffine_groupScheme n _

local instance specialLinear_finiteType :
    LocallyOfFiniteType (SpecialLinear.groupScheme n (CommRingCat.of E)).X.hom :=
  SpecialLinear.locallyOfFiniteType_groupScheme n _

local instance vectorGroup_affine :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of E) 1).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin 1) E)))
  infer_instance

local instance vectorGroup_finiteType :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of E) 1).X.hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin 1) E))))
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The actual affine Weil restriction of the split special-linear group over E. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of F)) :=
  AffineWeil.groupScheme F E (SpecialLinear.groupScheme n (CommRingCat.of E))

/-- The actual restricted additive group parametrizing one coordinate root. -/
abbrev additiveScheme : GroupScheme (Spec (CommRingCat.of F)) :=
  AffineWeil.groupScheme F E (VectorGroup.groupScheme (CommRingCat.of E) 1)

/-- Restriction of the actual additive coordinate-root homomorphism. -/
def rootMap {i j : n} (hij : i ≠ j) :
    additiveScheme F E ⟶ groupScheme (n := n) F E :=
  AffineWeil.map F E (Root.rootMap (CommRingCat.of E) hij)

/-- The actual rational points of the restricted scheme are determinant-one E-matrices. -/
def rationalMatrixEquiv :
    rationalPoints (groupScheme (n := n) F E) ≃* Matrix.SpecialLinearGroup n E :=
  (AffineWeil.rationalPointsEquiv F E
    (SpecialLinear.groupScheme n (CommRingCat.of E))).trans
      (Root.rationalMatrixEquiv (n := n) E)

/-- The restricted actual root map has its original E-rational matrix formula. -/
theorem rationalMatrixEquiv_rootMap {i j : n} (hij : i ≠ j)
    (x : rationalPoints (additiveScheme F E)) :
    rationalMatrixEquiv F E (rationalPoints.map (rootMap F E hij) x) =
      Root.rationalMatrixEquiv (n := n) E
        (rationalPoints.map (Root.rootMap (CommRingCat.of E) hij)
          (AffineWeil.rationalPointsEquiv F E
            (VectorGroup.groupScheme (CommRingCat.of E) 1) x)) := by
  simp only [rationalMatrixEquiv, MulEquiv.trans_apply, rootMap]
  exact congrArg (Root.rationalMatrixEquiv (n := n) E)
    (AffineWeil.rationalPointsEquiv_map F E (Root.rootMap (CommRingCat.of E) hij) x)

/-- Every scalar E-transvection comes from an actual F-rational restricted root point. -/
theorem exists_rational_rootPoint {i j : n} (hij : i ≠ j) (a : E) :
    ∃ x : rationalPoints (additiveScheme F E),
      rationalMatrixEquiv F E (rationalPoints.map (rootMap F E hij) x) =
        Matrix.SpecialLinearGroup.transvection hij a := by
  obtain ⟨y, hy⟩ := Root.exists_rational_rootPoint E hij a
  refine ⟨(AffineWeil.rationalPointsEquiv F E
    (VectorGroup.groupScheme (CommRingCat.of E) 1)).symm y, ?_⟩
  rw [rationalMatrixEquiv_rootMap, MulEquiv.apply_symm_apply]
  exact hy

/-- Actual restricted coordinate-root images generate every F-point of Res(E/F) SL_n. -/
theorem eq_top_of_root_images
    (N : Subgroup (rationalPoints (groupScheme (n := n) F E)))
    (hroot : ∀ (i j : n) (hij : i ≠ j),
      (rationalPoints.map (rootMap F E hij)).range ≤ N) : N = ⊤ := by
  have htop : N.comap (rationalMatrixEquiv (n := n) F E).symm.toMonoidHom = ⊤ := by
    apply Root.eq_top_of_transvections
    intro i j hij a
    obtain ⟨y, hy⟩ := exists_rational_rootPoint F E hij a
    change (rationalMatrixEquiv (n := n) F E).symm _ ∈ N
    rw [← hy, MulEquiv.symm_apply_apply]
    exact hroot i j hij ⟨y, rfl⟩
  apply top_unique
  intro x _
  have hx : rationalMatrixEquiv (n := n) F E x ∈
      N.comap (rationalMatrixEquiv (n := n) F E).symm.toMonoidHom := by
    rw [htop]
    trivial
  change (rationalMatrixEquiv (n := n) F E).symm
    (rationalMatrixEquiv (n := n) F E x) ∈ N at hx
  simpa only [MulEquiv.symm_apply_apply] using hx

end Langlands.GroupScheme.SpecialLinear.WeilRoot
