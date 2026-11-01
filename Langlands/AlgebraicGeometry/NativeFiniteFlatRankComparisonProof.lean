import Langlands.AlgebraicGeometry.NativeFiniteFlatRankComparisonStatement

/-! # Calculating native rank from affine sections and their fraction fields -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
theorem nativeFiniteFlatRankComparison :
    NativeFiniteFlatRankComparisonStatement.{u} := by
  constructor
  · intro X Y f _ _ _ _
    let : IsAffine X := isAffine_of_isAffineHom f
    let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    let : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
    let : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := f.flat_appTop
    let : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff f.appTop).mpr f.finite_appTop
    let : Flat (Spec.map f.appTop) := Flat.SpecMap_iff.mpr f.flat_appTop
    intro y
    have hpb : IsPullback X.isoSpec.hom f (Spec.map f.appTop) Y.isoSpec.hom :=
      IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality f⟩
    rw [Scheme.Hom.finrank_of_isPullback X.isoSpec.hom f (Spec.map f.appTop)
      Y.isoSpec.hom hpb y]
    rw [Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]
    change Module.rankAtStalk Γ(X, ⊤) _ = _
    rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]
  · intro R S _ _ _ _ _ _ _ _
    let : Algebra (FractionRing R) (FractionRing S) :=
      FractionRing.liftAlgebra R (FractionRing S)
    let : IsScalarTower R (FractionRing R) (FractionRing S) :=
      FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
    intro p
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq,
      Ideal.finrank_fiber_eq_finrank]
    exact (IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)).symm

end Langlands.AlgebraicGeometry
