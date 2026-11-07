import Langlands.GroupScheme.GeometricComponentRationalBaseChange

/-! # Base-field extension on Galois-fixed geometric components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientBaseChangeEquiv_target
    (k K M : Type u) [Field k] [Field K] [Field M]
    [Algebra k K] [Algebra k M] [Algebra K M] [IsScalarTower k K M]
    {H H' : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ H')
    (x : (baseChanged k K H).affinePoints (CommAlgCat.of K M)) :
    coefficientBaseChangeEquiv k K M H'
        ((baseChanged k K H).affinePointsTarget
          ((GroupScheme.baseChange (baseMap k K)).map f) (CommAlgCat.of K M) x) =
      H.affinePointsTarget f (CommAlgCat.of k M)
        (coefficientBaseChangeEquiv k K M H x) := by
  apply Over.OverMorphism.ext
  simpa only [coefficientBaseChangeEquiv_left, affinePointsTarget_apply,
    baseChangePointsEquiv_left, Over.comp_left] using
    congrArg (fun y => y.left)
      (baseChangePointsEquiv_comp (baseMap k K) f
        (Langlands.AlgebraicGeometry.PointTopology.ringTest K M) x)

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
  [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The geometric comparison is equivariant for the actual continuous
restriction of absolute Galois groups through the specified closures. -/
theorem geometricComponentBaseChangeEquiv_restrict_smul
    (τ : Field.absoluteGaloisGroup K) (c : GeometricComponents k H) :
    geometricComponentBaseChangeEquiv k K H
        ((Field.absoluteGaloisGroup.mapOfAlgebra k K τ) • c) =
      τ • geometricComponentBaseChangeEquiv k K H c := by
  apply geometricComponentBaseChangeEquiv_smul k K H _ τ _ c
  intro a
  exact ((τ.restrictScalars k).restrictNormal_commutes (AlgebraicClosure k) a).symm

/-- Extend every base-Galois-fixed geometric component along the specified
closure embedding to a component fixed by the extension's absolute Galois group. -/
def geometricComponentFixedBaseChange :
    geometricComponentFixedSubgroup k H →*
      geometricComponentFixedSubgroup K (baseChanged k K H) where
  toFun c := ⟨geometricComponentBaseChangeEquiv k K H c.val, by
    change ∀ τ : Field.absoluteGaloisGroup K,
      τ • geometricComponentBaseChangeEquiv k K H c.val =
        geometricComponentBaseChangeEquiv k K H c.val
    intro τ
    calc
      τ • geometricComponentBaseChangeEquiv k K H c.val =
          geometricComponentBaseChangeEquiv k K H
            ((Field.absoluteGaloisGroup.mapOfAlgebra k K τ) • c.val) :=
        (geometricComponentBaseChangeEquiv_restrict_smul k K H τ c.val).symm
      _ = geometricComponentBaseChangeEquiv k K H c.val :=
        congrArg (geometricComponentBaseChangeEquiv k K H)
          (c.property (Field.absoluteGaloisGroup.mapOfAlgebra k K τ))⟩
  map_one' := Subtype.ext (map_one (geometricComponentBaseChangeEquiv k K H))
  map_mul' c d := Subtype.ext (map_mul (geometricComponentBaseChangeEquiv k K H) c.val d.val)

@[simp]
theorem geometricComponentFixedBaseChange_val
    (c : geometricComponentFixedSubgroup k H) :
    (geometricComponentFixedBaseChange k K H c).val =
      geometricComponentBaseChangeEquiv k K H c.val := rfl

/-- Extension of the base field loses no Galois-fixed geometric component. -/
theorem geometricComponentFixedBaseChange_injective :
    Function.Injective (geometricComponentFixedBaseChange k K H) := by
  intro c d h
  apply Subtype.ext
  apply (geometricComponentBaseChangeEquiv k K H).injective
  exact congrArg Subtype.val h

/-- On rationally represented components the new full-fixed map is the
previous rational-class construction. -/
theorem geometricComponentFixedBaseChange_rational
    (c : RationalComponentQuotient H) :
    geometricComponentFixedBaseChange k K H (rationalGeometricComponentToFixed k H c) =
      rationalGeometricComponentBaseChangeToFixed k K H c := by
  apply Subtype.ext
  exact geometricComponentBaseChangeEquiv_rational k K H c

variable {H} {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- The actual section comparison commutes with every base-field group-scheme
homomorphism and its iterated pullback. -/
theorem geometricComponentBaseChangeSectionHom_naturality (f : H ⟶ H')
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    geometricComponentBaseChangeSectionHom k K H'
        (rationalPoints.map
          ((GroupScheme.baseChange (baseMap k (AlgebraicClosure k))).map f) x) =
      rationalPoints.map
        ((GroupScheme.baseChange (baseMap K (AlgebraicClosure K))).map
          ((GroupScheme.baseChange (baseMap k K)).map f))
        (geometricComponentBaseChangeSectionHom k K H x) := by
  apply (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H')).injective
  apply (coefficientBaseChangeEquiv k K (AlgebraicClosure K) H').injective
  rw [geometricComponentBaseChangeSectionHom_coefficient,
    baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_map,
    coefficientBaseChangeEquiv_target, geometricComponentBaseChangeSectionHom_coefficient]
  exact congrArg (fun m => m (baseChangeCoeffEquiv k (AlgebraicClosure k) H x))
    (H.affinePointsTarget_naturality f
      (CommAlgCat.ofHom
        (IsScalarTower.toAlgHom k (AlgebraicClosure k) (AlgebraicClosure K))))

/-- The geometric base-field equivalence is natural in actual homomorphisms. -/
theorem geometricComponentBaseChangeEquiv_naturality (f : H ⟶ H')
    (c : GeometricComponents k H) :
    geometricComponentBaseChangeEquiv k K H' (geometricComponentMap k f c) =
      geometricComponentMap K ((GroupScheme.baseChange (baseMap k K)).map f)
        (geometricComponentBaseChangeEquiv k K H c) := by
  obtain ⟨x, rfl⟩ := geometricComponentOfPoint_surjective k H c
  rw [geometricComponentMap_ofPoint, geometricComponentBaseChangeEquiv_ofPoint,
    geometricComponentBaseChangeEquiv_ofPoint, geometricComponentMap_ofPoint,
    geometricComponentBaseChangeSectionHom_naturality]

/-- Extension of the full fixed subgroup commutes with actual homomorphisms. -/
theorem geometricComponentFixedBaseChange_naturality (f : H ⟶ H')
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentFixedBaseChange k K H' (geometricComponentFixedMap k f c) =
      geometricComponentFixedMap K ((GroupScheme.baseChange (baseMap k K)).map f)
        (geometricComponentFixedBaseChange k K H c) := by
  apply Subtype.ext
  exact geometricComponentBaseChangeEquiv_naturality k K f c.val

end Langlands.GroupScheme.IdentityComponent
