import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.IntegralModel

/-! # Morphisms of the actual torus norm subgroups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational/coefficient comparison commutes with actual group-scheme maps. -/
theorem rationalCoeffEquiv_map (f : G ⟶ H) (x : rationalPoints G) :
    rationalCoeffEquiv k H (rationalPoints.map f x) =
      G.affinePointsTarget f (CommAlgCat.of k k) (rationalCoeffEquiv k G x) := by
  rw [rationalPoints.map_apply, affinePointsTarget_apply]
  apply Over.OverMorphism.ext
  simp only [rationalCoeffEquiv_left, Over.comp_left]

variable [FiniteDimensional k L] [IsGalois k L]
  {T U : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffine T.X.left] [IsAffine U.X.left]

/-- An actual commutative-group morphism commutes with the rational point norm. -/
theorem rationalNorm_naturality (f : T ⟶ U)
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp) :
    rationalPoints.map (CommGroupScheme.groupHom f) (rationalNorm k L T x) =
      rationalNorm k L U
        (rationalPoints.map
          (CommGroupScheme.groupHom ((CommGroupScheme.baseChange (baseMap k L)).map f)) x) := by
  apply (rationalCoeffEquiv k U.toGrp).injective
  rw [rationalCoeffEquiv_map, rationalCoeffEquiv_rationalNorm,
    GaloisPoint.norm_naturality, rationalCoeffEquiv_rationalNorm]
  congr 1
  exact (baseChangeCoeffEquiv_map k L (CommGroupScheme.groupHom f) x).symm

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

open Langlands.GroupScheme
open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)
  {T U : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffine T.X.left] [IsAffine U.X.left]

/-- With a common extension and valuation, a morphism preserves the actual norm subgroups. -/
theorem map_torusNormIwahori_le (f : T ⟶ U) :
    (torusNormIwahori k L v T).map (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
      torusNormIwahori k L v U := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨x, hx, rfl⟩ := (mem_torusNormIwahori k L).mp ht
  rw [rationalNorm_naturality]
  apply (mem_torusNormIwahori k L).mpr
  refine ⟨_, ?_, rfl⟩
  exact map_characterValuationKernel_le v
    (CommGroupScheme.groupHom ((CommGroupScheme.baseChange (baseMap k L)).map f))
    ⟨x, hx, rfl⟩

/-- The actual rational-point map restricted to the two norm subgroups. -/
def torusNormIwahoriMap (f : T ⟶ U) :
    torusNormIwahori k L v T →* torusNormIwahori k L v U :=
  ((rationalPoints.map (CommGroupScheme.groupHom f)).comp
    (torusNormIwahori k L v T).subtype).codRestrict _
      (fun t => map_torusNormIwahori_le k L v f ⟨t, t.property, rfl⟩)

@[simp] theorem torusNormIwahoriMap_coe (f : T ⟶ U) (t : torusNormIwahori k L v T) :
    (torusNormIwahoriMap k L v f t : rationalPoints U.toGrp) =
      rationalPoints.map (CommGroupScheme.groupHom f) t := rfl

end Langlands.Geometry.Building
