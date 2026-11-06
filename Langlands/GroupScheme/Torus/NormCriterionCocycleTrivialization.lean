import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.Torus.SplitCoverCocycleVanishing
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Rational.DimensionLEOneTorusCocycleVanishingStatement
import Mathlib.FieldTheory.SeparableDegree

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (T : GroupScheme (Spec (CommRingCat.of k)))

/-- The finite-extension norm criterion trivializes a torus cocycle on its original
finite Galois cover, whether or not that cover splits the torus. -/
theorem IsTorus.cocycle_isTrivial_of_dimensionLEOne
    (hT : IsTorus T) (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (ξ : Cocycle T (GaloisCocycle.cover k L)) : ξ.IsTrivial := by
  have hTL := IsTorus.baseChange_of_isAlgebraic k L T hT
  obtain ⟨N, hN, hAN, hfinN, hgalN, hTN⟩ := torusFiniteGaloisSplitting L _ hTL
  let : Algebra k N := ((algebraMap L N).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L N := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional k N := FiniteDimensional.trans k L N
  let : Algebra.IsSeparable k N := Algebra.IsSeparable.trans k L N
  have hTN' := (IsSplitTorus.baseChange_fieldTower_iff k L N T).2 hTN
  let f : N →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra N (SeparableClosure k) := f.toRingHom.toAlgebra
  let : IsScalarTower k N (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let E := IntermediateField.normalClosure k N (SeparableClosure k)
  let : Algebra L E := ((algebraMap N E).comp (algebraMap L N)).toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap k E =
      (algebraMap N E).comp ((algebraMap L N).comp (algebraMap k L))
    rw [← IsScalarTower.algebraMap_eq k L N, ← IsScalarTower.algebraMap_eq k N E])
  let : FiniteDimensional L E := FiniteDimensional.right k L E
  let : IsGalois L E := IsGalois.tower_top_of_isGalois k L E
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  let Tc : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { T with comm := hT.isCommMonObj }
  have hTE : IsSplitTorus (TorusPointsTensorGalois.baseChanged k E Tc).toGrp :=
    hTN'.baseChange_fieldTower k N E T
  apply GaloisCocycle.isTrivial_of_refine k L E ξ
  exact TorusPointsTensorGalois.cocycle_isTrivial k E Tc hk hTE
    (ξ.refine (GaloisCocycle.coverMap k L E))

/-- Choose an actual trivializing point on the cocycle's original finite Galois cover. -/
def IsTorus.cocycleTrivializingPoint
    (hT : IsTorus T) (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (ξ : Cocycle T (GaloisCocycle.cover k L)) :
    GaloisCocycle.cover k L ⟶ T.X :=
  Classical.choose (hT.cocycle_isTrivial_of_dimensionLEOne k L T hk ξ)

/-- The chosen point trivializes the cocycle on every relative test scheme. -/
theorem IsTorus.cocycleTrivializingPoint_spec
    (hT : IsTorus T) (hk : Langlands.FieldTheory.HasDimensionLEOne k)
    (ξ : Cocycle T (GaloisCocycle.cover k L))
    {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ GaloisCocycle.cover k L) :
    ξ.toFun a b =
      (a ≫ hT.cocycleTrivializingPoint k L T hk ξ) *
        (b ≫ hT.cocycleTrivializingPoint k L T hk ξ)⁻¹ :=
  Classical.choose_spec (hT.cocycle_isTrivial_of_dimensionLEOne k L T hk ξ) a b

end Langlands.GroupScheme
