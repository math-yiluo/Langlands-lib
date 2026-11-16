import Langlands.GroupScheme.Torus.MaximalModuliUniqueness
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamilyNormalizer
import Langlands.GroupScheme.HomogeneousQuotientMonomorphism
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Normalizer orbits in supplied universal maximal-torus moduli -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {M U : Over S} {K : CommGroupScheme M.left} {H : CommGroupScheme S}

/-- Every conjugate of a maximal torus is fibrewise maximal on its parameter base. -/
theorem isFibrewiseMaximalTorus_conjugateFamily
    (i : H.toGrp ⟶ G) (hi : IsFibrewiseMaximalTorus i) (g : U ⟶ G.X) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange U.hom).obj H)
      (SubgroupFunctor.conjugateFamily i g) :=
  (hi.baseChange U.hom).comp_iso
    (((baseChange U.hom).obj G).innerIso ((baseChangeBasePointsEquiv U.hom G).symm g))

/-- Classify all conjugates of a fixed maximal torus using the universal point of G. -/
def maximalOrbit
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) : G.X ⟶ M :=
  Classical.choose (huni G.X ((CommGroupScheme.baseChange G.X.hom).obj H)
    (SubgroupFunctor.conjugateFamily i (𝟙 G.X)) (hH.baseChange G.X.hom)
    (SubgroupFunctor.isClosedSubgroup_conjugatePullback G.X.hom i hi _)
    (isFibrewiseMaximalTorus_conjugateFamily i hmax (𝟙 G.X)))

/-- The orbit morphism pulls back the universal family to the actual conjugate family. -/
theorem evaluate_maximalOrbit_id
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) :
    evaluate j (maximalOrbit j huni i hH hi hmax) =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily i (𝟙 G.X)) :=
  (Classical.choose_spec (huni G.X ((CommGroupScheme.baseChange G.X.hom).obj H)
    (SubgroupFunctor.conjugateFamily i (𝟙 G.X)) (hH.baseChange G.X.hom)
    (SubgroupFunctor.isClosedSubgroup_conjugatePullback G.X.hom i hi _)
    (isFibrewiseMaximalTorus_conjugateFamily i hmax (𝟙 G.X)))).1

/-- On every test, the orbit parameter classifies conjugation by that test's group point. -/
theorem evaluate_maximalOrbit
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) (g : U ⟶ G.X) :
    evaluate j (g ≫ maximalOrbit j huni i hH hi hmax) =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily i g) := by
  rw [← evaluate_comp]
  rw [evaluate_eq_of_range_eq _ _ (evaluate_maximalOrbit_id j huni i hH hi hmax) g]
  simpa only [Category.comp_id] using SubgroupFunctor.evaluate_conjugateFamily i (𝟙 G.X) g

/-- The exact all-test fibers of the orbit are right cosets of the full normalizer. -/
theorem maximalOrbit_fibers
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) (g h : U ⟶ G.X) :
    g ≫ maximalOrbit j huni i hH hi hmax = h ≫ maximalOrbit j huni i hH hi hmax ↔
      g⁻¹ * h ∈ (torusNormalizer i).carrier U := by
  calc
    _ ↔ evaluate j (g ≫ maximalOrbit j huni i hH hi hmax) =
        evaluate j (h ≫ maximalOrbit j huni i hH hi hmax) :=
      (huni.evaluate_injective hK hj hm).eq_iff.symm
    _ ↔ _ := by
      rw [evaluate_maximalOrbit, evaluate_maximalOrbit]
      exact SubgroupFunctor.range_conjugateFamily_eq_iff i g h

end Langlands.GroupScheme.TorusSubgroupModuli
