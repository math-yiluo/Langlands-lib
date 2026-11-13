import Langlands.Geometry.Building.RootBuildingGaloisFieldExtension
import Langlands.Geometry.Building.IntegerValuation
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.HomConjugacy
import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # Fixed points of scalar-extended torus units -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- Fixation by the image of the character-valuation kernel after scalar extension.
For a split torus this is fixation by its unit subgroup. -/
def IsFixedByScalarTorusUnits (k K : Type u) [Field k] [Field K] [Algebra k K]
    (valuation : Valuation K (WithZero (Multiplicative ℤ)))
    {A G : GroupScheme (Spec (CommRingCat.of k))} (i : A ⟶ G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged k K G)) Y] (y : Y) : Prop :=
  ∀ t : rationalPoints (baseChanged k K A),
    t ∈ characterValuationKernel valuation (baseChanged k K A) →
      rationalPoints.map ((GroupScheme.baseChange (baseMap k K)).map i) t • y = y

/-- The preceding predicate over the maximal unramified extension, with its
canonical integer-valued valuation. -/
def IsFixedByUnramifiedTorusUnits (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A G : GroupScheme (Spec (CommRingCat.of F))} (i : A ⟶ G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (y : Y) : Prop :=
  IsFixedByScalarTorusUnits F (inertiaFixedField F) (MaximalUnramified.valuation F) i y

/-- A rational conjugacy of source groups transports fixation by their units.
Only the morphism from the first source to the second is needed. -/
theorem IsFixedByScalarTorusUnits.conjugate
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (valuation : Valuation K (WithZero (Multiplicative ℤ)))
    {A A' G : GroupScheme (Spec (CommRingCat.of k))}
    (i : A ⟶ G) (i' : A' ⟶ G) (e : A ⟶ A')
    (g : rationalPoints G) (he : i ≫ (G.innerIso g).hom = e ≫ i')
    {Y : Type v} [MulAction (rationalPoints (baseChanged k K G)) Y] {y : Y}
    (hy : IsFixedByScalarTorusUnits k K valuation i' y) :
    IsFixedByScalarTorusUnits k K valuation i ((rationalExtend k K G g)⁻¹ • y) := by
  intro t ht
  have hbase := congrArg ((GroupScheme.baseChange (baseMap k K)).map) he
  rw [Functor.map_comp, Functor.map_comp, baseChange_innerIso_hom,
    ← rationalExtend_eq_baseChangeBasePoint] at hbase
  have hpoint := congrArg
    (fun f => rationalPoints.map f t) hbase
  change rationalPoints.map
      ((baseChanged k K G).innerIso (rationalExtend k K G g)).hom
      (rationalPoints.map ((GroupScheme.baseChange (baseMap k K)).map i) t) =
    rationalPoints.map ((GroupScheme.baseChange (baseMap k K)).map i')
      (rationalPoints.map ((GroupScheme.baseChange (baseMap k K)).map e) t) at hpoint
  rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self] at hpoint
  have hfix := hy _
    (IntegerValuation.map_mem_characterValuationKernel valuation
      ((GroupScheme.baseChange (baseMap k K)).map e) ht)
  rw [← hpoint] at hfix
  have h := congrArg ((rationalExtend k K G g)⁻¹ • ·) hfix
  simpa only [mul_smul, inv_smul_smul] using h

end Langlands.Geometry.Building
