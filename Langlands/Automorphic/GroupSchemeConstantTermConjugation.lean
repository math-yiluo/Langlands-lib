import Langlands.Global.AdelicSubgroupQuotientTransport
import Langlands.Automorphic.GroupSchemeConstantTermConsequences

/-! # Constant terms along subgroups conjugate by a rational point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (g : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

/-- The adelic point by which the inner automorphism `innerIso g` conjugates adelic points. -/
abbrev innerAdelicPoint : AdelicGroupPoints F G :=
  G.constantPoint g ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F (AdeleRing (𝓞 F) F))))

/-- The conjugating adelic point is the principal image of the corresponding rational point. -/
theorem innerAdelicPoint_eq_rational :
    innerAdelicPoint F G g = AdelicGroupPoints.rational F G
      (G.constantPoint g ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))) :=
  (G.constantPoint_naturality g _).symm

/-- On adelic points, `innerIso g` is conjugation by `innerAdelicPoint F G g`. -/
theorem affinePointsTarget_innerIso_hom (x : AdelicGroupPoints F G) :
    G.affinePointsTarget (G.innerIso g).hom (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x =
      innerAdelicPoint F G g * x * (innerAdelicPoint F G g)⁻¹ :=
  G.comp_innerIso_hom g _ x

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (V : SubgroupFunctor G)
  [IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G))]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V)]

/-- Constant terms along `V` and along its inverse image under the rational inner automorphism
`innerIso g` agree after left translation by the conjugating point, for the intrinsic mass-one
quotient measures on both rational quotients. -/
theorem constantTerm_comap_innerIso (U : SubgroupFunctor G)
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G))]
    (hU : U = V.comap (G.innerIso g).hom)
    (f : ContinuousRationalFunctions F G) (y : AdelicGroupPoints F G) :
    constantTerm F G V (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) f y =
      constantTerm F G U (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U) f
        ((innerAdelicPoint F G g)⁻¹ * y) := by
  subst hU
  unfold constantTerm
  rw [← AdelicSubgroupPoints.integral_comp_rationalQuotientIso F (G.innerIso g) V]
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | _ u =>
    change evaluate F G f ((G.affinePointsTarget (G.innerIso g).hom
        (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (u : AdelicGroupPoints F G)) * y) =
      evaluate F G f ((u : AdelicGroupPoints F G) * ((innerAdelicPoint F G g)⁻¹ * y))
    rw [affinePointsTarget_innerIso_hom, mul_assoc, mul_assoc, innerAdelicPoint_eq_rational]
    exact f.val.property _ _

/-- Vanishing of all constant terms is the same along `V` and along its conjugate `U`. -/
theorem forall_constantTerm_eq_zero_comap_innerIso_iff (U : SubgroupFunctor G)
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G))]
    (hU : U = V.comap (G.innerIso g).hom) (f : ContinuousRationalFunctions F G) :
    (∀ y, constantTerm F G V
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) f y = 0) ↔
      ∀ y, constantTerm F G U
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U) f y = 0 := by
  constructor
  · intro h y
    have := h (innerAdelicPoint F G g * y)
    rwa [constantTerm_comap_innerIso F G g V U hU, inv_mul_cancel_left] at this
  · intro h y
    rw [constantTerm_comap_innerIso F G g V U hU]
    exact h _

end Langlands.Automorphic.GroupSchemeFunctions
