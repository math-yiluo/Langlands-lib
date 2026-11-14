import Langlands.Geometry.Building.Kottwitz.CocenterTorusRestriction
import Langlands.Geometry.Building.Kottwitz.CocenterCocharacterExactness
import Langlands.Geometry.Building.Kottwitz.CocenterTargetBijectivityReduction
import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedConstructionReduction
import Langlands.Geometry.Building.Kottwitz.TorusMapStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Cocenter Kottwitz surjectivity through maximal-torus points -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section Coinvariants

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
  (K : Type u) [Field K] [Algebra k K] [Algebra K E]
  [IsScalarTower k K E] [Normal k K]

/-- Surjectivity of actual geometric cocharacters descends to integral
inertia coinvariants. -/
theorem torusInertiaMap_surjective_of_geometric_surjective
    (hf : Function.Surjective (geometricCocharacterMap k E f)) :
    Function.Surjective (torusInertiaMap k E f K) := by
  intro y
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨w, hw⟩ := hf v
  refine ⟨inertiaProjection k K E (cocharacterLattice.galoisRepresentation k E S) w, ?_⟩
  rw [torusInertiaMap_projection, hw]

end Coinvariants

section CocenterRestriction

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k G) (c : Cocenter k G)

variable (E : Type u) [Field E] [Algebra k E] [IsSepClosure k E]
  (K : Type u) [Field K] [Algebra k K] [Algebra K E]
  [IsScalarTower k K E] [Normal k K]

/-- The restricted cocenter quotient is surjective on actual inertia
cocharacter targets. -/
theorem cocenterTorusInertiaMap_surjective :
    Function.Surjective (torusInertiaMap k E (cocenterTorusRestriction a c) K) := by
  let : IsSepClosed E := IsSepClosure.sep_closed k
  have hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E a.torus.toGrp) :=
    SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
      Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning _
      (IsTorus.baseChange_of_isAlgebraic k E a.torus.toGrp a.isMaximal.1)
  exact torusInertiaMap_surjective_of_geometric_surjective k E
    (cocenterTorusRestriction a c) K (cocenter_cocharacter_surjective a c E hTE)

end CocenterRestriction

section KottwitzComposite

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (a : Choice k G) (c : Cocenter k G)

/-- Torus surjectivity and naturality for the actual maximal-torus restriction
give surjectivity of the cocenter Kottwitz composite on ambient group points. -/
theorem cocenterKottwitzComposite_surjective_of_torus_data
    (hsurj : Function.Surjective (torusKottwitz F k a.torus a.isMaximal.1))
    (hnat : ∀ x : torusKPoints F k a.torus,
      (torusKottwitz F k c.torus c.isTorus
        (affinePointsTarget a.torus.toGrp
          (CommGroupScheme.groupHom (cocenterTorusRestriction a c))
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      torusInertiaMap k (SeparableClosure F) (cocenterTorusRestriction a c)
        (UnramifiedClosure F) (torusKottwitz F k a.torus a.isMaximal.1 x).toAdd) :
    Function.Surjective ((torusKottwitz F k c.torus c.isTorus).comp
      (G.affinePointsTarget c.quotient (CommAlgCat.of k (UnramifiedClosure F)))) := by
  intro y
  obtain ⟨v, hv⟩ := cocenterTorusInertiaMap_surjective a c
    (SeparableClosure F) (UnramifiedClosure F) y.toAdd
  obtain ⟨t, ht⟩ := hsurj (Multiplicative.ofAdd v)
  refine ⟨affinePointsTarget a.torus.toGrp a.inclusion
    (CommAlgCat.of k (UnramifiedClosure F)) t, ?_⟩
  apply Multiplicative.toAdd.injective
  have hp : affinePointsTarget a.torus.toGrp
      (CommGroupScheme.groupHom (cocenterTorusRestriction a c))
      (CommAlgCat.of k (UnramifiedClosure F)) t =
      affinePointsTarget G c.quotient (CommAlgCat.of k (UnramifiedClosure F))
        (affinePointsTarget a.torus.toGrp a.inclusion
          (CommAlgCat.of k (UnramifiedClosure F)) t) := by
    change t ≫ (a.inclusion ≫ c.quotient).hom.hom =
      (t ≫ a.inclusion.hom.hom) ≫ c.quotient.hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  change (torusKottwitz F k c.torus c.isTorus
    (affinePointsTarget G c.quotient (CommAlgCat.of k (UnramifiedClosure F))
      (affinePointsTarget a.torus.toGrp a.inclusion
        (CommAlgCat.of k (UnramifiedClosure F)) t))).toAdd = y.toAdd
  rw [← hp, hnat, ht]
  exact hv

end KottwitzComposite

/-- The complete cocenter construction follows from the five existing
comparison/descent statements, torus existence, and actual torus naturality. -/
theorem simplyConnectedDerivedKottwitz_of_torus_inputs
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (htorus : TorusFundamentalComparisonStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (hexists : TorusKottwitzExistenceStatement.{u})
    (hnat : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (k : Type u) [Field k]
      [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
      [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
      [Normal k (UnramifiedClosure F)]
      (S T : CommGroupScheme (Spec (CommRingCat.of k)))
      (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp) (f : S ⟶ T)
      (x : torusKPoints F k S),
      (torusKottwitz F k T hT
        (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
        (torusKottwitz F k S hS x).toAdd) :
    SimplyConnectedDerivedKottwitzStatement.{u} := by
  intro F _ _ _ _ k _ _ _ _ _ _ G hG hsc
  let a := chosenChoice k G hG
  let c := Classical.choice (nonempty_cocenter k G hG)
  refine simplyConnectedDerivedKottwitz_of_cocenter_data F k G hG
    hcmp hfund htorus hmap hinertia hsc
    (fun d => cocenterTargetMap_bijective_of_statements
      hcmp hfund htorus hmap hinertia F k G hG hsc d) c ?_ ?_
  · intro d x
    exact hnat F k c.torus d.torus c.isTorus d.isTorus (c.map d hG (𝟙 G)) x
  · exact cocenterKottwitzComposite_surjective_of_torus_data F k G a c
      (hexists F k a.torus a.isMaximal.1).2.2.1
      (hnat F k a.torus c.torus a.isMaximal.1 c.isTorus (cocenterTorusRestriction a c))

end Langlands.Geometry.Building.Kottwitz
