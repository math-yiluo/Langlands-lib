import Langlands.Geometry.Building.Kottwitz.CocenterFunctoriality
import Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonNaturality
import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement

/-! # Reducing simply-connected-derived Kottwitz naturality to torus naturality -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section NaturalAt

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)]

/-- The naturality property needed only for groups with simply connected derived group. -/
def SimplyConnectedDerivedKottwitzNaturalAt
    (H J : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hJ : IsConnectedReductive J)
    (hscH : HasSimplyConnectedDerivedGroup H) (hscJ : HasSimplyConnectedDerivedGroup J)
    (f : H ⟶ J) : Prop :=
  ∀ x : reductiveKPoints F k H,
    (simplyConnectedDerivedKottwitz F k J hJ hscJ
      (H.affinePointsTarget f (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
    fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F) J hJ H hH f
      (simplyConnectedDerivedKottwitz F k H hH hscH x).toAdd

end NaturalAt

variable
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (htorus : TorusFundamentalComparisonStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k]
    [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
    [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)
    (cH : Cocenter k H) (cG : Cocenter k G) (f : H ⟶ G)

include hcmp hfund htorus hmap hinertia

/-- The actual cocenter square induces a commuting square on inertia targets. -/
theorem cocenterTargetMap_natural_of_statements
    (x : ReductiveTarget F k H hH) :
    cocenterTargetMap F k G hG cG
        (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
          G hG H hH f x) =
      torusInertiaMap k (SeparableClosure F) (cH.map cG hH f) (UnramifiedClosure F)
        (cocenterTargetMap F k H hH cH x) := by
  let d := cH.map cG hH f
  have hleft := congrArg (fun m => m x)
    ((hmap k (UnramifiedClosure F) (SeparableClosure F)).2.2
      H G cG.torus.toGrp hH hG cG.isTorus.isConnectedReductive_of_fieldSplitting
      f cG.quotient)
  have hright := congrArg (fun m => m x)
    ((hmap k (UnramifiedClosure F) (SeparableClosure F)).2.2
      H cH.torus.toGrp cG.torus.toGrp hH cH.isTorus.isConnectedReductive_of_fieldSplitting
      cG.isTorus.isConnectedReductive_of_fieldSplitting cH.quotient
      (CommGroupScheme.groupHom d))
  dsimp only [LinearMap.comp_apply] at hleft hright
  rw [show cH.quotient ≫ CommGroupScheme.groupHom d = f ≫ cG.quotient from
    cH.quotient_map cG hH f] at hright
  unfold cocenterTargetMap
  simp only [LinearMap.comp_apply]
  rw [hleft, ← hright]
  exact torusInertiaComparison_natural_of_statements hcmp hfund htorus hmap hinertia
    k (UnramifiedClosure F) (SeparableClosure F) cH.torus cG.torus cH.isTorus cG.isTorus
    d _

/-- Torus naturality and the cocenter characterization imply naturality for
actual groups with simply connected derived subgroup. -/
theorem simplyConnectedDerivedKottwitz_natural_of_torus_naturality
    (hsc : SimplyConnectedDerivedKottwitzStatement.{u})
    (hscH : HasSimplyConnectedDerivedGroup H) (hscG : HasSimplyConnectedDerivedGroup G)
    (hnat : ∀ x : torusKPoints F k cH.torus,
      (torusKottwitz F k cG.torus cG.isTorus
        (affinePointsTarget cH.torus.toGrp (CommGroupScheme.groupHom (cH.map cG hH f))
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
        torusInertiaMap k (SeparableClosure F) (cH.map cG hH f) (UnramifiedClosure F)
          (torusKottwitz F k cH.torus cH.isTorus x).toAdd)
    (x : reductiveKPoints F k H) :
    (simplyConnectedDerivedKottwitz F k G hG hscG
      (H.affinePointsTarget f (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
      fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F) G hG H hH f
        (simplyConnectedDerivedKottwitz F k H hH hscH x).toAdd := by
  apply ((hsc F k G hG hscG).2.2.2 cG).1.1
  rw [(hsc F k G hG hscG).2.1 cG,
    cocenterTargetMap_natural_of_statements hcmp hfund htorus hmap hinertia
      F k H G hH hG cH cG f,
    (hsc F k H hH hscH).2.1 cH]
  have hx :
      G.affinePointsTarget cG.quotient (CommAlgCat.of k (UnramifiedClosure F))
          (H.affinePointsTarget f (CommAlgCat.of k (UnramifiedClosure F)) x) =
        affinePointsTarget cH.torus.toGrp
          (CommGroupScheme.groupHom (cH.map cG hH f))
          (CommAlgCat.of k (UnramifiedClosure F))
          (H.affinePointsTarget cH.quotient (CommAlgCat.of k (UnramifiedClosure F)) x) := by
    change (x ≫ f.hom.hom) ≫ cG.quotient.hom.hom =
      (x ≫ cH.quotient.hom.hom) ≫
        (CommGroupScheme.groupHom (cH.map cG hH f)).hom.hom
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom,
      cH.quotient_map cG hH f]
  rw [hx]
  exact hnat _

end Langlands.Geometry.Building.Kottwitz
