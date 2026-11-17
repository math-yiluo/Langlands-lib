import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.Global.AdelicGroupLocalPoints

/-! # The Hasse principle for first cohomology of reductive groups over `ℚ` -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Let `G` be a connected reductive group over `ℚ` whose derived group `D` is simply connected,
and let `q : G ⟶ T` be an fppf quotient of `G` by `D`. If `T` satisfies the Hasse principle for
`H¹`, so does `G`. A group `H` over `ℚ` satisfies the Hasse principle for `H¹` when, for every
finite separable extension `L` of `ℚ`, two cocycles of `H` on the cover `Spec L → Spec ℚ` that
become cohomologous on `Spec (ℚ_v ⊗ L) → Spec ℚ_v` at every place `v` of `ℚ` are cohomologous
on `Spec L`. -/
def RationalReductiveHassePrincipleStatement : Prop :=
  let HassePrinciple : GroupScheme (Spec (CommRingCat.of ℚ)) → Prop := fun H =>
    ∀ (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [Algebra.IsSeparable ℚ L]
      (ξ₁ ξ₂ : Cocycle H (Over.mk (algebraBaseMap ℚ L))),
      (∀ i : Langlands.Global.Place ℚ,
        let b := algebraBaseMap ℚ (Langlands.Global.placeCompletion ℚ i)
        let r := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap ℚ L))
        ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap ℚ L)) ⟶
            ((baseChange b).obj H).X,
          ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion ℚ i)))}
            (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap ℚ L))),
            (ξ₂.baseChange b _ r).toFun x y = ((ξ₁.baseChange b _ r).twist f).toFun x y) →
      ∃ f : Over.mk (algebraBaseMap ℚ L) ⟶ H.X,
        ∀ {Z : Over (Spec (CommRingCat.of ℚ))} (x y : Z ⟶ Over.mk (algebraBaseMap ℚ L)),
          ξ₂.toFun x y = (ξ₁.twist f).toFun x y
  ∀ (G D T : GroupScheme (Spec (CommRingCat.of ℚ))) (d : D ⟶ G) (q : G ⟶ T),
    IsConnectedReductive G → IsDerivedSubgroup d → IsSimplyConnected D →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
    HassePrinciple T → HassePrinciple G

end Langlands.GroupScheme
