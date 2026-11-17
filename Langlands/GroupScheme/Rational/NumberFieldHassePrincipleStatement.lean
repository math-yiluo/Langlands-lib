import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.Global.AdelicGroupLocalPoints

/-! # The Hasse principle for first cohomology over number fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Quaternionic

/-- Hasse principle for `H¹` over a number field `F`, for a group `G` over `F` that is
semisimple and simply connected, or semisimple with trivial centre, or isomorphic to the
orthogonal group of a nondegenerate quadratic form. Classes are represented by cocycles on the
cover `Spec L → Spec F` of a finite separable extension `L`. If two such cocycles become
cohomologous on the base-changed cover `Spec (L ⊗ F_v) → Spec F_v` at every place `v`, they
are cohomologous on `Spec L`. -/
def NumberFieldHassePrincipleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    (IsSimplyConnected G ∨ IsAdjoint G ∨
      ∃ (m : ℕ) (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin m)),
        (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q ∧
          Nonempty (G ≅ (FirstKindInvolution.scalar F).isometryGroup q)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (ξ₁ ξ₂ : Cocycle G (Over.mk (algebraBaseMap F L))),
      (∀ i : Langlands.Global.Place F,
        let b := algebraBaseMap F (Langlands.Global.placeCompletion F i)
        let r := (Over.mapPullbackAdj b).counit.app (Over.mk (algebraBaseMap F L))
        ∃ f : (Over.pullback b).obj (Over.mk (algebraBaseMap F L)) ⟶
            ((baseChange b).obj G).X,
          ∀ {Z : Over (Spec (CommRingCat.of (Langlands.Global.placeCompletion F i)))}
            (x y : Z ⟶ (Over.pullback b).obj (Over.mk (algebraBaseMap F L))),
            (ξ₂.baseChange b _ r).toFun x y = ((ξ₁.baseChange b _ r).twist f).toFun x y) →
      ∃ f : Over.mk (algebraBaseMap F L) ⟶ G.X,
        ∀ {Z : Over (Spec (CommRingCat.of F))} (x y : Z ⟶ Over.mk (algebraBaseMap F L)),
          ξ₂.toFun x y = (ξ₁.twist f).toFun x y

end Langlands.GroupScheme
