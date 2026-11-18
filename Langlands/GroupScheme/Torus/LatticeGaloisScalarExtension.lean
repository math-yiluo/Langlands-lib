import Langlands.GroupScheme.Reductive.StarActionFiniteStageTower
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescent
import Mathlib.RepresentationTheory.Intertwining

/-! # Character transport after changing the ground scheme -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Tower

variable {B S K : Scheme.{u}} (b : S ⟶ B) (j : K ⟶ S)
  (a : K ⟶ K) (ha : a ≫ j = j) (G : GroupScheme B)

/-- Descent of points is compatible with changing the ground scheme from `B`
to `S`, under the canonical direct/iterated base-change isomorphism. -/
theorem descentPoint_scalarExtension_inv (U : Over K)
    (y : U ⟶ ((Over.pullback j).mapGrp.obj ((Over.pullback b).mapGrp.obj G)).X) :
    descentPoint j a ha ((Over.pullback b).mapGrp.obj G) U y ≫
        (baseChangeCompIso b j G).inv.hom.hom =
      descentPoint (j ≫ b) a (by rw [← Category.assoc, ha]) G U
        (y ≫ (baseChangeCompIso b j G).inv.hom.hom) := by
  apply (baseChangePointsEquiv (j ≫ b) G ((Over.map a).obj U)).injective
  apply Over.OverMorphism.ext
  change ((descentPoint j a ha ((Over.pullback b).mapGrp.obj G) U y).left ≫
      (baseChangeCompIso b j G).inv.hom.hom.left) ≫ pullback.fst G.X.hom (j ≫ b) = _
  have hj := descentPoint_left_fst j a ha ((Over.pullback b).mapGrp.obj G) U y
  change (descentPoint j a ha ((Over.pullback b).mapGrp.obj G) U y).left ≫
    pullback.fst (pullback.snd G.X.hom b) j =
      y.left ≫ pullback.fst (pullback.snd G.X.hom b) j at hj
  calc
    _ = ((descentPoint j a ha ((Over.pullback b).mapGrp.obj G) U y).left ≫
        pullback.fst (pullback.snd G.X.hom b) j) ≫ pullback.fst G.X.hom b := by
      rw [Category.assoc, baseChangeCompIso_inv_fst, Category.assoc]
    _ = (y.left ≫ pullback.fst (pullback.snd G.X.hom b) j) ≫
        pullback.fst G.X.hom b := congrArg (fun f => f ≫ pullback.fst G.X.hom b) hj
    _ = (y ≫ (baseChangeCompIso b j G).inv.hom.hom).left ≫
        pullback.fst G.X.hom (j ≫ b) := by
      change _ = (y.left ≫ (baseChangeCompIso b j G).inv.hom.hom.left) ≫ _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => y.left ≫ f) (baseChangeCompIso_inv_fst b j G).symm).trans
          (Category.assoc _ _ _).symm)
    _ = _ := (descentPoint_left_fst (j ≫ b) a _ G U _).symm

end Tower

namespace characterLattice

variable {B S K : Scheme.{u}} (b : S ⟶ B) (j : K ⟶ S) (a : K ⟶ K)
  (ha : a ≫ j = j) (T : CommGroupScheme B)

/-- Character transport over the original base agrees with transport over the
extended base, through the canonical isomorphism of the two pulled-back tori. -/
theorem transport_scalarExtension
    (χ : characterLattice ((CommGroupScheme.baseChange (j ≫ b)).obj T)) :
    (StarActionFiniteStage.towerIso b j T).inv ≫
        transport (j ≫ b) a (by rw [← Category.assoc, ha]) T χ =
      transport j a ha ((CommGroupScheme.baseChange b).obj T)
        ((StarActionFiniteStage.towerIso b j T).inv ≫ χ) := by
  apply CommGroupScheme.hom_ext_points
  intro U y
  apply (Gm.pointsEquiv K U).injective
  rw [comp_groupHom_comp, transport_points, transport_points]
  have hp := descentPoint_scalarExtension_inv b j a ha T.toGrp U y
  have hχ := congrArg (fun z => Gm.pointsEquiv K ((Over.map a).obj U)
    (z ≫ (CommGroupScheme.groupHom χ).hom.hom)) hp.symm
  have hc := congrArg (Gm.pointsEquiv K ((Over.map a).obj U))
    (comp_groupHom_comp (descentPoint j a ha ((CommGroupScheme.baseChange b).obj T).toGrp U y)
      (StarActionFiniteStage.towerIso b j T).inv χ)
  exact hχ.trans hc.symm

/-- The same scalar-extension compatibility along a specified equality of base maps. -/
theorem transport_scalarExtensionOf (bK : K ⟶ B) (hc : j ≫ b = bK)
    (χ : characterLattice ((CommGroupScheme.baseChange bK).obj T)) :
    (StarActionFiniteStage.towerIsoOf b j T bK hc).inv ≫
        transport bK a (by rw [← hc, ← Category.assoc, ha]) T χ =
      transport j a ha ((CommGroupScheme.baseChange b).obj T)
        ((StarActionFiniteStage.towerIsoOf b j T bK hc).inv ≫ χ) := by
  subst bK
  simpa only [StarActionFiniteStage.towerIsoOf, eqToIso_refl, Iso.refl_trans] using
    transport_scalarExtension b j a ha T χ

section Fields

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra E L] [Algebra k L] [IsScalarTower k E L]
  (hc : algebraBaseMap E L ≫ algebraBaseMap k E = algebraBaseMap k L)
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Restricting a relative Galois automorphism to the original ground field
intertwines the two actual character-lattice actions through the tower isomorphism. -/
theorem galoisRepresentation_scalarExtension (σ : L ≃ₐ[E] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)) :
    (StarActionFiniteStage.towerIsoOf (algebraBaseMap k E) (algebraBaseMap E L)
        T (algebraBaseMap k L) hc).inv ≫
        galoisRepresentation k L T (σ.restrictScalars k) χ =
      galoisRepresentation E L ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) σ
        ((StarActionFiniteStage.towerIsoOf (algebraBaseMap k E) (algebraBaseMap E L)
          T (algebraBaseMap k L) hc).inv ≫ χ) := by
  exact transport_scalarExtensionOf (algebraBaseMap k E) (algebraBaseMap E L)
    (galoisBaseMap E L σ) (galoisBaseMap_over E L σ) T (algebraBaseMap k L) hc χ

/-- The actual integral character Galois representations before and after
extension of the ground field are equivalent after restricting scalars. -/
def scalarExtensionGaloisEquiv :
    Representation.Equiv
      ((galoisRepresentation k L T).comp (AlgEquiv.restrictScalarsHom k))
      (galoisRepresentation E L ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) where
  __ := (characterLattice.congr
    (StarActionFiniteStage.towerIsoOf (algebraBaseMap k E) (algebraBaseMap E L)
      T (algebraBaseMap k L) hc)).toIntLinearEquiv
  isIntertwining' σ := by
    ext χ
    exact galoisRepresentation_scalarExtension hc T σ χ

end Fields

end characterLattice

end Langlands.GroupScheme
