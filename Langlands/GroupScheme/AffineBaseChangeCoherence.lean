import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.HomScheme.MultiplicativeTargetEtale
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Composition of pullbacks of commutative group schemes -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.CommGroupScheme

open GroupScheme.HomScheme

/-- Lift the standard pullback composition comparison to commutative group schemes,
using the indicated map for the composite. -/
def baseChangeCompAlong {X Y Z : Scheme.{u}}
    (b : Y ⟶ X) (c : Z ⟶ Y) (d : Z ⟶ X) (h : d = c ≫ b) :
    CommGroupScheme.baseChange d ≅ CommGroupScheme.baseChange b ⋙ CommGroupScheme.baseChange c :=
  eqToIso (congrArg CommGroupScheme.baseChange h) ≪≫
    NatIso.ofComponents (fun G => GroupScheme.CommGroupScheme.isoOfGroupIso
      (GroupScheme.baseChangeCompIso b c G.toGrp))
      (by
        intro G H f
        exact congrArg Additive.ofMul
          ((Functor.mapGrpNatIso (Over.pullbackComp c b) ≪≫
            Functor.mapGrpCompIso).hom.naturality f.toMul))

section Affine

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- The spectral maps of the algebras form the opposite compositional diagram. -/
theorem specBase_comp : specBase R T = specBase S T ≫ specBase R S := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The natural comparison from direct pullback to successive pullbacks over affine bases. -/
def affineBaseChangeCompNatIso :
    CommGroupScheme.baseChange (specBase R T) ≅
      CommGroupScheme.baseChange (specBase R S) ⋙ CommGroupScheme.baseChange (specBase S T) :=
  baseChangeCompAlong (specBase R S) (specBase S T) (specBase R T) (specBase_comp (S := S))

end Affine

end Langlands.CommGroupScheme
