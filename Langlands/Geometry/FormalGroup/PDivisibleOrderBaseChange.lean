import Langlands.Geometry.FormalGroup.HarrisSplitPDivisiblePoint
import Langlands.Geometry.FormalGroup.PDivisibleBaseChangeCoherence

/-! # Pullback of order-linear quasi-isogenies -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

namespace Langlands.PDivisibleGroup

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable {p : ℕ} [Fact p.Prime] {A : Type v} [Ring A]
variable {G H : PDivisibleGroup (CommRingCat.of R) p}
variable {a : A →+* End G} {b : A →+* End H}

/-- Pullback of the actual rational map and its inverse respects the pulled-back order actions. -/
def OrderQuasiIsogeny.baseChange [Algebra R S] (e : OrderQuasiIsogeny a b) :
    OrderQuasiIsogeny ((baseChangeEnd (S := S) G).comp a) ((baseChangeEnd (S := S) H).comp b) where
  val := e.val.baseChange (S := S)
  commutes t := by
    let F := baseChangeFunctor R S p
    change RationalHom.comp (RationalHom.ofHom (F.map (a t)))
        (RationalHom.baseChangeMap (S := S) e.val.hom) =
      RationalHom.comp (RationalHom.baseChangeMap (S := S) e.val.hom)
        (RationalHom.ofHom (F.map (b t)))
    have h := congrArg (RationalHom.baseChangeMap (S := S)) (e.commutes t)
    simp only [RationalHom.baseChangeMap_comp, RationalHom.baseChangeMap_ofHom] at h
    exact h

/-- Identity pullback gives the order-linear comparison with the original tower. -/
def baseChangeIdOrderIso (a : A →+* End G) :
    OrderQuasiIsogeny ((baseChangeEnd (S := R) G).comp a) a :=
  OrderQuasiIsogeny.ofIso (baseChangeIdIso G) (fun t => (baseChangeIdNatIso R p).hom.naturality (a t))

/-- The direct-to-successive pullback comparison preserves the order action. -/
def baseChangeCompOrderIso [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (a : A →+* End G) :
    OrderQuasiIsogeny ((baseChangeEnd (S := T) G).comp a)
      ((baseChangeEnd (S := T) ((baseChangeFunctor R S p).obj G)).comp
        ((baseChangeEnd (S := S) G).comp a)) :=
  OrderQuasiIsogeny.ofIso (baseChangeCompIso (S := S) (T := T) G)
    (fun t => (baseChangeCompNatIso R S T p).hom.naturality (a t))

end Langlands.PDivisibleGroup
