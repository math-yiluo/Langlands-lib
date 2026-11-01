import Langlands.AbelianScheme.RationalBaseChange
import Langlands.CategoryTheory.RationalizationDenominators

/-! # Actual integral maps underlying rational isomorphisms of abelian schemes -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme

variable {S S' : Scheme.{u}} {A B : AbelianScheme S}

/-- Integral representatives of a given rational isomorphism of actual abelian schemes. -/
abbrev RationalIsoIntegralData (e : Rationalization.of A ≅ Rationalization.of B) :=
  Rationalization.IntegralIsoData e

/-- Choose actual integral maps with nonzero denominators and exact inverse-multiple identities. -/
def rationalIsoIntegralData (e : Rationalization.of A ≅ Rationalization.of B) :
    RationalIsoIntegralData e :=
  Rationalization.integralIsoData e

namespace RationalIsoIntegralData

variable {e : Rationalization.of A ≅ Rationalization.of B}

/-- Transport supplied integral representatives by arbitrary actual scheme base change. -/
def baseChange (d : RationalIsoIntegralData e) (b : S' ⟶ S) :
    RationalIsoIntegralData (rationalBaseChangeIso b e) where
  homDenom := d.homDenom
  invDenom := d.invDenom
  homDenom_ne_zero := d.homDenom_ne_zero
  invDenom_ne_zero := d.invDenom_ne_zero
  hom := (AbelianScheme.baseChange b).map d.hom
  inv := (AbelianScheme.baseChange b).map d.inv
  ofHom_hom := by
    change Rationalization.ofHom ((AbelianScheme.baseChange b).map d.hom) =
      d.homDenom • rationalBaseChangeHom b e.hom
    rw [← rationalBaseChangeHom_ofHom, d.ofHom_hom, map_zsmul]
  ofHom_inv := by
    change Rationalization.ofHom ((AbelianScheme.baseChange b).map d.inv) =
      d.invDenom • rationalBaseChangeHom b e.inv
    rw [← rationalBaseChangeHom_ofHom, d.ofHom_inv, map_zsmul]
  hom_inv := by
    rw [← Functor.map_comp, d.hom_inv, Functor.map_zsmul, (AbelianScheme.baseChange b).map_id A]
  inv_hom := by
    rw [← Functor.map_comp, d.inv_hom, Functor.map_zsmul, (AbelianScheme.baseChange b).map_id B]

@[simp] theorem baseChange_homDenom (d : RationalIsoIntegralData e) (b : S' ⟶ S) :
    (baseChange d b).homDenom = d.homDenom := rfl

@[simp] theorem baseChange_invDenom (d : RationalIsoIntegralData e) (b : S' ⟶ S) :
    (baseChange d b).invDenom = d.invDenom := rfl

@[simp] theorem baseChange_hom (d : RationalIsoIntegralData e) (b : S' ⟶ S) :
    (baseChange d b).hom = (AbelianScheme.baseChange b).map d.hom := rfl

@[simp] theorem baseChange_inv (d : RationalIsoIntegralData e) (b : S' ⟶ S) :
    (baseChange d b).inv = (AbelianScheme.baseChange b).map d.inv := rfl

end RationalIsoIntegralData
end Langlands.AbelianScheme
