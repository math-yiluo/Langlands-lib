import Langlands.Geometry.FormalGroup.PDivisibleRationalDuality
import Langlands.Geometry.FormalGroup.PDivisibleRationalProduct

/-! # The actual split rigidifier of the polarized p-divisible product -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable {G H G' H' : PDivisibleGroup R p}

namespace QuasiIsogeny

/-- Multiply a rational isomorphism by a nonzero scalar, with inverse scalar on the inverse. -/
def scale (e : QuasiIsogeny G H) (c : ℚ_[p]ˣ) : QuasiIsogeny G H where
  hom := (c : ℚ_[p]) • e.hom
  inv := (↑c⁻¹ : ℚ_[p]) • e.inv
  hom_inv_id := by
    have he : RationalHom.comp e.hom e.inv = RationalHom.id G := e.hom_inv_id
    change RationalHom.comp ((c : ℚ_[p]) • e.hom) ((↑c⁻¹ : ℚ_[p]) • e.inv) = RationalHom.id G
    rw [RationalHom.smul_comp, RationalHom.comp_smul, smul_smul, Units.mul_inv, one_smul, he]
  inv_hom_id := by
    have he : RationalHom.comp e.inv e.hom = RationalHom.id H := e.inv_hom_id
    change RationalHom.comp ((↑c⁻¹ : ℚ_[p]) • e.inv) ((c : ℚ_[p]) • e.hom) = RationalHom.id H
    rw [RationalHom.smul_comp, RationalHom.comp_smul, smul_smul, Units.inv_mul, one_smul, he]

/-- The componentwise product of two quasi-isogenies of actual towers. -/
def prod (e : QuasiIsogeny G G') (f : QuasiIsogeny H H') : QuasiIsogeny (G.prod H) (G'.prod H') where
  hom := RationalHom.prodMap e.hom f.hom
  inv := RationalHom.prodMap e.inv f.inv
  hom_inv_id := by
    have he : RationalHom.comp e.hom e.inv = RationalHom.id G := e.hom_inv_id
    have hf : RationalHom.comp f.hom f.inv = RationalHom.id H := f.hom_inv_id
    change RationalHom.comp (RationalHom.prodMap e.hom f.hom) (RationalHom.prodMap e.inv f.inv) =
      RationalHom.id (G.prod H)
    rw [RationalHom.prodMap_comp, he, hf, RationalHom.prodMap_id]
  inv_hom_id := by
    have he : RationalHom.comp e.inv e.hom = RationalHom.id G' := e.inv_hom_id
    have hf : RationalHom.comp f.inv f.hom = RationalHom.id H' := f.inv_hom_id
    change RationalHom.comp (RationalHom.prodMap e.inv f.inv) (RationalHom.prodMap e.hom f.hom) =
      RationalHom.id (G'.prod H')
    rw [RationalHom.prodMap_comp, he, hf, RationalHom.prodMap_id]

end QuasiIsogeny

variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- The actual split rigidifier with primal part e and one common multiplier c.
The dual factor acts by c times the inverse of the actual Cartier dual of e. -/
def splitRigidifier (e : QuasiIsogeny G H) (c : ℚ_[p]ˣ) :
    QuasiIsogeny (G.splitWithDual hExact) (H.splitWithDual hExact) :=
  QuasiIsogeny.prod e (QuasiIsogeny.scale (G := G.dual hExact) (H := H.dual hExact)
    (e.dual hExact).symm c)

@[simp] theorem splitRigidifier_hom (e : QuasiIsogeny G H) (c : ℚ_[p]ˣ) :
    (splitRigidifier hExact e c).hom = RationalHom.prodMap e.hom
      ((c : ℚ_[p]) • RationalHom.dualMap hExact e.inv) := rfl

@[simp] theorem splitRigidifier_inv (e : QuasiIsogeny G H) (c : ℚ_[p]ˣ) :
    (splitRigidifier hExact e c).inv = RationalHom.prodMap e.inv
      ((↑c⁻¹ : ℚ_[p]) • RationalHom.dualMap hExact e.hom) := rfl

/-- Projection of the actual split rigidifier recovers the original primal map. -/
theorem splitRigidifier_primal (e : QuasiIsogeny G H) (c : ℚ_[p]ˣ) :
    RationalHom.comp (RationalHom.ofHom (prodInl G (G.dual hExact)))
      (RationalHom.comp (splitRigidifier hExact e c).hom
        (RationalHom.ofHom (prodFst H (H.dual hExact)))) = e.hom := by
  change RationalHom.comp (RationalHom.ofHom (prodInl G (G.dual hExact)))
    (RationalHom.comp (RationalHom.prodMap e.hom ((c : ℚ_[p]) • RationalHom.dualMap hExact e.inv))
      (RationalHom.ofHom (prodFst H (H.dual hExact)))) = e.hom
  rw [RationalHom.prodMap_fst, ← RationalHom.comp_assoc, ← RationalHom.ofHom_comp,
    prodInl_fst, RationalHom.ofHom_id, RationalHom.id_comp]

/-- The other block of the actual split rigidifier is the scaled inverse dual. -/
theorem splitRigidifier_dual (e : QuasiIsogeny G H) (c : ℚ_[p]ˣ) :
    RationalHom.comp (RationalHom.ofHom (prodInr G (G.dual hExact)))
      (RationalHom.comp (splitRigidifier hExact e c).hom
        (RationalHom.ofHom (prodSnd H (H.dual hExact)))) =
      (c : ℚ_[p]) • RationalHom.dualMap hExact e.inv := by
  change RationalHom.comp (RationalHom.ofHom (prodInr G (G.dual hExact)))
    (RationalHom.comp (RationalHom.prodMap e.hom ((c : ℚ_[p]) • RationalHom.dualMap hExact e.inv))
      (RationalHom.ofHom (prodSnd H (H.dual hExact)))) = _
  rw [RationalHom.prodMap_snd, ← RationalHom.comp_assoc, ← RationalHom.ofHom_comp,
    prodInr_snd, RationalHom.ofHom_id, RationalHom.id_comp]

/-- The dual block is characterized by the rational Cartier adjoint equation for
similitudes of the split evaluation pairing. -/
theorem dualBlock_eq_iff_adjoint (e : QuasiIsogeny G H) (c : ℚ_[p])
    (z : RationalHom (G.dual hExact) (H.dual hExact)) :
    z = c • RationalHom.dualMap hExact e.inv ↔
      RationalHom.comp z (RationalHom.dualMap hExact e.hom) = c • RationalHom.id (G.dual hExact) := by
  have hG : RationalHom.comp e.hom e.inv = RationalHom.id G := e.hom_inv_id
  have hH : RationalHom.comp e.inv e.hom = RationalHom.id H := e.inv_hom_id
  constructor
  · intro hz
    rw [hz, RationalHom.smul_comp, ← RationalHom.dualMap_comp, hG, RationalHom.dualMap_id]
  · intro hz
    calc
      z = RationalHom.comp z (RationalHom.id (H.dual hExact)) := (RationalHom.comp_id z).symm
      _ = RationalHom.comp z (RationalHom.comp (RationalHom.dualMap hExact e.hom)
          (RationalHom.dualMap hExact e.inv)) := by
        rw [← RationalHom.dualMap_comp, hH, RationalHom.dualMap_id]
      _ = c • RationalHom.dualMap hExact e.inv := by
        rw [← RationalHom.comp_assoc, hz, RationalHom.smul_comp, RationalHom.id_comp]

end Langlands.PDivisibleGroup
