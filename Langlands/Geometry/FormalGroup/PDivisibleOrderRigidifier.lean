import Langlands.Geometry.FormalGroup.PDivisibleSplitRigidifier

/-! # Order-linearity of the actual split rigidifier -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier RationalHom

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable {G H J : PDivisibleGroup R p} {O : Type v} [Ring O]

/-- An actual quasi-isogeny intertwining two integral order actions. -/
structure OrderQuasiIsogeny (a : O →+* End G) (b : O →+* End H) where
  val : QuasiIsogeny G H
  commutes : ∀ o : O, comp (ofHom (a o).asHom) val.hom = comp val.hom (ofHom (b o).asHom)

namespace OrderQuasiIsogeny

variable {a : O →+* End G} {b : O →+* End H} {d : O →+* End J}

/-- The actual inverse also intertwines the two order actions. -/
theorem inverse_commutes (e : OrderQuasiIsogeny a b) (o : O) :
    comp (ofHom (b o).asHom) e.val.inv = comp e.val.inv (ofHom (a o).asHom) := by
  have hG : comp e.val.hom e.val.inv = RationalHom.id G := e.val.hom_inv_id
  have hH : comp e.val.inv e.val.hom = RationalHom.id H := e.val.inv_hom_id
  calc
    comp (ofHom (b o).asHom) e.val.inv = comp (comp (comp e.val.inv e.val.hom) (ofHom (b o).asHom)) e.val.inv := by
      rw [hH, RationalHom.id_comp]
    _ = comp (comp e.val.inv (comp (ofHom (a o).asHom) e.val.hom)) e.val.inv := by
      rw [RationalHom.comp_assoc e.val.inv e.val.hom, ← e.commutes o]
    _ = comp e.val.inv (ofHom (a o).asHom) := by
      rw [← RationalHom.comp_assoc e.val.inv, RationalHom.comp_assoc, hG, RationalHom.comp_id]

/-- Reverse both the actual quasi-isogeny and its order-linearity equation. -/
def symm (e : OrderQuasiIsogeny a b) : OrderQuasiIsogeny b a :=
  ⟨e.val.symm, e.inverse_commutes⟩

/-- Compose two actual order-linear quasi-isogenies. -/
def trans (e : OrderQuasiIsogeny a b) (f : OrderQuasiIsogeny b d) : OrderQuasiIsogeny a d where
  val := e.val.trans f.val
  commutes o := by
    change comp (ofHom (a o).asHom) (comp e.val.hom f.val.hom) =
      comp (comp e.val.hom f.val.hom) (ofHom (d o).asHom)
    rw [← RationalHom.comp_assoc (ofHom (a o).asHom), e.commutes o, RationalHom.comp_assoc,
      f.commutes o, ← RationalHom.comp_assoc e.val.hom]

end OrderQuasiIsogeny

variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- The actual split rigidifier intertwines the ordinary and opposite order actions. -/
def splitOrderRigidifier {a : O →+* End G} {b : O →+* End H}
    (e : OrderQuasiIsogeny a b) (c : ℚ_[p]ˣ) :
    OrderQuasiIsogeny (splitOrderAction a hExact) (splitOrderAction b hExact) where
  val := splitRigidifier hExact e.val c
  commutes o := by
    let f := e.val.hom
    let g := (c : ℚ_[p]) • dualMap hExact e.val.inv
    let a₁ := (a o.2).asHom
    let a₂ := (a o.1.unop).asHom.dual hExact
    let b₁ := (b o.2).asHom
    let b₂ := (b o.1.unop).asHom.dual hExact
    have hf : comp (ofHom a₁) f = comp f (ofHom b₁) := e.commutes o.2
    have h := congrArg (dualMap hExact) (e.inverse_commutes o.1.unop)
    simp only [dualMap_comp, dualMap_ofHom] at h
    have hg : comp (ofHom a₂) g = comp g (ofHom b₂) := by
      change comp (ofHom a₂) ((c : ℚ_[p]) • dualMap hExact e.val.inv) =
        comp ((c : ℚ_[p]) • dualMap hExact e.val.inv) (ofHom b₂)
      rw [RationalHom.comp_smul, RationalHom.smul_comp]
      exact congrArg ((c : ℚ_[p]) • ·) h.symm
    change comp (ofHom (Hom.prodMap a₁ a₂)) (prodMap f g) =
      comp (prodMap f g) (ofHom (Hom.prodMap b₁ b₂))
    rw [← prodMap_ofHom, ← prodMap_ofHom, prodMap_comp, prodMap_comp, hf, hg]

@[simp] theorem splitOrderRigidifier_val {a : O →+* End G} {b : O →+* End H}
    (e : OrderQuasiIsogeny a b) (c : ℚ_[p]ˣ) :
    (splitOrderRigidifier hExact e c).val = splitRigidifier hExact e.val c := rfl

end Langlands.PDivisibleGroup
