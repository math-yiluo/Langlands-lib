import Langlands.Geometry.FormalGroup.HarrisSplitPDivisibleClasses
import Langlands.Geometry.FormalGroup.PDivisibleRationalSplitBaseChange

/-! # Actual rational frame similitudes and their action on the framing -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] {A : Type v} [Ring A]
variable {G : PDivisibleGroup R p}

/-- The automorphisms of the actual rational tower that commute with the order. -/
def orderAut (a : A →+* End G) : Subgroup (Aut (RationalCategory.of G)) where
  carrier := {g | ∀ t, RationalHom.comp (RationalHom.ofHom (a t)) g.hom =
    RationalHom.comp g.hom (RationalHom.ofHom (a t))}
  one_mem' t := by
    change RationalHom.comp (RationalHom.ofHom (a t)) (RationalHom.id G) =
      RationalHom.comp (RationalHom.id G) (RationalHom.ofHom (a t))
    rw [RationalHom.comp_id, RationalHom.id_comp]
  mul_mem' {g h} hg hh :=
    (OrderQuasiIsogeny.trans (a := a) (b := a) (d := a) ⟨h, hh⟩ ⟨g, hg⟩).commutes
  inv_mem' {g} hg := (OrderQuasiIsogeny.symm (a := a) (b := a) ⟨g, hg⟩).commutes

/-- Regard an actual order-linear automorphism as a rigidifier of the fixed frame. -/
def OrderQuasiIsogeny.ofAut {a : A →+* End G} (g : orderAut a) : OrderQuasiIsogeny a a :=
  ⟨g.val, g.property⟩

/-- The actual rational isomorphism determines the order-linear isomorphism. -/
theorem OrderQuasiIsogeny.ext_val {H : PDivisibleGroup R p} {a : A →+* End G} {b : A →+* End H}
    {e f : OrderQuasiIsogeny a b} (h : e.val = f.val) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- A split frame similitude is a primal order-linear automorphism and one multiplier. -/
abbrev SplitFrameSimilitudes (a : A →+* End G) := orderAut a × ℚ_[p]ˣ

variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- The split frame similitudes act by actual order-linear automorphisms of the split frame. -/
def splitFrameAut (a : A →+* End G) :
    SplitFrameSimilitudes a →* orderAut (splitOrderAction a hExact) where
  toFun g := ⟨(splitOrderRigidifier hExact (OrderQuasiIsogeny.ofAut g.1) g.2).val,
    (splitOrderRigidifier hExact (OrderQuasiIsogeny.ofAut g.1) g.2).commutes⟩
  map_one' := by
    apply Subtype.ext
    apply Aut.ext
    change RationalHom.prodMap (RationalHom.id G)
      ((↑(1 : ℚ_[p]ˣ) : ℚ_[p]) • RationalHom.dualMap hExact (RationalHom.id G)) =
      RationalHom.id (G.splitWithDual hExact)
    rw [Units.val_one, one_smul, RationalHom.dualMap_id, RationalHom.prodMap_id]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    change splitRigidifier hExact (h.1.val.trans g.1.val) (g.2 * h.2) =
      (splitRigidifier hExact h.1.val h.2).trans (splitRigidifier hExact g.1.val g.2)
    rw [mul_comm g.2 h.2]
    exact splitRigidifier_trans hExact h.1.val g.1.val h.2 g.2

end Langlands.PDivisibleGroup

namespace Langlands.PDivisibleGroup.PolarizedFramedTower

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {p : ℕ} [Fact p.Prime]
variable {A : Type v} [Ring A] {G : PDivisibleGroup (CommRingCat.of S) p}
variable {a : A →+* End G}

/-- Precompose the actual rigidifier with the inverse of a frame automorphism. -/
def act (g : orderAut a) (X : PolarizedFramedTower (R := R) a) : PolarizedFramedTower (R := R) a :=
  { X with rigidifier := (OrderQuasiIsogeny.ofAut g).symm.trans X.rigidifier }

@[simp] theorem act_one (X : PolarizedFramedTower (R := R) a) : act 1 X = X := by
  have h : (OrderQuasiIsogeny.ofAut (1 : orderAut a)).symm.trans X.rigidifier = X.rigidifier := by
    apply OrderQuasiIsogeny.ext_val
    exact CategoryTheory.Iso.refl_trans X.rigidifier.val
  unfold act
  rw [h]

theorem act_mul (g h : orderAut a) (X : PolarizedFramedTower (R := R) a) :
    act (g * h) X = act g (act h X) := by
  have hcomp : (OrderQuasiIsogeny.ofAut (g * h)).symm.trans X.rigidifier =
      (OrderQuasiIsogeny.ofAut g).symm.trans ((OrderQuasiIsogeny.ofAut h).symm.trans X.rigidifier) := by
    apply OrderQuasiIsogeny.ext_val
    apply CategoryTheory.Iso.ext
    change RationalHom.comp (RationalHom.comp g.val.inv h.val.inv) X.rigidifier.val.hom =
      RationalHom.comp g.val.inv (RationalHom.comp h.val.inv X.rigidifier.val.hom)
    exact RationalHom.comp_assoc _ _ _
  exact congrArg (fun e => { X with rigidifier := e }) hcomp

/-- Changing the target by a polarized isomorphism commutes with precomposition. -/
def Iso.act {X Y : PolarizedFramedTower (R := R) a} (e : Iso X Y) (g : orderAut a) :
    Iso (act g X) (act g Y) where
  targetIso := e.targetIso
  order := e.order
  pairing := e.pairing
  frame := by
    let q := (OrderQuasiIsogeny.ofAut g).val.inv
    change RationalHom.comp (RationalHom.comp q X.rigidifier.val.hom)
      (RationalHom.ofHom ((baseChangeFunctor R S p).map e.targetIso.hom)) =
      RationalHom.comp q Y.rigidifier.val.hom
    rw [RationalHom.comp_assoc, e.frame]

/-- The frame automorphism acts on the polarized isomorphism classes. -/
def actClass (g : orderAut a) : Quotient (isoSetoid (R := R) (a := a)) →
    Quotient (isoSetoid (R := R) (a := a)) :=
  Quotient.map (act g) (fun _ _ ⟨e⟩ => ⟨e.act g⟩)

/-- The inverse-precomposition formula defines a left action on the actual classes. -/
@[instance_reducible] def frameAction : MulAction (orderAut a) (Quotient (isoSetoid (R := R) (a := a))) where
  smul := actClass
  one_smul x := Quotient.inductionOn x fun X => congrArg Quotient.mk'' (act_one X)
  mul_smul g h x := Quotient.inductionOn x fun X => congrArg Quotient.mk'' (act_mul g h X)

end Langlands.PDivisibleGroup.PolarizedFramedTower
