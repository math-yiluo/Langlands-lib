import Langlands.Shimura.PEL.PolarizedWeilOrderModel

/-! # Polarized actions on a supplied rationally isogenous model -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {R : Type v} [Ring R] [Algebra ℚ R] [StarRing R]

local notation "PObj" => PolarizedAction P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality S R

variable (X : PolarizedAction P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality S R)
variable (B : AbelianScheme S)
variable (e : Rationalization.of B ≅ Rationalization.of X.actionObj.abelianScheme)

/-- Conjugate the original rational action along the exact supplied isomorphism. -/
def PolarizedAction.isogenyAction : R →ₐ[ℚ] End0 B where
  toFun r := e.hom ≫ X.actionObj.action r ≫ e.inv
  map_one' := by
    change e.hom ≫ X.actionObj.action 1 ≫ e.inv = 𝟙 _
    rw [map_one]
    simp
  map_mul' r t := by
    change e.hom ≫ X.actionObj.action (r * t) ≫ e.inv =
      (e.hom ≫ X.actionObj.action t ≫ e.inv) ≫
        (e.hom ≫ X.actionObj.action r ≫ e.inv)
    rw [map_mul]
    change e.hom ≫ (X.actionObj.action t ≫ X.actionObj.action r) ≫ e.inv = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  map_zero' := by
    rw [map_zero]
    simp
  map_add' r t := by
    rw [map_add]
    change e.hom ≫ (X.actionObj.action r + X.actionObj.action t) ≫ e.inv =
      (e.hom ≫ X.actionObj.action r ≫ e.inv) +
        (e.hom ≫ X.actionObj.action t ≫ e.inv)
    rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' q := by
    rw [AlgHom.commutes]
    change e.hom ≫ (q • 𝟙 _) ≫ e.inv = q • 𝟙 _
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.hom_inv_id]

local notation "β" => PolarizedAction.isogenyAction (P := P) (X := X) (B := B) (e := e)

/-- The exact supplied rational isomorphism intertwines the conjugate action. -/
def PolarizedAction.isogenyActionIso :
    RationalAlgebraAction.of B β ≅ X.actionObj :=
  RationalAlgebraAction.isoMk e (by
    intro r
    change (e.hom ≫ X.actionObj.action r ≫ e.inv) ≫ e.hom =
      e.hom ≫ X.actionObj.action r
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

local notation "E" => PolarizedAction.isogenyActionIso (P := P) (X := X) (B := B) (e := e)

omit [QuasiSeparatedSpace S] in
/-- The comparison to the original action retains the exact input arrow. -/
@[simp] theorem PolarizedAction.isogenyActionIso_hom :
    RationalAlgebraAction.hom0 (E).hom = e.hom := rfl

omit [QuasiSeparatedSpace S] in
/-- It also retains the exact input inverse. -/
@[simp] theorem PolarizedAction.isogenyActionIso_inv :
    RationalAlgebraAction.hom0 (E).inv = e.inv := rfl

/-- Square both denominator choices to make their product positive without
changing the supplied rational isomorphism. -/
def PolarizedAction.isogenyIntegralData : Rationalization.IntegralIsoData e :=
  let d := Rationalization.integralIsoData e
  d.rescale d.homDenom d.invDenom d.homDenom_ne_zero d.invDenom_ne_zero

local notation "d" => PolarizedAction.isogenyIntegralData (P := P) (X := X) (B := B) (e := e)

/-- The two selected integral representatives have exact integral inverse identities. -/
def PolarizedAction.isogenyInverseData :
    Rationalization.IntegralInverseData B X.actionObj.abelianScheme where
  multiple := (d).homDenom * (d).invDenom
  multiple_ne_zero := mul_ne_zero (d).homDenom_ne_zero (d).invDenom_ne_zero
  hom := (d).hom
  inv := (d).inv
  hom_inv := (d).hom_inv
  inv_hom := (d).inv_hom

local notation "a" => PolarizedAction.isogenyInverseData (P := P) (X := X) (B := B) (e := e)

omit [QuasiSeparatedSpace S] in
theorem PolarizedAction.isogenyInverseData_pos : 0 < (a).multiple := by
  let c := Rationalization.integralIsoData e
  change 0 < (c.homDenom * c.homDenom) * (c.invDenom * c.invDenom)
  exact mul_pos (mul_self_pos.mpr c.homDenom_ne_zero)
    (mul_self_pos.mpr c.invDenom_ne_zero)

variable (W : DualWitness B)

local notation "addAA" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  X.actionObj.abelianScheme X.actionObj.abelianScheme X.hasDual X.hasDual
local notation "addBB" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  B B W.hasDual W.hasDual
local notation "addBA" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  B X.actionObj.abelianScheme W.hasDual X.hasDual
local notation "addAB" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  X.actionObj.abelianScheme B X.hasDual W.hasDual
local notation "pull" => integralDualPullbackHom P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  W.hasDual X.hasDual W.geometry X.geometry W.inverseBundle W.evaluation
  X.inversePoincare X.evaluation
local notation "pull0" => rationalDualPullbackHom0 P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  W.hasDual X.hasDual W.geometry X.geometry W.inverseBundle W.evaluation
  X.inversePoincare X.evaluation addBA

variable {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

omit [QuasiSeparatedSpace S] in
include p in
/-- The common positive inverse multiple is a unit on a characteristic-zero field scheme. -/
theorem PolarizedAction.isogenyInverseData_unit :
    IsUnit ((a).multiple : Γ(S, ⊤)) := by
  have hnK : IsUnit ((a).multiple : K) :=
    isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr (a).multiple_ne_zero)
  simpa only [map_intCast] using
    hnK.map ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom

/-- Pull back the original actual polarization along an integral multiple of
the exact supplied rational isomorphism. -/
def PolarizedAction.isogenyModelPolarization : B ⟶ W.dual P :=
  pull (d).hom X.polarization

local notation "lamB" => PolarizedAction.isogenyModelPolarization (P := P) (X := X) (B := B) (e := e) (W := W)

include p in
theorem PolarizedAction.isogenyModelPolarization_isPolarization :
    W.IsPolarization P lamB := by
  have hmaps := integralInverseData_finiteEtaleIsogenies a
    (PolarizedAction.isogenyInverseData_pos (P := P) (X := X) (B := B) (e := e))
    (PolarizedAction.isogenyInverseData_unit (P := P) (X := X) (B := B) (e := e) (p := p))
  have hduals := dualIntegralInverseData_finiteEtaleIsogenies
    P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability W.hasDual X.hasDual W.geometry X.geometry
    W.inverseBundle W.evaluation X.inversePoincare X.evaluation addBB addAA
    a (PolarizedAction.isogenyInverseData_pos (P := P) (X := X) (B := B) (e := e))
      (PolarizedAction.isogenyInverseData_unit (P := P) (X := X) (B := B) (e := e) (p := p))
  exact isPolarization_integralDualPullbackHom P.preservation P.square P.universality
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    W.hasDual X.hasDual W.geometry X.geometry W.inverseBundle W.evaluation
    X.inversePoincare X.evaluation (d).hom hmaps.1 hduals.2.2.1
    X.polarization X.isPolarization

/-- The exact supplied model carries a faithful rational action and actual
geometric polarization satisfying the original full involution equation. -/
def PolarizedAction.isogenyModel : PObj where
  actionObj := RationalAlgebraAction.of B β
  hasDual := W.hasDual
  geometry := W.geometry
  inversePoincare := W.inverseBundle
  evaluation := W.evaluation
  dualEndAdditivity := addBB
  polarization := lamB
  isPolarization := PolarizedAction.isogenyModelPolarization_isPolarization (P := P) (X := X) (B := B) (e := e) (W := W) (p := p)
  faithful := (RationalAlgebraAction.action_injective_iff E).mpr X.faithful
  involutionCompatible := by
    change IsInvolutionCompatible P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability W.hasDual addBB
      W.inverseBundle W.evaluation W.geometry (β).toRingHom
      (homToHom0 (pull (d).hom X.polarization))
    rw [← rationalDualPullbackHom0_homToHom0 P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      W.hasDual X.hasDual W.geometry X.geometry W.inverseBundle W.evaluation
      X.inversePoincare X.evaluation addBA]
    apply IsInvolutionCompatible.rationalDualPullback
      P.preservation P.composition P.unitCoherence P.associativity P.comparison
      P.symmetry P.stability W.hasDual X.hasDual W.geometry X.geometry
      W.inverseBundle W.evaluation X.inversePoincare X.evaluation
      addBA addBB addAA (β).toRingHom X.actionObj.action.toRingHom
      (homToHom0 (d).hom) _ (homToHom0 X.polarization)
    · exact X.involutionCompatible
    · intro r
      have he := RationalAlgebraAction.intertwines (E).hom r
      change comp0 B B X.actionObj.abelianScheme (β r) e.hom =
        comp0 B X.actionObj.abelianScheme X.actionObj.abelianScheme
          e.hom (X.actionObj.action r) at he
      change comp0 B B X.actionObj.abelianScheme (β r) (Rationalization.ofHom (d).hom) =
        comp0 B X.actionObj.abelianScheme X.actionObj.abelianScheme
          (Rationalization.ofHom (d).hom) (X.actionObj.action r)
      rw [(d).ofHom_hom]
      simpa only [map_zsmul, LinearMap.smul_apply] using
        congrArg (fun z => (d).homDenom • z) he

local notation "Y" => PolarizedAction.isogenyModel (P := P) (X := X) (B := B) (e := e) (W := W) (p := p)

/-- The polarized model comparison is the exact input inverse, with no rescaling. -/
def PolarizedAction.isogenyModelIso : X.actionObj ≅ (Y).actionObj := (E).symm

/-- The actual polarization was scaled, while the rational comparison remains exact. -/
@[simp] theorem PolarizedAction.isogenyModelIso_hom :
    RationalAlgebraAction.hom0
      (PolarizedAction.isogenyModelIso (P := P) (X := X) (B := B) (e := e) (W := W) (p := p)).hom = e.inv := rfl

@[simp] theorem PolarizedAction.isogenyModelIso_inv :
    RationalAlgebraAction.hom0
      (PolarizedAction.isogenyModelIso (P := P) (X := X) (B := B) (e := e) (W := W) (p := p)).inv = e.hom := rfl

omit [QuasiSeparatedSpace S] in
/-- The square of the selected forward denominator is positive in the rational order. -/
theorem PolarizedAction.isogenyModelMultiple_pos : 0 < ((d).homDenom : ℚ) ^ 2 :=
  sq_pos_of_ne_zero (Int.cast_ne_zero.mpr (d).homDenom_ne_zero)

/-- Pullback along the unchanged input inverse has the exact positive square multiplier. -/
theorem PolarizedAction.isogenyModelMultiple
    (additivity : PairAdditivity P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability P.square P.universality (S := S) (D := R)) :
    Multiple P.preservation P.composition P.unitCoherence P.associativity P.comparison
      P.symmetry P.stability P.square P.universality additivity X Y
      (Units.mk0 (((d).homDenom : ℚ) ^ 2)
        (pow_ne_zero _ (Int.cast_ne_zero.mpr (d).homDenom_ne_zero)))
      (PolarizedAction.isogenyModelIso (P := P) (X := X) (B := B) (e := e) (W := W) (p := p)) := by
  change rationalDualPullbackHom0 P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability X.hasDual W.hasDual
    X.geometry W.geometry X.inversePoincare X.evaluation W.inverseBundle W.evaluation
    addAB e.inv (homToHom0 (pull (d).hom X.polarization)) =
      (((d).homDenom : ℚ) ^ 2) • homToHom0 X.polarization
  rw [integralDualPullbackHom_rationalization P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    W.hasDual X.hasDual W.geometry X.geometry W.inverseBundle W.evaluation
    X.inversePoincare X.evaluation addBA e d X.polarization,
    rationalDualPullbackHom0_smul,
    rationalDualPullbackHom0_inv_hom P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability
      W.hasDual X.hasDual W.geometry X.geometry W.inverseBundle W.evaluation
      X.inversePoincare X.evaluation addBA addAB addAA,
    pow_two]

end Langlands.Shimura.PEL.PolarizedWeilLevel
