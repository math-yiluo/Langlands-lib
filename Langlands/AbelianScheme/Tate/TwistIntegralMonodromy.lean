import Langlands.AbelianScheme.Tate.TwistFiniteMonodromy
import Langlands.AbelianScheme.Tate.TwistDivisibility
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (P : ℕ → Prop)
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Evaluate the actual geometric action at every selected roots-of-unity level. -/
def integralMonodromyHom (g : FundamentalGroup s hfin) :
    Divisibility.Integral Ω P →+ Divisibility.Integral Ω P :=
  Divisibility.lift Ω P
    (fun n => (levelMonodromy s hfin n.val g).toAddMonoidHom.comp
      (Divisibility.evaluation Ω P n)) (by
    intro n m h x
    change transition Ω h (levelMonodromy s hfin m.val g (x.val m)) = _
    rw [← levelMonodromy_transition s hfin h, x.property n m h]
    rfl)

@[simp] theorem evaluation_integralMonodromyHom (g : FundamentalGroup s hfin)
    (n : Index P) (x : Divisibility.Integral Ω P) :
    Divisibility.evaluation Ω P n (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g x) =
      levelMonodromy s hfin n.val g (Divisibility.evaluation Ω P n x) := rfl

@[simp] theorem integralMonodromyHom_one (x : Divisibility.Integral Ω P) :
    integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) 1 x = x := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_one s hfin n.val (x.val n)

theorem integralMonodromyHom_mul (g h : FundamentalGroup s hfin)
    (x : Divisibility.Integral Ω P) :
    integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) (g * h) x =
      integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g
        (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) h x) := by
  apply Subtype.ext
  funext n
  change Divisibility.evaluation Ω P n
      (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) (g * h) x) =
    Divisibility.evaluation Ω P n
      (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g
        (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) h x))
  rw [evaluation_integralMonodromyHom, evaluation_integralMonodromyHom,
    evaluation_integralMonodromyHom]
  exact levelMonodromy_mul s hfin n.val g h (Divisibility.evaluation Ω P n x)

/-- The inverse is the same coordinate construction evaluated at the inverse group element. -/
def integralMonodromy (g : FundamentalGroup s hfin) :
    AddAut (Divisibility.Integral Ω P) :=
  { integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g with
    invFun := integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g⁻¹
    left_inv := fun x => by
      change integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g⁻¹
        (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g x) = x
      rw [← integralMonodromyHom_mul, inv_mul_cancel, integralMonodromyHom_one]
    right_inv := fun x => by
      change integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g
        (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g⁻¹ x) = x
      rw [← integralMonodromyHom_mul, mul_inv_cancel, integralMonodromyHom_one] }

@[simp] theorem evaluation_integralMonodromy (g : FundamentalGroup s hfin)
    (n : Index P) (x : Divisibility.Integral Ω P) :
    Divisibility.evaluation Ω P n (integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) =
      levelMonodromy s hfin n.val g (Divisibility.evaluation Ω P n x) := rfl

/-- Joint continuity follows from the finite-level action and the product-subspace topology. -/
theorem continuous_integralMonodromy :
    Continuous (fun z : FundamentalGroup s hfin × Divisibility.Integral Ω P =>
      integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  change Continuous ((fun z : FundamentalGroup s hfin × Level Ω n.val =>
    levelMonodromy s hfin n.val z.1 z.2) ∘
    (fun z : FundamentalGroup s hfin × Divisibility.Integral Ω P =>
      (z.1, Divisibility.evaluation Ω P n z.2)))
  apply (continuous_levelMonodromy s hfin n.val).comp
  exact continuous_fst.prodMk ((Divisibility.continuous_evaluation Ω P n).comp continuous_snd)

/-- This locally installable action uses the existing additive group of coherent roots. -/
@[instance_reducible] def integralMonodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Divisibility.Integral Ω P) where
  smul := fun g x => integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g x
  one_smul := integralMonodromyHom_one s hfin P (hμfin := hμfin) (hμet := hμet)
  mul_smul := integralMonodromyHom_mul s hfin P (hμfin := hμfin) (hμet := hμet)
  smul_zero g := map_zero (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g)
  smul_add g := map_add (integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g)

theorem integralMonodromyAction_continuousSMul :
    let := integralMonodromyAction s hfin P (hμfin := hμfin) (hμet := hμet)
    ContinuousSMul (FundamentalGroup s hfin) (Divisibility.Integral Ω P) := by
  let := integralMonodromyAction s hfin P (hμfin := hμfin) (hμet := hμet)
  exact ⟨continuous_integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet)⟩

/-- The geometric action preserves the existing full residue scalar action. -/
theorem integralMonodromy_full_smul (g : FundamentalGroup s hfin)
    (a : Global.ProfiniteIntegerRing) (x : Divisibility.Integral Ω P) :
    integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g (a • x) =
      a • integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x := by
  apply Subtype.ext
  funext n
  exact (levelMonodromyLinear s hfin n.val g).map_smul
    (GroupScheme.Tate.fullReduction P n a) (x.val n)

/-- The actual action is linear over the full profinite-integer ring for any selected system. -/
def integralMonodromyLinearEquiv (g : FundamentalGroup s hfin) :
    Divisibility.Integral Ω P ≃ₗ[Global.ProfiniteIntegerRing] Divisibility.Integral Ω P :=
  { integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g with
    map_smul' := integralMonodromy_full_smul s hfin P (hμfin := hμfin) (hμet := hμet) g }

/-- Bundle the left-action laws as a representation on the actual twist. -/
def integralRepresentation :
    FundamentalGroup s hfin →*
      (Divisibility.Integral Ω P ≃ₗ[Global.ProfiniteIntegerRing] Divisibility.Integral Ω P) where
  toFun := integralMonodromyLinearEquiv s hfin P (hμfin := hμfin) (hμet := hμet)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_one s hfin P (hμfin := hμfin) (hμet := hμet) x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_mul s hfin P (hμfin := hμfin) (hμet := hμet) g h x

/-- Continuity with a fixed geometric automorphism. -/
theorem continuous_integralMonodromy_fixed (g : FundamentalGroup s hfin) :
    Continuous (integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g) := by
  change Continuous ((fun z : FundamentalGroup s hfin × Divisibility.Integral Ω P =>
    integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) z.1 z.2) ∘
    (fun x : Divisibility.Integral Ω P => (g, x)))
  apply (continuous_integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet)).comp
  exact continuous_const.prodMk continuous_id

/-- Each geometric automorphism is a continuous linear equivalence of the existing limit. -/
def integralMonodromyContinuousLinearEquiv (g : FundamentalGroup s hfin) :
    Divisibility.Integral Ω P ≃L[Global.ProfiniteIntegerRing] Divisibility.Integral Ω P :=
  { integralMonodromyLinearEquiv s hfin P (hμfin := hμfin) (hμet := hμet) g with
    continuous_toFun := continuous_integralMonodromy_fixed s hfin P
      (hμfin := hμfin) (hμet := hμet) g
    continuous_invFun := continuous_integralMonodromy_fixed s hfin P
      (hμfin := hμfin) (hμet := hμet) g⁻¹ }

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))

/-- Full monodromy uses finite étaleness at every positive order. -/
abbrev fullMonodromy
    (hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) : AddAut (Divisibility.Full Ω) :=
  integralMonodromy s hfin (fun _ => True) (hμfin := hμfin) (hμet := hμet) g

variable (p : ℕ)
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n p), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n p), Etale (mu S n.val).X.hom]

/-- Away monodromy only uses finite étaleness at positive orders coprime to the modulus. -/
abbrev awayMonodromy (g : FundamentalGroup s hfin) : AddAut (Divisibility.Away Ω p) :=
  integralMonodromy s hfin (fun n => Nat.Coprime n p) (hμfin := hμfin) (hμet := hμet) g

theorem awayMonodromy_smul (g : FundamentalGroup s hfin)
    (a : Global.PrimeToProfiniteIntegerRing p) (x : Divisibility.Away Ω p) :
    awayMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g (a • x) =
      a • awayMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g x := by
  apply Subtype.ext
  funext n
  exact (levelMonodromyLinear s hfin n.val g).map_smul
    (GroupScheme.Tate.awayReduction p n a) (x.val n)

/-- The away action preserves scalars from the actual prime-to-p residue ring. -/
def awayMonodromyLinearEquiv (g : FundamentalGroup s hfin) :
    Divisibility.Away Ω p ≃ₗ[Global.PrimeToProfiniteIntegerRing p] Divisibility.Away Ω p :=
  { awayMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g with
    map_smul' := awayMonodromy_smul s hfin p (hμfin := hμfin) (hμet := hμet) g }

def awayRepresentation :
    FundamentalGroup s hfin →*
      (Divisibility.Away Ω p ≃ₗ[Global.PrimeToProfiniteIntegerRing p] Divisibility.Away Ω p) where
  toFun := awayMonodromyLinearEquiv s hfin p (hμfin := hμfin) (hμet := hμet)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_one s hfin _ (hμfin := hμfin) (hμet := hμet) x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact integralMonodromyHom_mul s hfin _ (hμfin := hμfin) (hμet := hμet) g h x

/-- The away representation consists of continuous linear equivalences. -/
def awayMonodromyContinuousLinearEquiv (g : FundamentalGroup s hfin) :
    Divisibility.Away Ω p ≃L[Global.PrimeToProfiniteIntegerRing p] Divisibility.Away Ω p :=
  { awayMonodromyLinearEquiv s hfin p (hμfin := hμfin) (hμet := hμet) g with
    continuous_toFun := continuous_integralMonodromy_fixed s hfin _
      (hμfin := hμfin) (hμet := hμet) g
    continuous_invFun := continuous_integralMonodromy_fixed s hfin _
      (hμfin := hμfin) (hμet := hμet) g⁻¹ }

variable (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
  (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)

omit hμfin hμet in
/-- Restriction intertwines full monodromy with the action from the same geometric automorphism. -/
theorem restrictAway_monodromy (g : FundamentalGroup s hfin) (x : Divisibility.Full Ω) :
    Divisibility.restrictAway Ω p (fullMonodromy s hfin hfullfin hfullet g x) =
      awayMonodromy s hfin p
        (hμfin := fun n => hfullfin ⟨n.val, n.property.1, trivial⟩)
        (hμet := fun n => hfullet ⟨n.val, n.property.1, trivial⟩) g
          (Divisibility.restrictAway Ω p x) := rfl

end Langlands.TateTwist.Geometry
