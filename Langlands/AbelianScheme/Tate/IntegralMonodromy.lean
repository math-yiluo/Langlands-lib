import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.Tate.Scalars
import Langlands.AbelianScheme.Tate.Topology

/-! # Actual geometric monodromy on integral Tate limits -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))

/-- Evaluate the actual geometric automorphism at every selected torsion level. -/
def integralMonodromyHom (g : FundamentalGroup s hfin) :
    Integral A (Over.mk s) P →+ Integral A (Over.mk s) P :=
  lift A (Over.mk s) P
    (fun n => (levelMonodromy s hfin htor A n.val n.property.1 (hu n) g).toAddMonoidHom.comp
      (evaluation A (Over.mk s) P n)) (by
    intro n m h x
    change transition A (Over.mk s) h
      (levelMonodromy s hfin htor A m.val m.property.1 (hu m) g (x.val m)) = _
    rw [← levelMonodromy_transition s hfin htor A n.val n.property.1 (hu n)
      m.val m.property.1 (hu m) h, x.property n m h]
    rfl)

@[simp] theorem evaluation_integralMonodromyHom (g : FundamentalGroup s hfin)
    (n : Index P) (x : Integral A (Over.mk s) P) :
    evaluation A (Over.mk s) P n (integralMonodromyHom s hfin htor A P hu g x) =
      levelMonodromy s hfin htor A n.val n.property.1 (hu n) g
        (evaluation A (Over.mk s) P n x) := rfl

@[simp] theorem integralMonodromyHom_one (x : Integral A (Over.mk s) P) :
    integralMonodromyHom s hfin htor A P hu 1 x = x := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_one s hfin htor A n.val n.property.1 (hu n) (x.val n)

theorem integralMonodromyHom_mul (g h : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) P) :
    integralMonodromyHom s hfin htor A P hu (g * h) x =
      integralMonodromyHom s hfin htor A P hu g
        (integralMonodromyHom s hfin htor A P hu h x) := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_mul s hfin htor A n.val n.property.1 (hu n) g h (x.val n)

/-- The actual action as additive automorphisms; inverse is evaluation at `g⁻¹`. -/
def integralMonodromy (g : FundamentalGroup s hfin) : AddAut (Integral A (Over.mk s) P) :=
  { integralMonodromyHom s hfin htor A P hu g with
    invFun := integralMonodromyHom s hfin htor A P hu g⁻¹
    left_inv := fun x => by
      change integralMonodromyHom s hfin htor A P hu g⁻¹
        (integralMonodromyHom s hfin htor A P hu g x) = x
      rw [← integralMonodromyHom_mul, inv_mul_cancel, integralMonodromyHom_one]
    right_inv := fun x => by
      change integralMonodromyHom s hfin htor A P hu g
        (integralMonodromyHom s hfin htor A P hu g⁻¹ x) = x
      rw [← integralMonodromyHom_mul, mul_inv_cancel, integralMonodromyHom_one] }

@[simp] theorem integralMonodromy_apply (g : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) P) :
    integralMonodromy s hfin htor A P hu g x =
      integralMonodromyHom s hfin htor A P hu g x := rfl

/-- Locally installable geometric action on the existing integral Tate carrier. -/
@[instance_reducible] def integralMonodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Integral A (Over.mk s) P) where
  smul := fun g x => integralMonodromyHom s hfin htor A P hu g x
  one_smul := integralMonodromyHom_one s hfin htor A P hu
  mul_smul := integralMonodromyHom_mul s hfin htor A P hu
  smul_zero g := map_zero (integralMonodromyHom s hfin htor A P hu g)
  smul_add g := _root_.map_add (integralMonodromyHom s hfin htor A P hu g)

set_option maxHeartbeats 800000 in
/-- Each transformed coordinate is jointly continuous. -/
theorem continuous_integralMonodromy_coordinate (n : Index P) :
    Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) P =>
      levelMonodromy s hfin htor A n.val n.property.1 (hu n) z.1
        (evaluation A (Over.mk s) P n z.2)) := by
  have he : Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) P =>
      (z.1, evaluation A (Over.mk s) P n z.2)) :=
    continuous_fst.prodMk ((continuous_evaluation A (Over.mk s) P n).comp continuous_snd)
  exact Continuous.comp
    (f := fun z : FundamentalGroup s hfin × Integral A (Over.mk s) P =>
      (z.1, evaluation A (Over.mk s) P n z.2))
    (continuous_levelMonodromy s hfin htor A n.val n.property.1 (hu n)) he

set_option maxHeartbeats 800000 in
/-- Joint continuity for the additive homomorphism follows from its coordinates. -/
theorem continuous_integralMonodromyHom :
    Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) P =>
      integralMonodromyHom s hfin htor A P hu z.1 z.2) := by
  apply (GroupScheme.Tate.continuous_iff_evaluation A.toGrp (Over.mk s) P
    (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) P =>
      integralMonodromyHom s hfin htor A P hu z.1 z.2)).mpr
  intro n
  exact (continuous_integralMonodromy_coordinate s hfin htor A P hu n).congr
    (fun z => (evaluation_integralMonodromyHom s hfin htor A P hu z.1 n z.2).symm)

/-- Joint continuity of the actual action with the existing Tate topology. -/
theorem continuous_integralMonodromy :
    Continuous (fun z : FundamentalGroup s hfin × Integral A (Over.mk s) P =>
      integralMonodromy s hfin htor A P hu z.1 z.2) :=
  (continuous_integralMonodromyHom s hfin htor A P hu).congr
    (fun z => (integralMonodromy_apply s hfin htor A P hu z.1 z.2).symm)

theorem integralMonodromyAction_continuousSMul :
    let := integralMonodromyAction s hfin htor A P hu
    ContinuousSMul (FundamentalGroup s hfin) (Integral A (Over.mk s) P) := by
  let := integralMonodromyAction s hfin htor A P hu
  exact ⟨continuous_integralMonodromy s hfin htor A P hu⟩

/-- Monodromy commutes with the existing full profinite-integer action. -/
theorem integralMonodromy_full_smul (g : FundamentalGroup s hfin)
    (a : Global.ProfiniteIntegerRing) (x : Integral A (Over.mk s) P) :
    integralMonodromy s hfin htor A P hu g (a • x) =
      a • integralMonodromy s hfin htor A P hu g x := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_zmod_smul s hfin htor A n.val n.property.1 (hu n) g
    (GroupScheme.Tate.fullReduction P n a) (x.val n)

/-- The same geometric automorphism bundled over the full residue scalar ring. -/
def integralMonodromyLinearEquiv (g : FundamentalGroup s hfin) :
    Integral A (Over.mk s) P ≃ₗ[Global.ProfiniteIntegerRing] Integral A (Over.mk s) P :=
  { integralMonodromy s hfin htor A P hu g with
    map_smul' := integralMonodromy_full_smul s hfin htor A P hu g }

include hfin htor hu in
/-- The selected Tate limit is compact because its actual finite levels are finite. -/
theorem integralMonodromy_compactSpace : CompactSpace (Integral A (Over.mk s) P) := by
  let : ∀ n : Index P, Finite (Level A (Over.mk s) n.val) := fun n =>
    level_finite s hfin htor A n.val n.property.1 (hu n)
  infer_instance

/-- Bundle the existing Tate topology using finiteness derived from the geometric hypotheses. -/
def geometricProfiniteTate : Profinite := by
  letI := integralMonodromy_compactSpace s hfin htor A P hu
  exact Profinite.of (Integral A (Over.mk s) P)

variable {A} {B : AbelianScheme S}

/-- The published integral map of an actual homomorphism is geometrically equivariant. -/
theorem integralMonodromy_map (f : A ⟶ B) (g : FundamentalGroup s hfin)
    (x : Integral A (Over.mk s) P) :
    integralMonodromy s hfin htor B P hu g (map (Over.mk s) P f x) =
      map (Over.mk s) P f (integralMonodromy s hfin htor A P hu g x) := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_map s hfin htor A n.val n.property.1 (hu n) f g (x.val n)

end Langlands.AbelianScheme.Tate

namespace Langlands.AbelianScheme.Tate

universe u
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)

/-- Full geometric monodromy, requiring invertibility of every positive torsion order. -/
abbrev fullMonodromy (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) : AddAut (Full A (Over.mk s)) :=
  integralMonodromy s hfin htor A (fun _ => True) hu g

/-- Away monodromy requires invertibility only of the retained positive orders. -/
abbrev awayMonodromy (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) : AddAut (Away A (Over.mk s) m) :=
  integralMonodromy s hfin htor A (fun n => Nat.Coprime n m) hu g

/-- The away action preserves the existing away residue scalar multiplication. -/
theorem awayMonodromy_smul (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (a : Global.PrimeToProfiniteIntegerRing m)
    (x : Away A (Over.mk s) m) :
    awayMonodromy s hfin htor A m hu g (a • x) =
      a • awayMonodromy s hfin htor A m hu g x := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_zmod_smul s hfin htor A n.val n.property.1 (hu n) g
    (GroupScheme.Tate.awayReduction m n a) (x.val n)

/-- Away monodromy as a linear equivalence over the actual away residue ring. -/
def awayMonodromyLinearEquiv (m : ℕ)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) :
    Away A (Over.mk s) m ≃ₗ[Global.PrimeToProfiniteIntegerRing m] Away A (Over.mk s) m :=
  { awayMonodromy s hfin htor A m hu g with
    map_smul' := awayMonodromy_smul s hfin htor A m hu g }

/-- Full-to-away restriction intertwines the actual geometric actions. -/
theorem restrictAway_monodromy (m : ℕ)
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (g : FundamentalGroup s hfin) (x : Full A (Over.mk s)) :
    restrictAway A (Over.mk s) m (fullMonodromy s hfin htor A hu g x) =
      awayMonodromy s hfin htor A m
        (fun n => hu ⟨n.val, n.property.1, trivial⟩) g
          (restrictAway A (Over.mk s) m x) := rfl

end Langlands.AbelianScheme.Tate
