import Langlands.AbelianScheme.Tate.TwistIntegralMonodromy
import Langlands.AbelianScheme.Tate.TwistPrimeComparison

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
  (p : ℕ) [Fact p.Prime]
  [hμfin : ∀ n : ℕ, IsFinite (mu S (p ^ n)).X.hom]
  [hμet : ∀ n : ℕ, Etale (mu S (p ^ n)).X.hom]

/-- The finite geometric action preserves the prime-adic residue scalar action. -/
def primeLevelMonodromyLinear (n : ℕ) (g : FundamentalGroup s hfin) :
    Level Ω (p ^ n) →ₗ[ℤ_[p]] Level Ω (p ^ n) where
  toAddHom := (levelMonodromy s hfin (p ^ n) g).toAddMonoidHom
  map_smul' a x :=
    (levelMonodromyLinear s hfin (p ^ n) g).map_smul (PadicInt.toZModPow n a) x

/-- Lift actual geometric evaluation to the existing prime-power root limit. -/
def primeMonodromyHom (g : FundamentalGroup s hfin) :
    Integral Ω p →ₗ[ℤ_[p]] Integral Ω p :=
  lift Ω p
    (fun n => (primeLevelMonodromyLinear s hfin p
      (hμfin := hμfin) (hμet := hμet) n g).comp (evaluation Ω p n)) (by
    intro n x
    change transition Ω _ (levelMonodromy s hfin (p ^ (n + 1)) g (x.val (n + 1))) = _
    rw [← levelMonodromy_transition s hfin, x.property n]
    rfl)

@[simp] theorem evaluation_primeMonodromyHom (g : FundamentalGroup s hfin)
    (n : ℕ) (x : Integral Ω p) :
    evaluation Ω p n
        (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g x) =
      levelMonodromy s hfin (p ^ n) g (evaluation Ω p n x) := rfl

@[simp] theorem primeMonodromyHom_one (x : Integral Ω p) :
    primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) 1 x = x := by
  apply Subtype.ext
  funext n
  exact levelMonodromy_one s hfin (p ^ n) (evaluation Ω p n x)

theorem primeMonodromyHom_mul (g h : FundamentalGroup s hfin) (x : Integral Ω p) :
    primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) (g * h) x =
      primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g
        (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) h x) := by
  apply Subtype.ext
  funext n
  change evaluation Ω p n
      (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) (g * h) x) =
    evaluation Ω p n
      (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g
        (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) h x))
  rw [evaluation_primeMonodromyHom, evaluation_primeMonodromyHom,
    evaluation_primeMonodromyHom]
  exact levelMonodromy_mul s hfin (p ^ n) g h (evaluation Ω p n x)

/-- Geometric monodromy is an automorphism of the actual integral prime-adic twist. -/
def primeMonodromy (g : FundamentalGroup s hfin) : Integral Ω p ≃ₗ[ℤ_[p]] Integral Ω p :=
  { primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g with
    invFun := primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g⁻¹
    left_inv := fun x => by
      change primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g⁻¹
        (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g x) = x
      rw [← primeMonodromyHom_mul, inv_mul_cancel, primeMonodromyHom_one]
    right_inv := fun x => by
      change primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g
        (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g⁻¹ x) = x
      rw [← primeMonodromyHom_mul, mul_inv_cancel, primeMonodromyHom_one] }

@[simp] theorem evaluation_primeMonodromy (g : FundamentalGroup s hfin)
    (n : ℕ) (x : Integral Ω p) :
    evaluation Ω p n
        (primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g x) =
      levelMonodromy s hfin (p ^ n) g (evaluation Ω p n x) := rfl

/-- Bundle the actual left action as a prime-adic linear representation. -/
def primeRepresentation :
    FundamentalGroup s hfin →* (Integral Ω p ≃ₗ[ℤ_[p]] Integral Ω p) where
  toFun := primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact primeMonodromyHom_one s hfin p (hμfin := hμfin) (hμet := hμet) x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact primeMonodromyHom_mul s hfin p (hμfin := hμfin) (hμet := hμet) g h x

/-- Joint continuity uses finite evaluation and the existing product-subspace topology. -/
theorem continuous_primeMonodromy :
    Continuous (fun z : FundamentalGroup s hfin × Integral Ω p =>
      primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  change Continuous ((fun z : FundamentalGroup s hfin × Level Ω (p ^ n) =>
    levelMonodromy s hfin (p ^ n) z.1 z.2) ∘
    (fun z : FundamentalGroup s hfin × Integral Ω p =>
      (z.1, evaluation Ω p n z.2)))
  apply (continuous_levelMonodromy s hfin (p ^ n)).comp
  exact continuous_fst.prodMk ((continuous_evaluation Ω p n).comp continuous_snd)

theorem continuous_primeMonodromy_fixed (g : FundamentalGroup s hfin) :
    Continuous (primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g) := by
  change Continuous ((fun z : FundamentalGroup s hfin × Integral Ω p =>
    primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) z.1 z.2) ∘
    (fun x : Integral Ω p => (g, x)))
  apply (continuous_primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet)).comp
  exact continuous_const.prodMk continuous_id

/-- Each geometric automorphism acts by a continuous prime-adic linear equivalence. -/
def primeMonodromyContinuousLinearEquiv (g : FundamentalGroup s hfin) :
    Integral Ω p ≃L[ℤ_[p]] Integral Ω p :=
  { primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet) g with
    continuous_toFun := continuous_primeMonodromy_fixed s hfin p
      (hμfin := hμfin) (hμet := hμet) g
    continuous_invFun := continuous_primeMonodromy_fixed s hfin p
      (hμfin := hμfin) (hμet := hμet) g⁻¹ }

/-- Install the same geometric action locally when typeclass notation is useful. -/
@[instance_reducible] def primeMonodromyAction :
    DistribMulAction (FundamentalGroup s hfin) (Integral Ω p) where
  smul := fun g x => primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g x
  one_smul := primeMonodromyHom_one s hfin p (hμfin := hμfin) (hμet := hμet)
  mul_smul := primeMonodromyHom_mul s hfin p (hμfin := hμfin) (hμet := hμet)
  smul_zero g := map_zero (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g)
  smul_add g := map_add (primeMonodromyHom s hfin p (hμfin := hμfin) (hμet := hμet) g)

theorem primeMonodromyAction_continuousSMul :
    let := primeMonodromyAction s hfin p (hμfin := hμfin) (hμet := hμet)
    ContinuousSMul (FundamentalGroup s hfin) (Integral Ω p) := by
  let := primeMonodromyAction s hfin p (hμfin := hμfin) (hμet := hμet)
  exact ⟨continuous_primeMonodromy s hfin p (hμfin := hμfin) (hμet := hμet)⟩

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
  (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Extracting prime-power coordinates intertwines the two geometric actions. -/
theorem toPrime_monodromy (hP : ∀ n : ℕ, P (p ^ n))
    (g : FundamentalGroup s hfin) (x : Divisibility.Integral Ω P) :
    Divisibility.toPrime Ω P p hP
        (integralMonodromy s hfin P (hμfin := hμfin) (hμet := hμet) g x) =
      primeMonodromy s hfin p
        (hμfin := fun n => hμfin (Divisibility.primePowerIndex P p hP n))
        (hμet := fun n => hμet (Divisibility.primePowerIndex P p hP n)) g
          (Divisibility.toPrime Ω P p hP x) := rfl

omit hμfin hμet in
/-- Full prime-power extraction preserves the actual geometric monodromy. -/
theorem fullToPrime_monodromy
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) (x : Divisibility.Full Ω) :
    Divisibility.fullToPrime Ω p (fullMonodromy s hfin hfullfin hfullet g x) =
      primeMonodromy s hfin p
        (hμfin := fun n => hfullfin
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n))
        (hμet := fun n => hfullet
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n)) g
          (Divisibility.fullToPrime Ω p x) := rfl

omit hμfin hμet in
/-- The away projection is equivariant at primes coprime to the excluded modulus. -/
theorem awayToPrime_monodromy (m : ℕ) (h : Nat.Coprime p m)
    (hawayfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom)
    (hawayet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom)
    (g : FundamentalGroup s hfin) (x : Divisibility.Away Ω m) :
    Divisibility.awayToPrime Ω p m h
        (awayMonodromy s hfin m (hμfin := hawayfin) (hμet := hawayet) g x) =
      primeMonodromy s hfin p
        (hμfin := fun n => hawayfin (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n))
        (hμet := fun n => hawayet (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n)) g
          (Divisibility.awayToPrime Ω p m h x) := rfl

end Langlands.TateTwist.Geometry
