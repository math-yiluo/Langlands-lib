import Langlands.AbelianScheme.Tate.TwistIntegralTransport
import Langlands.AbelianScheme.Tate.TwistPrimeMonodromy

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
variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (p : ℕ) [Fact p.Prime]
  [hμfin : ∀ n : ℕ, IsFinite (mu S (p ^ n)).X.hom]
  [hμet : ∀ n : ℕ, Etale (mu S (p ^ n)).X.hom]

/-- The finite path map preserves the existing prime-adic residue action. -/
def primeLevelTransportLinear (n : ℕ) (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Level Ω (p ^ n) →ₗ[ℤ_[p]] Level Ω' (p ^ n) where
  toAddHom := (levelTransport (p ^ n) γ).toAddMonoidHom
  map_smul' a x := (levelTransportLinear (p ^ n) γ).map_smul (PadicInt.toZModPow n a) x

/-- Lift actual geometric path evaluation to coherent prime-power roots. -/
def primeTransportHom (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral Ω p →ₗ[ℤ_[p]] Integral Ω' p :=
  lift Ω' p
    (fun n => (primeLevelTransportLinear p
      (hμfin := hμfin) (hμet := hμet) n γ).comp (evaluation Ω p n)) (by
    intro n x
    change transition Ω' _ (levelTransport (p ^ (n + 1)) γ (x.val (n + 1))) = _
    rw [← levelTransport_transition, x.property n]
    rfl)

@[simp] theorem evaluation_primeTransportHom
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (n : ℕ) (x : Integral Ω p) :
    evaluation Ω' p n (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ x) =
      levelTransport (p ^ n) γ (evaluation Ω p n x) := rfl

@[simp] theorem primeTransportHom_refl (x : Integral Ω p) :
    primeTransportHom p (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x := by
  apply Subtype.ext
  funext n
  exact levelTransport_refl (p ^ n) (evaluation Ω p n x)

theorem primeTransportHom_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Integral Ω p) :
    primeTransportHom p (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      primeTransportHom p (hμfin := hμfin) (hμet := hμet) δ
        (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ x) := by
  apply Subtype.ext
  funext n
  change evaluation Ω'' p n
      (primeTransportHom p (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x) =
    evaluation Ω'' p n
      (primeTransportHom p (hμfin := hμfin) (hμet := hμet) δ
        (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ x))
  rw [evaluation_primeTransportHom, evaluation_primeTransportHom,
    evaluation_primeTransportHom, levelTransport_trans]

/-- Prime-adic linear transport, with inverse induced by the reverse path. -/
def primeTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral Ω p ≃ₗ[ℤ_[p]] Integral Ω' p :=
  { primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ with
    invFun := primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ.symm
    left_inv := fun x => by
      change primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ.symm
        (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ x) = x
      rw [← primeTransportHom_trans]
      simp
    right_inv := fun x => by
      change primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ
        (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ.symm x) = x
      rw [← primeTransportHom_trans]
      simp }

@[simp] theorem evaluation_primeTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (n : ℕ) (x : Integral Ω p) :
    evaluation Ω' p n (primeTransport p (hμfin := hμfin) (hμet := hμet) γ x) =
      levelTransport (p ^ n) γ (evaluation Ω p n x) := rfl

@[simp] theorem primeTransport_refl (x : Integral Ω p) :
    primeTransport p (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x :=
  primeTransportHom_refl p (hμfin := hμfin) (hμet := hμet) x

theorem primeTransport_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Integral Ω p) :
    primeTransport p (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      primeTransport p (hμfin := hμfin) (hμet := hμet) δ
        (primeTransport p (hμfin := hμfin) (hμet := hμet) γ x) :=
  primeTransportHom_trans p (hμfin := hμfin) (hμet := hμet) γ δ x

theorem primeTransport_symm (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (primeTransport p (hμfin := hμfin) (hμet := hμet) γ).symm =
      primeTransport p (hμfin := hμfin) (hμet := hμet) γ.symm := rfl

/-- Loop transport agrees with the actual prime-adic geometric root monodromy. -/
theorem primeTransport_aut (g : FundamentalGroup s hs) :
    primeTransport p (hμfin := hμfin) (hμet := hμet) g =
      primeMonodromy s hs p (hμfin := hμfin) (hμet := hμet) g := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  funext n
  exact congrArg (fun e : Level Ω (p ^ n) ≃+ Level Ω (p ^ n) => e (evaluation Ω p n x))
    (levelTransport_aut (p ^ n) g)

/-- Continuity is proved in the existing product-subspace topology. -/
theorem continuous_primeTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Continuous (primeTransport p (hμfin := hμfin) (hμet := hμet) γ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_levelTransport (p ^ n) γ).comp (continuous_evaluation Ω p n)

def primeTransportContinuousLinearEquiv (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Integral Ω p ≃L[ℤ_[p]] Integral Ω' p :=
  { primeTransport p (hμfin := hμfin) (hμet := hμet) γ with
    continuous_toFun := continuous_primeTransport p (hμfin := hμfin) (hμet := hμet) γ
    continuous_invFun := continuous_primeTransport p (hμfin := hμfin) (hμet := hμet) γ.symm }

/-- The path intertwines the endpoint geometric actions by actual path conjugation. -/
theorem primeTransport_monodromy (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Integral Ω p) :
    primeTransport p (hμfin := hμfin) (hμet := hμet) γ
        (primeMonodromy s hs p (hμfin := hμfin) (hμet := hμet) g x) =
      primeMonodromy t ht p (hμfin := hμfin) (hμet := hμet) (pathConjugation γ g)
        (primeTransport p (hμfin := hμfin) (hμet := hμet) γ x) := by
  apply Subtype.ext
  funext n
  change evaluation Ω' p n
      (primeTransport p (hμfin := hμfin) (hμet := hμet) γ
        (primeMonodromy s hs p (hμfin := hμfin) (hμet := hμet) g x)) =
    evaluation Ω' p n
      (primeMonodromy t ht p (hμfin := hμfin) (hμet := hμet) (pathConjugation γ g)
        (primeTransport p (hμfin := hμfin) (hμet := hμet) γ x))
  rw [evaluation_primeTransport, evaluation_primeMonodromy,
    evaluation_primeMonodromy, evaluation_primeTransport, levelTransport_monodromy]

theorem primeTransport_change_path (γ δ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral Ω p) :
    primeTransport p (hμfin := hμfin) (hμet := hμet) δ x =
      primeMonodromy t ht p (hμfin := hμfin) (hμet := hμet) (γ.symm ≪≫ δ)
        (primeTransport p (hμfin := hμfin) (hμet := hμet) γ x) := by
  rw [← primeTransport_aut, ← primeTransport_trans]
  simp

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u
variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Extracting the prime-power coordinates commutes with the same geometric path. -/
theorem toPrime_transport (hP : ∀ n : ℕ, P (p ^ n))
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Integral Ω P) :
    Divisibility.toPrime Ω' P p hP
        (integralTransport P (hμfin := hμfin) (hμet := hμet) γ x) =
      primeTransport p
        (hμfin := fun n => hμfin (Divisibility.primePowerIndex P p hP n))
        (hμet := fun n => hμet (Divisibility.primePowerIndex P p hP n)) γ
          (Divisibility.toPrime Ω P p hP x) := rfl

omit hμfin hμet in
theorem fullToPrime_transport
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Full Ω) :
    Divisibility.fullToPrime Ω' p (fullTransport hfullfin hfullet γ x) =
      primeTransport p
        (hμfin := fun n => hfullfin
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n))
        (hμet := fun n => hfullet
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n)) γ
          (Divisibility.fullToPrime Ω p x) := rfl

omit hμfin hμet in
/-- Away extraction commutes with transport at a retained prime. -/
theorem awayToPrime_transport (m : ℕ) (h : Nat.Coprime p m)
    (hawayfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom)
    (hawayet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Away Ω m) :
    Divisibility.awayToPrime Ω' p m h
        (awayTransport m (hμfin := hawayfin) (hμet := hawayet) γ x) =
      primeTransport p
        (hμfin := fun n => hawayfin (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n))
        (hμet := fun n => hawayet (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n)) γ
          (Divisibility.awayToPrime Ω p m h x) := rfl

end Langlands.TateTwist.Geometry
