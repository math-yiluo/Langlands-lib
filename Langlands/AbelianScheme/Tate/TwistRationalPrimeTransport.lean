import Langlands.AbelianScheme.Tate.TwistPrimeTransport
import Langlands.AbelianScheme.Tate.TwistRationalTransport
import Langlands.AbelianScheme.Tate.TwistRationalPrimeMonodromy

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

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

/-- Scalar extension of actual prime-adic root path transport. -/
def rationalPrimeTransportMap (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational Ω p →ₗ[ℚ_[p]] Rational Ω' p :=
  (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ).baseChange ℚ_[p]

@[simp] theorem rationalPrimeTransportMap_tmul
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (q : ℚ_[p]) (x : Integral Ω p) :
    rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ (q ⊗ₜ[ℤ_[p]] x) =
      q ⊗ₜ[ℤ_[p]] primeTransport p (hμfin := hμfin) (hμet := hμet) γ x := rfl

@[simp] theorem rationalPrimeTransportMap_refl (x : Rational Ω p) :
    rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x := by
  have heq : primeTransportHom p (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) = LinearMap.id :=
    LinearMap.ext (primeTransportHom_refl p (hμfin := hμfin) (hμet := hμet))
  have hbase := congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω p => f.baseChange ℚ_[p]) heq
  rw [LinearMap.baseChange_id] at hbase
  exact LinearMap.congr_fun hbase x

theorem rationalPrimeTransportMap_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Rational Ω p) :
    rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) δ
        (rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ x) := by
  have heq : primeTransportHom p (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) =
      (primeTransportHom p (hμfin := hμfin) (hμet := hμet) δ).comp
        (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ) :=
    LinearMap.ext (primeTransportHom_trans p (hμfin := hμfin) (hμet := hμet) γ δ)
  have hbase := congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω'' p => f.baseChange ℚ_[p]) heq
  rw [LinearMap.baseChange_comp] at hbase
  exact LinearMap.congr_fun hbase x

/-- Rational prime-adic root transport, with inverse from the reverse path. -/
def rationalPrimeTransport (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational Ω p ≃ₗ[ℚ_[p]] Rational Ω' p :=
  { rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ with
    invFun := rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ.symm
    left_inv := fun x => by
      change rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ.symm
        (rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ x) = x
      rw [← rationalPrimeTransportMap_trans]
      simp
    right_inv := fun x => by
      change rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ
        (rationalPrimeTransportMap p (hμfin := hμfin) (hμet := hμet) γ.symm x) = x
      rw [← rationalPrimeTransportMap_trans]
      simp }

@[simp] theorem rationalPrimeTransport_tmul
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (q : ℚ_[p]) (x : Integral Ω p) :
    rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ (q ⊗ₜ[ℤ_[p]] x) =
      q ⊗ₜ[ℤ_[p]] primeTransport p (hμfin := hμfin) (hμet := hμet) γ x := rfl

@[simp] theorem rationalPrimeTransport_refl (x : Rational Ω p) :
    rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x :=
  rationalPrimeTransportMap_refl p (hμfin := hμfin) (hμet := hμet) x

theorem rationalPrimeTransport_trans (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (δ : fiberFunctor t ht ≅ fiberFunctor r hr) (x : Rational Ω p) :
    rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) (γ ≪≫ δ) x =
      rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) δ
        (rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ x) :=
  rationalPrimeTransportMap_trans p (hμfin := hμfin) (hμet := hμet) γ δ x

theorem rationalPrimeTransport_symm (γ : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ).symm =
      rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ.symm := rfl

/-- Loop transport recovers the existing rational prime-adic geometric action. -/
theorem rationalPrimeTransport_aut (g : FundamentalGroup s hs) :
    rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) g =
      rationalPrimeMonodromy s hs p (hμfin := hμfin) (hμet := hμet) g := by
  have heq : primeTransportHom p (hμfin := hμfin) (hμet := hμet) g =
      primeMonodromyHom s hs p (hμfin := hμfin) (hμet := hμet) g :=
    congrArg LinearEquiv.toLinearMap
      (primeTransport_aut p (hμfin := hμfin) (hμet := hμet) g)
  apply LinearEquiv.toLinearMap_injective
  exact congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω p => f.baseChange ℚ_[p]) heq

/-- The canonical integral-to-rational map commutes with transport. -/
theorem primeToRational_transport (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral Ω p) :
    TateTwist.toRational Ω' p
        (primeTransport p (hμfin := hμfin) (hμet := hμet) γ x) =
      rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ
        (TateTwist.toRational Ω p x) := rfl

/-- Transport intertwines the endpoint actions by the actual geometric conjugation. -/
theorem rationalPrimeTransport_monodromy (γ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (g : FundamentalGroup s hs) (x : Rational Ω p) :
    rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ
        (rationalPrimeMonodromy s hs p (hμfin := hμfin) (hμet := hμet) g x) =
      rationalPrimeMonodromy t ht p (hμfin := hμfin) (hμet := hμet) (pathConjugation γ g)
        (rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ x) := by
  have heq :
      (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ).comp
        (primeMonodromyHom s hs p (hμfin := hμfin) (hμet := hμet) g) =
      (primeMonodromyHom t ht p (hμfin := hμfin) (hμet := hμet)
        (pathConjugation γ g)).comp
        (primeTransportHom p (hμfin := hμfin) (hμet := hμet) γ) :=
    LinearMap.ext (primeTransport_monodromy p (hμfin := hμfin) (hμet := hμet) γ g)
  have hbase := congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω' p => f.baseChange ℚ_[p]) heq
  simp only [LinearMap.baseChange_comp] at hbase
  exact LinearMap.congr_fun hbase x

/-- The difference of two paths is measured by target-point monodromy. -/
theorem rationalPrimeTransport_change_path (γ δ : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational Ω p) :
    rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) δ x =
      rationalPrimeMonodromy t ht p (hμfin := hμfin) (hμet := hμet) (γ.symm ≪≫ δ)
        (rationalPrimeTransport p (hμfin := hμfin) (hμet := hμet) γ x) := by
  rw [← rationalPrimeTransport_aut, ← rationalPrimeTransport_trans]
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

/-- Rational extraction commutes with the same selected and prime-adic path. -/
theorem rationalToPrime_transport (hP : ∀ n : ℕ, P (p ^ n))
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Rational Ω P) :
    Divisibility.rationalToPrime Ω' P p hP
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) =
      rationalPrimeTransport p
        (hμfin := fun n => hμfin (Divisibility.primePowerIndex P p hP n))
        (hμet := fun n => hμet (Divisibility.primePowerIndex P p hP n)) γ
          (Divisibility.rationalToPrime Ω P p hP x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    rw [rationalTransport_tmul, Divisibility.rationalToPrime_tmul,
      Divisibility.rationalToPrime_tmul]
    exact congrArg (fun y : Integral Ω' p => (q : ℚ_[p]) ⊗ₜ[ℤ_[p]] y)
      (toPrime_transport P p (hμfin := hμfin) (hμet := hμet) hP γ x)
  | add x y hx hy => simp_all

/-- The existing semilinear projection has the same path compatibility. -/
theorem rationalToPrimeSemilinear_transport (hP : ∀ n : ℕ, P (p ^ n))
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Rational Ω P) :
    Divisibility.rationalToPrimeSemilinear Ω' P p hP
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) γ x) =
      rationalPrimeTransport p
        (hμfin := fun n => hμfin (Divisibility.primePowerIndex P p hP n))
        (hμet := fun n => hμet (Divisibility.primePowerIndex P p hP n)) γ
          (Divisibility.rationalToPrimeSemilinear Ω P p hP x) :=
  rationalToPrime_transport P p (hμfin := hμfin) (hμet := hμet) hP γ x

omit hμfin hμet in
/-- Full rational extraction commutes with geometric path transport. -/
theorem rationalFullToPrime_transport
    (hfullfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom)
    (hfullet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.RationalFull Ω) :
    Divisibility.rationalFullToPrime Ω' p
        (rationalFullTransport hfullfin hfullet γ x) =
      rationalPrimeTransport p
        (hμfin := fun n => hfullfin
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n))
        (hμet := fun n => hfullet
          (Divisibility.primePowerIndex (fun _ => True) p (fun _ => trivial) n)) γ
          (Divisibility.rationalFullToPrime Ω p x) :=
  rationalToPrime_transport (fun _ => True) p
    (hμfin := hfullfin) (hμet := hfullet) (fun _ => trivial) γ x

omit hμfin hμet in
/-- Rational away extraction commutes with transport at a retained prime. -/
theorem rationalAwayToPrime_transport (m : ℕ) (h : Nat.Coprime p m)
    (hawayfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom)
    (hawayet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.RationalAway Ω m) :
    Divisibility.rationalAwayToPrime Ω' p m h
        (rationalAwayTransport m (hμfin := hawayfin) (hμet := hawayet) γ x) =
      rationalPrimeTransport p
        (hμfin := fun n => hawayfin (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n))
        (hμet := fun n => hawayet (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n)) γ
          (Divisibility.rationalAwayToPrime Ω p m h x) :=
  rationalToPrime_transport (fun n => Nat.Coprime n m) p
    (hμfin := hawayfin) (hμet := hawayet) (fun n => h.pow_left n) γ x

omit hμfin hμet in
/-- The away semilinear projection retains the same path compatibility. -/
theorem rationalAwayToPrimeSemilinear_transport (m : ℕ) (h : Nat.Coprime p m)
    (hawayfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom)
    (hawayet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom)
    (γ : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.RationalAway Ω m) :
    Divisibility.rationalAwayToPrimeSemilinear Ω' p m h
        (rationalAwayTransport m (hμfin := hawayfin) (hμet := hawayet) γ x) =
      rationalPrimeTransport p
        (hμfin := fun n => hawayfin (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n))
        (hμet := fun n => hawayet (Divisibility.primePowerIndex
          (fun n => Nat.Coprime n m) p (fun n => h.pow_left n) n)) γ
          (Divisibility.rationalAwayToPrimeSemilinear Ω p m h x) :=
  rationalAwayToPrime_transport p m h hawayfin hawayet γ x

end Langlands.TateTwist.Geometry
