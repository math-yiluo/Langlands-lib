import Langlands.AlgebraicGeometry.FiniteEtale.PathPushforward
import Langlands.AbelianScheme.Tate.TwistFiniteBaseChange
import Langlands.AbelianScheme.Tate.TwistSectionTransport
import Langlands.AbelianScheme.Tate.TwistRationalPrimeTransport

/-! # Base change and path transport on the actual Tate twist -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace Langlands.GroupScheme.mu
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S'} {t : Spec (.of Ω') ⟶ S'}
  {hs : ∀ Y : Cover S', Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S', Finite (Fiber t Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (n : ℕ)
  [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]
  [IsFinite (mu S' n).X.hom] [Etale (mu S' n).X.hom]

/-- The actual root-kernel comparison commutes with a path and its pushforward. -/
theorem pointsBaseChangeEquiv_pathAct
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Over.mk s ⟶ (mu S' n).X) :
    pointsBaseChangeEquiv b n (Over.mk t) (pathAct p (mu S' n).X x) =
      pathAct (pathPushforward b hsb htb p) (mu S n).X
        (pointsBaseChangeEquiv b n (Over.mk s) x) := by
  let φ := (baseChangeIso b n).inv.hom.hom.left ≫ pullback.fst (mu S n).X.hom b
  have hφ : φ ≫ (mu S n).X.hom = (mu S' n).X.hom ≫ b := by
    dsimp [φ]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact (baseChangeIso b n).inv.hom.hom.w
  apply Over.OverMorphism.ext
  rw [pointsBaseChangeEquiv_left]
  exact (pathPushforward_apply_left_of_comp b hsb htb p
    (Y := ofOver (mu S n).X) (pointsBaseChangeEquiv b n (Over.mk s) x)
    (Y' := ofOver (mu S' n).X) x φ hφ
    (pointsBaseChangeEquiv_left b n (Over.mk s) x).symm).symm

end Langlands.GroupScheme.mu

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S'} {t : Spec (.of Ω') ⟶ S'}
  {hs : ∀ Y : Cover S', Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S', Finite (Fiber t Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))

/-- Base change preserves the actual root coordinate at either endpoint. -/
theorem levelTransport_baseChange (n : ℕ)
    [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]
    [IsFinite (mu S' n).X.hom] [Etale (mu S' n).X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Level Ω n) :
    levelTransport n (pathPushforward b hsb htb p) x = levelTransport n p x := by
  obtain ⟨y, rfl⟩ := (mu.levelEquiv n s).surjective x
  conv_lhs => rw [← mu.levelEquiv_pointsBaseChangeEquiv b n s y]
  rw [levelTransport_kernel, levelTransport_kernel]
  simp only [toMul_ofMul]
  rw [← mu.pointsBaseChangeEquiv_pathAct b hsb htb n p y.toMul]
  exact mu.levelEquiv_pointsBaseChangeEquiv b n t _

section Selected
variable (P : ℕ → Prop)
  [hSfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hSet : ∀ n : Index P, Etale (mu S n.val).X.hom]
  [hTfin : ∀ n : Index P, IsFinite (mu S' n.val).X.hom]
  [hTet : ∀ n : Index P, Etale (mu S' n.val).X.hom]

/-- The selected integral root comparison holds at every retained coordinate. -/
theorem integralTransport_baseChange
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Integral Ω P) :
    integralTransport P (hμfin := hSfin) (hμet := hSet)
        (pathPushforward b hsb htb p) x =
      integralTransport P (hμfin := hTfin) (hμet := hTet) p x := by
  apply Subtype.ext
  funext n
  exact levelTransport_baseChange b hsb htb n.val p (x.val n)

/-- Rationalization preserves the same actual root comparison. -/
theorem rationalTransport_baseChange
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Divisibility.Rational Ω P) :
    rationalTransport P (hμfin := hSfin) (hμet := hSet)
        (pathPushforward b hsb htb p) x =
      rationalTransport P (hμfin := hTfin) (hμet := hTet) p x := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    rw [rationalTransport_tmul, rationalTransport_tmul,
      integralTransport_baseChange b hsb htb P]
  | add x y hx hy => simp_all

/-- Conjugating by the same affine section comparison gives the section-twist square. -/
theorem sectionRationalTransport_baseChange
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionRationalTransport P (hμfin := hSfin) (hμet := hSet)
        (pathPushforward b hsb htb p) x =
      sectionRationalTransport P (hμfin := hTfin) (hμet := hTet) p x := by
  simp only [sectionRationalTransport_apply]
  exact congrArg ((sectionRationalEquiv t P).symm)
    (rationalTransport_baseChange b hsb htb P p (sectionRationalEquiv s P x))

/-- The common finite-adelic scalar identification retains that same section-twist square. -/
theorem sectionFiniteAdeleTransport_baseChange
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionFiniteAdeleTransport P (hμfin := hSfin) (hμet := hSet) h
        (pathPushforward b hsb htb p) x =
      sectionFiniteAdeleTransport P (hμfin := hTfin) (hμet := hTet) h p x :=
  sectionRationalTransport_baseChange b hsb htb P p x

end Selected

section Away
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  [hSfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hSet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  [hTfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S' n.val).X.hom]
  [hTet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S' n.val).X.hom]

/-- The coupled away scalar structure preserves the same actual section-twist comparison. -/
theorem sectionPrimeToFiniteAdeleTransport_baseChange
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m) :
    sectionPrimeToFiniteAdeleTransport hAway (hμfin := hSfin) (hμet := hSet)
        (pathPushforward b hsb htb p) x =
      sectionPrimeToFiniteAdeleTransport hAway (hμfin := hTfin) (hμet := hTet) p x :=
  sectionRationalTransport_baseChange b hsb htb (fun n => Nat.Coprime n m) p x

end Away

section Prime
variable (ℓ : ℕ) [Fact ℓ.Prime]
  [hSfin : ∀ n : ℕ, IsFinite (mu S (ℓ ^ n)).X.hom]
  [hSet : ∀ n : ℕ, Etale (mu S (ℓ ^ n)).X.hom]
  [hTfin : ∀ n : ℕ, IsFinite (mu S' (ℓ ^ n)).X.hom]
  [hTet : ∀ n : ℕ, Etale (mu S' (ℓ ^ n)).X.hom]

/-- The prime-adic integral root transport is also unchanged by actual base change. -/
theorem primeTransport_baseChange
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Integral Ω ℓ) :
    primeTransport ℓ (hμfin := hSfin) (hμet := hSet)
        (pathPushforward b hsb htb p) x =
      primeTransport ℓ (hμfin := hTfin) (hμet := hTet) p x := by
  apply Subtype.ext
  funext n
  exact levelTransport_baseChange b hsb htb (ℓ ^ n) p (x.val n)

/-- Scalar extension over the prime-adic integers preserves the root comparison. -/
theorem rationalPrimeTransport_baseChange
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (x : Rational Ω ℓ) :
    rationalPrimeTransport ℓ (hμfin := hSfin) (hμet := hSet)
        (pathPushforward b hsb htb p) x =
      rationalPrimeTransport ℓ (hμfin := hTfin) (hμet := hTet) p x := by
  have heq :
      primeTransportHom ℓ (hμfin := hSfin) (hμet := hSet) (pathPushforward b hsb htb p) =
        primeTransportHom ℓ (hμfin := hTfin) (hμet := hTet) p :=
    LinearMap.ext (primeTransport_baseChange b hsb htb ℓ p)
  exact LinearMap.congr_fun
    (congrArg (fun f : Integral Ω ℓ →ₗ[ℤ_[ℓ]] Integral Ω' ℓ => f.baseChange ℚ_[ℓ]) heq) x

end Prime
end Langlands.TateTwist.Geometry
