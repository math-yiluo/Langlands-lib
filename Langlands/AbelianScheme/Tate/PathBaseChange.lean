import Langlands.AlgebraicGeometry.FiniteEtale.PathPushforward
import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeProof
import Langlands.AbelianScheme.Tate.RationalTransport
import Langlands.AbelianScheme.Tate.TwistPathBaseChange

/-! # Base change and path transport on actual Tate modules -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace Langlands.GroupScheme
open Langlands.AlgebraicGeometry.FiniteEtale

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S'} {t : Spec (.of Ω') ⟶ S'}
  {hs : ∀ Y : Cover S', Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S', Finite (Fiber t Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))

/-- Pullback adjunction on actual finite étale group points commutes with path transport. -/
theorem baseChangePointsEquiv_pathAct (G : Grp (Over S))
    [IsFinite G.X.hom] [Etale G.X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Over.mk s ⟶ ((Over.pullback b).mapGrp.obj G).X) :
    baseChangePointsEquiv b G (Over.mk t)
        (pathAct p ((Over.pullback b).mapGrp.obj G).X x) =
      pathAct (pathPushforward b hsb htb p) G.X
        (baseChangePointsEquiv b G (Over.mk s) x) := by
  apply Over.OverMorphism.ext
  exact (pathPushforward_apply_left_of_comp b hsb htb p
    (Y := ofOver G.X) (baseChangePointsEquiv b G (Over.mk s) x)
    (Y' := ofOver ((Over.pullback b).mapGrp.obj G).X) x
    (pullback.fst G.X.hom b) pullback.condition rfl).symm

namespace Tate

variable (G : Grp (Over S)) [IsCommMonObj G.X]

/-- The actual torsion base-change comparison commutes with path transport and pushed paths. -/
theorem levelBaseChange_finiteLevelTransport (n : ℕ)
    [IsFinite (kernel (multiplication G n)).X.hom]
    [Etale (kernel (multiplication G n)).X.hom]
    [IsFinite (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom]
    [Etale (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom]
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (z : Level ((Over.pullback b).mapGrp.obj G) (Over.mk s) n) :
    levelBaseChange b G (Over.mk t) n
        (finiteLevelTransport ((Over.pullback b).mapGrp.obj G) n p z) =
      finiteLevelTransport G n (pathPushforward b hsb htb p)
        (levelBaseChange b G (Over.mk s) n z) := by
  let : IsFinite (torsion G (n : ℤ)).X.hom :=
    inferInstanceAs (IsFinite (kernel (multiplication G n)).X.hom)
  let : Etale (torsion G (n : ℤ)).X.hom :=
    inferInstanceAs (Etale (kernel (multiplication G n)).X.hom)
  let : IsFinite (torsion ((Over.pullback b).mapGrp.obj G) (n : ℤ)).X.hom :=
    inferInstanceAs (IsFinite (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom)
  let : Etale (torsion ((Over.pullback b).mapGrp.obj G) (n : ℤ)).X.hom :=
    inferInstanceAs (Etale (kernel (multiplication ((Over.pullback b).mapGrp.obj G) n)).X.hom)
  obtain ⟨y, rfl⟩ := (kernelLevelEquiv ((Over.pullback b).mapGrp.obj G)
    (Over.mk s) n).surjective z
  let e := torsionBaseChangeIso b G (n : ℤ)
  let x := y.toMul ≫ e.inv.hom.hom
  have hy : y = Additive.ofMul (x ≫ e.hom.hom.hom) := by
    change y.toMul = (y.toMul ≫ e.inv.hom.hom) ≫ e.hom.hom.hom
    rw [Category.assoc]
    have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
      congrArg (fun f => f.hom.hom) e.inv_hom_id
    rw [he]
    exact (Category.comp_id y.toMul).symm
  have hx₁ := levelBaseChange_kernel b G (Over.mk s) n x
  have hx₂ := levelBaseChange_kernel b G (Over.mk t) n
    (pathAct p ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X x)
  have hnat := pathAct_naturality p e.hom.hom.hom x
  have hpath := baseChangePointsEquiv_pathAct b hsb htb (torsion G (n : ℤ)) p x
  rw [hy, finiteLevelTransport_kernel]
  calc
    _ = levelBaseChange b G (Over.mk t) n
        (kernelLevelEquiv _ (Over.mk t) n (Additive.ofMul
          (pathAct p ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X x
            ≫ e.hom.hom.hom))) :=
      congrArg (fun v => levelBaseChange b G (Over.mk t) n
        (kernelLevelEquiv _ (Over.mk t) n (Additive.ofMul v))) hnat
    _ = kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
        (Additive.ofMul (baseChangePointsEquiv b (torsion G (n : ℤ)) (Over.mk t)
          (pathAct p ((Over.pullback b).mapGrp.obj (torsion G (n : ℤ))).X x))) := hx₂
    _ = kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
        (Additive.ofMul (pathAct (pathPushforward b hsb htb p) (torsion G (n : ℤ)).X
          (baseChangePointsEquiv b (torsion G (n : ℤ)) (Over.mk s) x))) :=
      congrArg (fun v => kernelLevelEquiv G ((Over.map b).obj (Over.mk t)) n
        (Additive.ofMul v)) hpath
    _ = finiteLevelTransport G n (pathPushforward b hsb htb p)
        (kernelLevelEquiv G ((Over.map b).obj (Over.mk s)) n
          (Additive.ofMul (baseChangePointsEquiv b (torsion G (n : ℤ)) (Over.mk s) x))) :=
      (finiteLevelTransport_kernel G n (pathPushforward b hsb htb p) _).symm
    _ = _ := congrArg (finiteLevelTransport G n (pathPushforward b hsb htb p)) hx₁.symm

end Tate
end Langlands.GroupScheme

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S'} {t : Spec (.of Ω') ⟶ S'}
  {hs : ∀ Y : Cover S', Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S', Finite (Fiber t Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)

/-- The finite square for an actual positive, invertible abelian torsion level. -/
theorem levelBaseChange_transport (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) (hu' : IsUnit (n : Γ(S', ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Level ((AbelianScheme.baseChange b).obj A) (Over.mk s) n) :
    GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk t) n
        (levelTransport htor ((AbelianScheme.baseChange b).obj A) n hn hu' p x) =
      levelTransport htor A n hn hu (pathPushforward b hsb htb p)
        (GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk s) n x) := by
  have := torsionKernel_isFinite htor A n hn hu
  have := torsionKernel_etale htor A n hn hu
  have : IsFinite (GroupScheme.kernel (GroupScheme.multiplication
      ((Over.pullback b).mapGrp.obj A.toGrp) n)).X.hom :=
    torsionKernel_isFinite htor ((AbelianScheme.baseChange b).obj A) n hn hu'
  have : Etale (GroupScheme.kernel (GroupScheme.multiplication
      ((Over.pullback b).mapGrp.obj A.toGrp) n)).X.hom :=
    torsionKernel_etale htor ((AbelianScheme.baseChange b).obj A) n hn hu'
  exact GroupScheme.Tate.levelBaseChange_finiteLevelTransport b hsb htb A.toGrp n p x

variable (P : ℕ → Prop)
  (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index P, IsUnit (n.val : Γ(S', ⊤)))

/-- The actual selected integral inverse-limit square, checked on every torsion coordinate. -/
theorem integralBaseChange_transport (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Integral ((AbelianScheme.baseChange b).obj A) (Over.mk s) P) :
    integralBaseChange b A (Over.mk t) P
        (integralTransport htor ((AbelianScheme.baseChange b).obj A) P hu' p x) =
      integralTransport htor A P hu (pathPushforward b hsb htb p)
        (integralBaseChange b A (Over.mk s) P x) := by
  apply Subtype.ext
  funext n
  exact levelBaseChange_transport b hsb htb htor A n.val n.property.1 (hu n) (hu' n) p
    (x.val n)

/-- Rationalization preserves the actual base-change/path square. -/
theorem rationalBaseChange_transport (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational ((AbelianScheme.baseChange b).obj A) (Over.mk s) P) :
    rationalBaseChange b A (Over.mk t) P
        (rationalTransport htor ((AbelianScheme.baseChange b).obj A) P hu' p x) =
      rationalTransport htor A P hu (pathPushforward b hsb htb p)
        (rationalBaseChange b A (Over.mk s) P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change q ⊗ₜ[ℤ] integralBaseChange b A (Over.mk t) P
      (integralTransport htor ((AbelianScheme.baseChange b).obj A) P hu' p x) =
        q ⊗ₜ[ℤ] integralTransport htor A P hu (pathPushforward b hsb htb p)
          (integralBaseChange b A (Over.mk s) P x)
    rw [integralBaseChange_transport b hsb htb htor A P hu hu']
  | add x y hx hy => simp_all

/-- Compare the actual rational Tate module over `s` with that over `t ≫ b`,
using the given path on the new base and then actual pointed base change. -/
def rationalBaseChangeAlongPath (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Rational ((AbelianScheme.baseChange b).obj A) (Over.mk s) P ≃ₗ[ℚ]
      Rational A (Over.mk (t ≫ b)) P :=
  (rationalTransport htor ((AbelianScheme.baseChange b).obj A) P hu' p).trans
    (rationalBaseChange b A (Over.mk t) P)

/-- The same diagonal comparison is obtained by first changing base and then using the pushed path. -/
theorem rationalBaseChangeAlongPath_apply (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational ((AbelianScheme.baseChange b).obj A) (Over.mk s) P) :
    rationalBaseChangeAlongPath b htor A P hu' p x =
      rationalTransport htor A P hu (pathPushforward b hsb htb p)
        (rationalBaseChange b A (Over.mk s) P x) :=
  rationalBaseChange_transport b hsb htb htor A P hu hu' p x

/-- The inverse diagonal comparison can likewise be computed on the other two sides of the square. -/
theorem rationalBaseChangeAlongPath_symm_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational A (Over.mk (t ≫ b)) P) :
    (rationalBaseChangeAlongPath b htor A P hu' p).symm x =
      (rationalBaseChange b A (Over.mk s) P).symm
        ((rationalTransport htor A P hu (pathPushforward b hsb htb p)).symm x) := by
  apply (rationalBaseChange b A (Over.mk s) P).injective
  apply (rationalTransport htor A P hu (pathPushforward b hsb htb p)).injective
  rw [← rationalBaseChangeAlongPath_apply b hsb htb htor A P hu hu']
  simp

/-- The same square holds for the finite-adelic linear comparisons with one scalar identification. -/
theorem finiteAdeleBaseChange_transport (h : Global.RationalProfiniteIntegerAdeleComparison)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Rational ((AbelianScheme.baseChange b).obj A) (Over.mk s) P) :
    finiteAdeleBaseChange b A (Over.mk t) P h
        (finiteAdeleTransport htor ((AbelianScheme.baseChange b).obj A) P hu' h p x) =
      finiteAdeleTransport htor A P hu h (pathPushforward b hsb htb p)
        (finiteAdeleBaseChange b A (Over.mk s) P h x) :=
  rationalBaseChange_transport b hsb htb htor A P hu hu' p x

/-- The coupled away scalar comparison gives the same square on the selected prime-to system. -/
theorem primeToFiniteAdeleBaseChange_transport
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : RationalAway ((AbelianScheme.baseChange b).obj A) (Over.mk s) m) :
    primeToFiniteAdeleBaseChange b A (Over.mk t) hAway
        (primeToFiniteAdeleTransport htor ((AbelianScheme.baseChange b).obj A)
          m hu' hAway p x) =
      primeToFiniteAdeleTransport htor A m hu hAway (pathPushforward b hsb htb p)
        (primeToFiniteAdeleBaseChange b A (Over.mk s) hAway x) :=
  rationalBaseChange_transport b hsb htb htor A (fun n => Nat.Coprime n m) hu hu' p x

end Langlands.AbelianScheme.Tate
