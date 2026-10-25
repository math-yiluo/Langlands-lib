import Langlands.AbelianScheme.Tate.TwistMonodromyBaseChangeStatement
import Langlands.AbelianScheme.Tate.TwistFiniteBaseChange

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u

/-- Selected integral root monodromy is compatible with pointed base change. -/
theorem integralMonodromyBaseChange : IntegralMonodromyBaseChange.{u} := by
  intro S S' b Ω hΩ t ht hs P hSfin hSet hTfin hTet g x
  let := hΩ
  let := hSfin
  let := hSet
  let := hTfin
  let := hTet
  apply Subtype.ext
  funext n
  exact levelMonodromy_baseChange b t ht hs n.val g (x.val n)

/-- Prime-adic integral root monodromy is compatible with pointed base change. -/
theorem primeMonodromyBaseChange : PrimeMonodromyBaseChange.{u} := by
  intro S S' b Ω hΩ t ht hs p hp hSfin hSet hTfin hTet g x
  let := hΩ
  let := hp
  let := hSfin
  let := hSet
  let := hTfin
  let := hTet
  apply Subtype.ext
  funext n
  exact levelMonodromy_baseChange b t ht hs (p ^ n) g (x.val n)

/-- Scalar extension over the integers preserves the selected integral comparison. -/
theorem rationalMonodromyBaseChange : RationalMonodromyBaseChange.{u} := by
  intro S S' b Ω hΩ t ht hs P hSfin hSet hTfin hTet g x
  let := hΩ
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    rw [rationalMonodromy_tmul, rationalMonodromy_tmul]
    exact congrArg (fun y : Divisibility.Integral Ω P => q ⊗ₜ[ℤ] y)
      (integralMonodromyBaseChange S S' b Ω hΩ t ht hs P hSfin hSet hTfin hTet g x)
  | add x y hx hy => simp_all

/-- Scalar extension over the prime-adic integers preserves the prime comparison. -/
theorem rationalPrimeMonodromyBaseChange : RationalPrimeMonodromyBaseChange.{u} := by
  intro S S' b Ω hΩ t ht hs p hp hSfin hSet hTfin hTet g x
  let := hΩ
  let := hp
  have heq :
      primeMonodromyHom (t ≫ b) hs p (hμfin := hSfin) (hμet := hSet)
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g) =
      primeMonodromyHom t ht p (hμfin := hTfin) (hμet := hTet) g := by
    apply LinearMap.ext
    intro y
    exact primeMonodromyBaseChange S S' b Ω hΩ t ht hs p hp hSfin hSet hTfin hTet g y
  have hbase := congrArg
    (fun f : Integral Ω p →ₗ[ℤ_[p]] Integral Ω p => f.baseChange ℚ_[p]) heq
  exact LinearMap.congr_fun hbase x

/-- The four existing root monodromy actions restrict along pointed base change. -/
theorem twistMonodromyBaseChange : TwistMonodromyBaseChange.{u} :=
  ⟨integralMonodromyBaseChange, primeMonodromyBaseChange,
    rationalMonodromyBaseChange, rationalPrimeMonodromyBaseChange⟩

end Langlands.TateTwist.Geometry
