import Langlands.AlgebraicGeometry.FiniteEtale.Pullback
import Langlands.AbelianScheme.Tate.RationalBaseChange
import Langlands.AbelianScheme.Tate.RationalMonodromy

open CategoryTheory AlgebraicGeometry

universe u
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)

/-- Actual abelian torsion-level base change intertwines the pointed monodromy actions. -/
def LevelMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
    (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) (hu' : IsUnit (n : Γ(S', ⊤)))
    (g : FundamentalGroup t ht)
    (x : Level ((AbelianScheme.baseChange b).obj A) (Over.mk t) n),
    GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk t) n
      (levelMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) n hn hu' g x) =
    levelMonodromy (t ≫ b) hs htor A n hn hu
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk t) n x)

/-- Selected integral Tate base change intertwines the pointed monodromy actions. -/
def IntegralMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
    (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index P, IsUnit (n.val : Γ(S', ⊤)))
    (g : FundamentalGroup t ht)
    (x : Integral ((AbelianScheme.baseChange b).obj A) (Over.mk t) P),
    integralBaseChange b A (Over.mk t) P
      (integralMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) P hu' g x) =
    integralMonodromy (t ≫ b) hs htor A P hu
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (integralBaseChange b A (Over.mk t) P x)

/-- Rationalized selected Tate base change intertwines the pointed monodromy actions. -/
def RationalMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
    (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index P, IsUnit (n.val : Γ(S', ⊤)))
    (g : FundamentalGroup t ht)
    (x : Rational ((AbelianScheme.baseChange b).obj A) (Over.mk t) P),
    rationalBaseChange b A (Over.mk t) P
      (rationalMonodromy t ht htor ((AbelianScheme.baseChange b).obj A) P hu' g x) =
    rationalMonodromy (t ≫ b) hs htor A P hu
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
      (rationalBaseChange b A (Over.mk t) P x)

/-- Pointed base-change equivariance at finite, integral, and rational Tate levels. -/
def PointedMonodromyBaseChange : Prop :=
  LevelMonodromyBaseChange.{u} ∧ IntegralMonodromyBaseChange.{u} ∧
    RationalMonodromyBaseChange.{u}

end Langlands.AbelianScheme.Tate
