import Langlands.AbelianScheme.Tate.TwistRationalPrimeMonodromy
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

open CategoryTheory AlgebraicGeometry

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

universe u

/-- Selected integral root monodromy restricts along the pointed fundamental-group map. -/
def IntegralMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (P : ℕ → Prop)
    (hSfin : ∀ n : Index P, IsFinite (mu S (n.val)).X.hom)
    (hSet : ∀ n : Index P, Etale (mu S (n.val)).X.hom)
    (hTfin : ∀ n : Index P, IsFinite (mu S' (n.val)).X.hom)
    (hTet : ∀ n : Index P, Etale (mu S' (n.val)).X.hom)
    (g : FundamentalGroup t ht) (x : Divisibility.Integral Ω P),
    integralMonodromy (t ≫ b) hs P (hμfin := hSfin) (hμet := hSet)
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g) x =
      integralMonodromy t ht P (hμfin := hTfin) (hμet := hTet) g x

/-- Prime-adic integral root monodromy restricts along the pointed fundamental-group map. -/
def PrimeMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (p : ℕ) (_ : Fact p.Prime)
    (hSfin : ∀ n : ℕ, IsFinite (mu S (p ^ n)).X.hom)
    (hSet : ∀ n : ℕ, Etale (mu S (p ^ n)).X.hom)
    (hTfin : ∀ n : ℕ, IsFinite (mu S' (p ^ n)).X.hom)
    (hTet : ∀ n : ℕ, Etale (mu S' (p ^ n)).X.hom)
    (g : FundamentalGroup t ht) (x : Integral Ω p),
    primeMonodromy (t ≫ b) hs p (hμfin := hSfin) (hμet := hSet)
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g) x =
      primeMonodromy t ht p (hμfin := hTfin) (hμet := hTet) g x

/-- Selected rational root monodromy restricts along the pointed fundamental-group map. -/
def RationalMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (P : ℕ → Prop)
    (hSfin : ∀ n : Index P, IsFinite (mu S (n.val)).X.hom)
    (hSet : ∀ n : Index P, Etale (mu S (n.val)).X.hom)
    (hTfin : ∀ n : Index P, IsFinite (mu S' (n.val)).X.hom)
    (hTet : ∀ n : Index P, Etale (mu S' (n.val)).X.hom)
    (g : FundamentalGroup t ht) (x : Divisibility.Rational Ω P),
    rationalMonodromy (t ≫ b) hs P (hμfin := hSfin) (hμet := hSet)
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g) x =
      rationalMonodromy t ht P (hμfin := hTfin) (hμet := hTet) g x

/-- Rational prime-adic root monodromy restricts along the pointed fundamental-group map. -/
def RationalPrimeMonodromyBaseChange : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (Ω : Type u) (_ : Field Ω)
    (t : Spec (.of Ω) ⟶ S')
    (ht : ∀ Y : Cover S', Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
    (p : ℕ) (_ : Fact p.Prime)
    (hSfin : ∀ n : ℕ, IsFinite (mu S (p ^ n)).X.hom)
    (hSet : ∀ n : ℕ, Etale (mu S (p ^ n)).X.hom)
    (hTfin : ∀ n : ℕ, IsFinite (mu S' (p ^ n)).X.hom)
    (hTet : ∀ n : ℕ, Etale (mu S' (p ^ n)).X.hom)
    (g : FundamentalGroup t ht) (x : Rational Ω p),
    rationalPrimeMonodromy (t ≫ b) hs p (hμfin := hSfin) (hμet := hSet)
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs g) x =
      rationalPrimeMonodromy t ht p (hμfin := hTfin) (hμet := hTet) g x

/-- Pointed base-change compatibility for the four existing integral and rational root actions. -/
def TwistMonodromyBaseChange : Prop :=
  IntegralMonodromyBaseChange.{u} ∧ PrimeMonodromyBaseChange.{u} ∧
    RationalMonodromyBaseChange.{u} ∧ RationalPrimeMonodromyBaseChange.{u}

end Langlands.TateTwist.Geometry
