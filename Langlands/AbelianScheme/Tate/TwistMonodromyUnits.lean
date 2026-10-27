import Langlands.GroupScheme.MuFiniteEtaleProof
import Langlands.AbelianScheme.Tate.TwistMonodromyBaseChange

/-! # Actual twist monodromy from invertible orders -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.TateTwist.Geometry.InvertibleOrders

open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu muFiniteEtale)
open Langlands.GroupScheme.Tate (Index)

/-- The existing finite-morphism input follows from the actual roots-of-unity theorem. -/
theorem finite (S : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) : IsFinite (mu S n).X.hom :=
  (muFiniteEtale S n hn hu).1

/-- The existing etale-morphism input follows from the actual roots-of-unity theorem. -/
theorem etale (S : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) : Etale (mu S n).X.hom :=
  (muFiniteEtale S n hn hu).2

/-- Pullback preserves the unit hypothesis on an order. -/
theorem pullbackUnit {S S' : Scheme.{u}} (b : S' ⟶ S) (n : ℕ)
    (hu : IsUnit (n : Γ(S, ⊤))) : IsUnit (n : Γ(S', ⊤)) := by
  simpa only [map_natCast] using hu.map b.appTop.hom

/-- Finiteness at every positive selected order, derived from invertibility. -/
theorem selectedFinite (S : Scheme.{u}) (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    ∀ n : Index P, IsFinite (mu S n.val).X.hom :=
  fun n => finite S n.val n.property.1 (hu n)

/-- Etaleness at every positive selected order, derived from invertibility. -/
theorem selectedEtale (S : Scheme.{u}) (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    ∀ n : Index P, Etale (mu S n.val).X.hom :=
  fun n => etale S n.val n.property.1 (hu n)

/-- A single unit prime gives the complete finite prime-power family, including order one. -/
theorem primeFinite (S : Scheme.{u}) (p : ℕ) [hp : Fact p.Prime]
    (hu : IsUnit (p : Γ(S, ⊤))) : ∀ n : ℕ, IsFinite (mu S (p ^ n)).X.hom := by
  intro n
  exact finite S (p ^ n) (pow_pos hp.out.pos n) (by simpa only [Nat.cast_pow] using hu.pow n)

/-- A single unit prime gives the complete etale prime-power family. -/
theorem primeEtale (S : Scheme.{u}) (p : ℕ) [hp : Fact p.Prime]
    (hu : IsUnit (p : Γ(S, ⊤))) : ∀ n : ℕ, Etale (mu S (p ^ n)).X.hom := by
  intro n
  exact etale S (p ^ n) (pow_pos hp.out.pos n) (by simpa only [Nat.cast_pow] using hu.pow n)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y))

/-- The existing finite geometric representation with its geometry proved from a unit. -/
abbrev levelRepresentation (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) :
    FundamentalGroup s hfin →* (Level Ω n ≃ₗ[ZMod n] Level Ω n) := by
  letI := finite S n hn hu
  letI := etale S n hn hu
  exact Geometry.levelRepresentation s hfin n

/-- Joint continuity of the finite action under positive-order invertibility. -/
theorem continuous_levelRepresentation (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) :
    Continuous (fun z : FundamentalGroup s hfin × Level Ω n =>
      levelRepresentation s hfin n hn hu z.1 z.2) := by
  let := finite S n hn hu
  let := etale S n hn hu
  exact Geometry.continuous_levelMonodromy s hfin n

/-- The selected integral twist representation, using only invertibility for its mu geometry. -/
abbrev integralRepresentation (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    FundamentalGroup s hfin →*
      (Divisibility.Integral Ω P ≃ₗ[Global.ProfiniteIntegerRing] Divisibility.Integral Ω P) :=
  Geometry.integralRepresentation s hfin P
    (hμfin := selectedFinite S P hu) (hμet := selectedEtale S P hu)

/-- The same selected action is jointly continuous on the existing inverse-limit topology. -/
theorem continuous_integralRepresentation (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    Continuous (fun z : FundamentalGroup s hfin × Divisibility.Integral Ω P =>
      integralRepresentation s hfin P hu z.1 z.2) :=
  Geometry.continuous_integralMonodromy s hfin P
    (hμfin := selectedFinite S P hu) (hμet := selectedEtale S P hu)

/-- The existing rationalized selected representation with its mu geometry discharged. -/
abbrev rationalRepresentation (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    FundamentalGroup s hfin →*
      (Divisibility.Rational Ω P ≃ₗ[ℚ] Divisibility.Rational Ω P) :=
  Geometry.rationalRepresentation s hfin P
    (hμfin := selectedFinite S P hu) (hμet := selectedEtale S P hu)

/-- Integral prime-adic twist monodromy needs just invertibility of the prime. -/
abbrev primeRepresentation (p : ℕ) [Fact p.Prime] (hu : IsUnit (p : Γ(S, ⊤))) :
    FundamentalGroup s hfin →* (Integral Ω p ≃ₗ[ℤ_[p]] Integral Ω p) :=
  Geometry.primeRepresentation s hfin p
    (hμfin := primeFinite S p hu) (hμet := primeEtale S p hu)

/-- Joint continuity of integral prime-adic twist monodromy from a unit prime. -/
theorem continuous_primeRepresentation (p : ℕ) [Fact p.Prime]
    (hu : IsUnit (p : Γ(S, ⊤))) :
    Continuous (fun z : FundamentalGroup s hfin × Integral Ω p =>
      primeRepresentation s hfin p hu z.1 z.2) :=
  Geometry.continuous_primeMonodromy s hfin p
    (hμfin := primeFinite S p hu) (hμet := primeEtale S p hu)

/-- Rational prime-adic monodromy uses the same single prime-invertibility input. -/
abbrev rationalPrimeRepresentation (p : ℕ) [Fact p.Prime]
    (hu : IsUnit (p : Γ(S, ⊤))) :
    FundamentalGroup s hfin →* (Rational Ω p ≃ₗ[ℚ_[p]] Rational Ω p) :=
  Geometry.rationalPrimeRepresentation s hfin p
    (hμfin := primeFinite S p hu) (hμet := primeEtale S p hu)

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S) (t : Spec (.of Ω) ⟶ S')
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))

/-- Finite monodromy restricts along pointed base change; units are pulled back. -/
theorem levelRepresentation_baseChange (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) :
    (levelRepresentation (t ≫ b) hs n hn hu).comp
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs) =
      levelRepresentation t ht n hn (pullbackUnit b n hu) := by
  let := finite S n hn hu
  let := etale S n hn hu
  let := finite S' n hn (pullbackUnit b n hu)
  let := etale S' n hn (pullbackUnit b n hu)
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  exact Geometry.levelMonodromy_baseChange b t ht hs n g x

/-- Selected integral monodromy restricts along pointed base change using pulled-back units. -/
theorem integralRepresentation_baseChange (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    (integralRepresentation (t ≫ b) hs P hu).comp
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs) =
      integralRepresentation t ht P (fun n => pullbackUnit b n.val (hu n)) := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  exact Geometry.integralMonodromyBaseChange S S' b Ω inferInstance t ht hs P
    (selectedFinite S P hu) (selectedEtale S P hu)
    (selectedFinite S' P (fun n => pullbackUnit b n.val (hu n)))
    (selectedEtale S' P (fun n => pullbackUnit b n.val (hu n))) g x

/-- Rational selected monodromy has the same pointed base-change compatibility. -/
theorem rationalRepresentation_baseChange (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))) :
    (rationalRepresentation (t ≫ b) hs P hu).comp
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs) =
      rationalRepresentation t ht P (fun n => pullbackUnit b n.val (hu n)) := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  exact Geometry.rationalMonodromyBaseChange S S' b Ω inferInstance t ht hs P
    (selectedFinite S P hu) (selectedEtale S P hu)
    (selectedFinite S' P (fun n => pullbackUnit b n.val (hu n)))
    (selectedEtale S' P (fun n => pullbackUnit b n.val (hu n))) g x

/-- Integral prime-adic monodromy restricts along pointed base change from a unit prime. -/
theorem primeRepresentation_baseChange (p : ℕ) [Fact p.Prime]
    (hu : IsUnit (p : Γ(S, ⊤))) :
    (primeRepresentation (t ≫ b) hs p hu).comp
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs) =
      primeRepresentation t ht p (pullbackUnit b p hu) := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  exact Geometry.primeMonodromyBaseChange S S' b Ω inferInstance t ht hs p inferInstance
    (primeFinite S p hu) (primeEtale S p hu)
    (primeFinite S' p (pullbackUnit b p hu))
    (primeEtale S' p (pullbackUnit b p hu)) g x

/-- Rational prime-adic monodromy restricts along pointed base change from a unit prime. -/
theorem rationalPrimeRepresentation_baseChange (p : ℕ) [Fact p.Prime]
    (hu : IsUnit (p : Γ(S, ⊤))) :
    (rationalPrimeRepresentation (t ≫ b) hs p hu).comp
        (fundamentalGroupMap b t (t ≫ b) rfl ht hs) =
      rationalPrimeRepresentation t ht p (pullbackUnit b p hu) := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  exact Geometry.rationalPrimeMonodromyBaseChange S S' b Ω inferInstance t ht hs p inferInstance
    (primeFinite S p hu) (primeEtale S p hu)
    (primeFinite S' p (pullbackUnit b p hu))
    (primeEtale S' p (pullbackUnit b p hu)) g x

end BaseChange

end Langlands.TateTwist.Geometry.InvertibleOrders
