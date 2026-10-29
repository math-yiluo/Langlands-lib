import Langlands.AbelianScheme.Tate.TwistRationalTransport
import Langlands.AbelianScheme.Tate.MultiplicativeRationalAffine

/-! # Geometric transport of twists over sections of a geometric point -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u v

namespace Langlands.TateTwist.Divisibility

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']

/-- A ring equivalence induces an equivalence linear over the compared finite adeles. -/
def finiteAdeleMapEquiv (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (f : R ≃+* R') :
    letI := finiteAdeleModule R P h
    letI := finiteAdeleModule R' P h
    Rational R P ≃ₗ[Global.FiniteAdeles ℚ] Rational R' P := by
  letI := finiteAdeleModule R P h
  letI := finiteAdeleModule R' P h
  exact { (rationalMapEquiv P f).toAddEquiv with
    map_smul' := rationalMap_finiteAdeleAction P h f.toRingHom }

@[simp] theorem finiteAdeleMapEquiv_apply (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (f : R ≃+* R')
    (x : Rational R P) :
    finiteAdeleMapEquiv P h f x = rationalMap P f.toRingHom x := rfl

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}

/-- The same ring equivalence preserves the coupled prime-to-modulus adelic action. -/
def primeToFiniteAdeleMapEquiv
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) (f : R ≃+* R') :
    letI := primeToFiniteAdeleModule R hAway
    letI := primeToFiniteAdeleModule R' hAway
    RationalAway R m ≃ₗ[Global.PrimeToFiniteAdeles m] RationalAway R' m := by
  letI := primeToFiniteAdeleModule R hAway
  letI := primeToFiniteAdeleModule R' hAway
  exact { (rationalMapEquiv (fun n => Nat.Coprime n m) f).toAddEquiv with
    map_smul' := rationalMap_primeToFiniteAdeleAction hAway f.toRingHom }

@[simp] theorem primeToFiniteAdeleMapEquiv_apply
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) (f : R ≃+* R')
    (x : RationalAway R m) :
    primeToFiniteAdeleMapEquiv hAway f x =
      rationalMap (fun n => Nat.Coprime n m) f.toRingHom x := rfl

end Langlands.TateTwist.Divisibility

namespace Langlands.TateTwist.Geometry

open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']

/-- Canonical comparison of the section-ring twist and the actual point-field twist. -/
def sectionRationalEquiv (s : Spec (.of Ω) ⟶ S) (P : ℕ → Prop) :
    Divisibility.Rational Γ((Over.mk s).left, ⊤) P ≃ₗ[ℚ] Divisibility.Rational Ω P :=
  Divisibility.rationalMapEquiv P (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv

@[simp] theorem sectionRationalEquiv_apply (s : Spec (.of Ω) ⟶ S) (P : ℕ → Prop)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionRationalEquiv s P x =
      Divisibility.rationalMap P (Scheme.ΓSpecIso (.of Ω)).hom.hom x := rfl

/-- This comparison is the one already used by the affine Gm Tate comparison. -/
theorem sectionRationalEquiv_gm (s : Spec (.of Ω) ⟶ S) (P : ℕ → Prop)
    (x : GroupScheme.Tate.Rational (GroupScheme.Gm S).toGrp (Over.mk s) P) :
    sectionRationalEquiv s P
        (GroupScheme.Gm.TateComparison.rationalEquiv (Over.mk s) P x) =
      GroupScheme.Gm.TateComparison.affineRationalEquiv s P x :=
  (GroupScheme.Gm.TateComparison.affineRationalEquiv_apply s P x).symm

variable {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}
  (P : ℕ → Prop)
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

/-- Transport of the actual section-ring twist by the canonical point-field comparisons. -/
def sectionRationalTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Divisibility.Rational Γ((Over.mk s).left, ⊤) P ≃ₗ[ℚ]
      Divisibility.Rational Γ((Over.mk t).left, ⊤) P :=
  (sectionRationalEquiv s P).trans
    ((rationalTransport P (hμfin := hμfin) (hμet := hμet) p).trans
      (sectionRationalEquiv t P).symm)

@[simp] theorem sectionRationalTransport_apply (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p x =
      (sectionRationalEquiv t P).symm
        (rationalTransport P (hμfin := hμfin) (hμet := hμet) p
          (sectionRationalEquiv s P x)) := rfl

@[simp] theorem sectionRationalTransport_refl
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionRationalTransport P (hμfin := hμfin) (hμet := hμet)
      (Iso.refl (fiberFunctor s hs)) x = x := by
  simp [sectionRationalTransport]

theorem sectionRationalTransport_trans
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) (p ≪≫ q) x =
      sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) q
        (sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p x) := by
  simp [sectionRationalTransport, rationalTransport_trans]

theorem sectionRationalTransport_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p).symm =
      sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p.symm := by
  apply LinearEquiv.ext
  intro x
  rfl

omit hμfin hμet in
/-- The canonical section comparison preserves the same finite-adelic scalar action. -/
def sectionFiniteAdeleEquiv (s : Spec (.of Ω) ⟶ S) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    letI := Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
    letI := Divisibility.finiteAdeleModule Ω P h
    Divisibility.Rational Γ((Over.mk s).left, ⊤) P ≃ₗ[Global.FiniteAdeles ℚ]
      Divisibility.Rational Ω P :=
  Divisibility.finiteAdeleMapEquiv P h
    (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Adelic section-twist transport retains the actual geometric root transport. -/
def sectionFiniteAdeleTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    letI := Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
    letI := Divisibility.finiteAdeleModule Γ((Over.mk t).left, ⊤) P h
    Divisibility.Rational Γ((Over.mk s).left, ⊤) P ≃ₗ[Global.FiniteAdeles ℚ]
      Divisibility.Rational Γ((Over.mk t).left, ⊤) P := by
  letI := Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
  letI := Divisibility.finiteAdeleModule Γ((Over.mk t).left, ⊤) P h
  letI := Divisibility.finiteAdeleModule Ω P h
  letI := Divisibility.finiteAdeleModule Ω' P h
  exact (sectionFiniteAdeleEquiv s P h).trans
    ((finiteAdeleTransport P (hμfin := hμfin) (hμet := hμet) h p).trans
      (sectionFiniteAdeleEquiv t P h).symm)

@[simp] theorem sectionFiniteAdeleTransport_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionFiniteAdeleTransport P (hμfin := hμfin) (hμet := hμet) h p x =
      sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p x := rfl

/-- The geometric root representation transported to the section-ring twist. -/
def sectionFiniteAdeleRepresentation :
    letI := Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
    FundamentalGroup s hs →*
      (Divisibility.Rational Γ((Over.mk s).left, ⊤) P ≃ₗ[Global.FiniteAdeles ℚ]
        Divisibility.Rational Γ((Over.mk s).left, ⊤) P) := by
  letI := Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
  letI := Divisibility.finiteAdeleModule Ω P h
  let e := sectionFiniteAdeleEquiv s P h
  let ρ := finiteAdeleRepresentation s hs P (hμfin := hμfin) (hμet := hμet) h
  exact {
    toFun := fun g => e.trans ((ρ g).trans e.symm)
    map_one' := by ext x; simp [map_one]
    map_mul' := fun g k => by ext x; simp [map_mul] }

theorem sectionFiniteAdeleTransport_aut (g : FundamentalGroup s hs)
    (x : Divisibility.Rational Γ((Over.mk s).left, ⊤) P) :
    sectionFiniteAdeleTransport P (hμfin := hμfin) (hμet := hμet) h g x =
      sectionFiniteAdeleRepresentation P (hμfin := hμfin) (hμet := hμet) h g x := by
  change (sectionRationalEquiv s P).symm
    (rationalTransport P (hμfin := hμfin) (hμet := hμet) g
      (sectionRationalEquiv s P x)) =
    (sectionRationalEquiv s P).symm
      (rationalMonodromy s hs P (hμfin := hμfin) (hμet := hμet) g
        (sectionRationalEquiv s P x))
  rw [rationalTransport_aut]

end Langlands.TateTwist.Geometry

namespace Langlands.TateTwist.Geometry

open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu)
open Langlands.GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- The canonical section comparison is also linear over the away finite adeles. -/
def sectionPrimeToFiniteAdeleEquiv (s : Spec (.of Ω) ⟶ S) :
    letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
    letI := Divisibility.primeToFiniteAdeleModule Ω hAway
    Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m ≃ₗ[Global.PrimeToFiniteAdeles m]
      Divisibility.RationalAway Ω m :=
  Divisibility.primeToFiniteAdeleMapEquiv hAway
    (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv

variable
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

/-- Prime-to-modulus section transport uses only the retained finite étale orders. -/
def sectionPrimeToFiniteAdeleTransport (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
    letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk t).left, ⊤) hAway
    Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m ≃ₗ[Global.PrimeToFiniteAdeles m]
      Divisibility.RationalAway Γ((Over.mk t).left, ⊤) m := by
  letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk t).left, ⊤) hAway
  letI := Divisibility.primeToFiniteAdeleModule Ω hAway
  letI := Divisibility.primeToFiniteAdeleModule Ω' hAway
  exact (sectionPrimeToFiniteAdeleEquiv hAway s).trans
    ((primeToFiniteAdeleTransport m (hμfin := hμfin) (hμet := hμet) hAway p).trans
      (sectionPrimeToFiniteAdeleEquiv hAway t).symm)

@[simp] theorem sectionPrimeToFiniteAdeleTransport_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (x : Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m) :
    sectionPrimeToFiniteAdeleTransport hAway (hμfin := hμfin) (hμet := hμet) p x =
      sectionRationalTransport (fun n => Nat.Coprime n m)
        (hμfin := hμfin) (hμet := hμet) p x := rfl

/-- The actual away root monodromy representation on the section-ring twist. -/
def sectionPrimeToFiniteAdeleRepresentation :
    letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
    FundamentalGroup s hs →*
      (Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m ≃ₗ[Global.PrimeToFiniteAdeles m]
        Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m) := by
  letI := Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  letI := Divisibility.primeToFiniteAdeleModule Ω hAway
  let e := sectionPrimeToFiniteAdeleEquiv hAway s
  let ρ := primeToFiniteAdeleRepresentation s hs m (hμfin := hμfin) (hμet := hμet) hAway
  exact {
    toFun := fun g => e.trans ((ρ g).trans e.symm)
    map_one' := by ext x; simp [map_one]
    map_mul' := fun g k => by ext x; simp [map_mul] }

theorem sectionPrimeToFiniteAdeleTransport_aut (g : FundamentalGroup s hs)
    (x : Divisibility.RationalAway Γ((Over.mk s).left, ⊤) m) :
    sectionPrimeToFiniteAdeleTransport hAway (hμfin := hμfin) (hμet := hμet) g x =
      sectionPrimeToFiniteAdeleRepresentation hAway
        (hμfin := hμfin) (hμet := hμet) g x := by
  change (sectionRationalEquiv s (fun n => Nat.Coprime n m)).symm
    (rationalTransport (fun n => Nat.Coprime n m) (hμfin := hμfin) (hμet := hμet) g
      (sectionRationalEquiv s (fun n => Nat.Coprime n m) x)) =
    (sectionRationalEquiv s (fun n => Nat.Coprime n m)).symm
      (rationalMonodromy s hs (fun n => Nat.Coprime n m) (hμfin := hμfin) (hμet := hμet) g
        (sectionRationalEquiv s (fun n => Nat.Coprime n m) x))
  rw [rationalTransport_aut]

end Langlands.TateTwist.Geometry
