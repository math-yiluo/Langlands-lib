import Langlands.AbelianScheme.Tate.TwistRational
import Langlands.AbelianScheme.Tate.RationalScalars

/-! # Rational scalar actions on actual roots-of-unity twists -/

noncomputable section
open scoped TensorProduct

namespace Langlands.TateTwist.Divisibility

universe u v
variable (R : Type u) [CommRing R]

/-- Rationalized full residue scalars act on every selected root limit. -/
def rationalScalarAction (P : ℕ → Prop) :
    (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) →ₐ[ℚ] Module.End ℚ (Rational R P) :=
  TateScalarExtension.action _ _

/-- Rationalized away residue scalars act on the actual away root limit. -/
def rationalAwayScalarAction (p : ℕ) :
    (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) →ₐ[ℚ]
      Module.End ℚ (RationalAway R p) :=
  TateScalarExtension.action _ _

@[simp] theorem rationalScalarAction_tmul (P : ℕ → Prop)
    (q r : ℚ) (a : Global.ProfiniteIntegerRing) (x : Integral R P) :
    rationalScalarAction R P (q ⊗ₜ[ℤ] a) (r ⊗ₜ[ℤ] x) =
      (q * r) ⊗ₜ[ℤ] (a • x) :=
  TateScalarExtension.action_tmul _ _ _ _ _ _

@[simp] theorem rationalAwayScalarAction_tmul (p : ℕ)
    (q r : ℚ) (a : Global.PrimeToProfiniteIntegerRing p) (x : Away R p) :
    rationalAwayScalarAction R p (q ⊗ₜ[ℤ] a) (r ⊗ₜ[ℤ] x) =
      (q * r) ⊗ₜ[ℤ] (a • x) :=
  TateScalarExtension.action_tmul _ _ _ _ _ _

/-- Finite-adelic scalars act through the explicitly assumed scalar comparison. -/
def finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    Global.FiniteAdeles ℚ →ₐ[ℚ] Module.End ℚ (Rational R P) :=
  (rationalScalarAction R P).comp
    (Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm.toAlgHom

/-- Module structure for local installation; the comparison remains explicit. -/
@[instance_reducible] def finiteAdeleModule (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    Module (Global.FiniteAdeles ℚ) (Rational R P) :=
  Module.compHom _ (finiteAdeleAction R P h).toRingHom

@[simp] theorem finiteAdeleAction_diagonal (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (q : ℚ) (x : Rational R P) :
    finiteAdeleAction R P h (algebraMap ℚ (Global.FiniteAdeles ℚ) q) x = q • x := by
  rw [AlgHom.commutes]
  rfl

theorem finiteAdeleModule_smul (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (a : Global.FiniteAdeles ℚ) (x : Rational R P) :
    let := finiteAdeleModule R P h
    a • x = finiteAdeleAction R P h a x := rfl

theorem finiteAdeleModule_scalarTower (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := finiteAdeleModule R P h
    IsScalarTower ℚ (Global.FiniteAdeles ℚ) (Rational R P) := by
  let := finiteAdeleModule R P h
  exact IsScalarTower.of_algebraMap_smul (finiteAdeleAction_diagonal R P h)

/-- The chosen integral comparison recovers the actual residue action on roots. -/
theorem finiteAdeleAction_integral_tmul (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (a : Global.ProfiniteIntegerRing) (q : ℚ) (x : Integral R P) :
    finiteAdeleAction R P h
      (Global.RationalProfiniteIntegerAdeleComparison.integralEquiv h a)
      (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (a • x) := by
  have he := Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv_tmul h 1 a
  simp only [map_one, one_mul] at he
  change TateScalarExtension.action _ _
    ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm _) _ = _
  rw [← he, AlgEquiv.symm_apply_apply, TateScalarExtension.action_tmul, one_mul]

/-- Full and away scalar actions agree after the existing scalar restriction. -/
theorem rationalScalarAction_eq_away (p : ℕ)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalAway R p) :
    rationalScalarAction R (fun n => Nat.Coprime n p) a x =
      rationalAwayScalarAction R p
        (GroupScheme.Tate.rationalScalarRestrictAway p a) x := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      simp [rationalScalarAction_tmul, rationalAwayScalarAction_tmul,
        full_smul_eq_away_smul]
    | add x y hx hy => simp_all
  | add a b ha hb => simp_all

/-- Restriction of root families is compatible with restriction of residue scalars. -/
theorem rationalRestrictAway_scalarAction (p : ℕ)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : RationalFull R) :
    rationalRestrictAway R p (rationalScalarAction R _ a x) =
      rationalAwayScalarAction R p (GroupScheme.Tate.rationalScalarRestrictAway p a)
        (rationalRestrictAway R p x) := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x => simp [restrictAway_smul]
    | add x y hx hy => simp_all
  | add a b ha hb => simp_all

variable {R} {S : Type v} [CommRing S]

/-- Ring maps preserve the rationalized full residue action on actual roots. -/
theorem rationalMap_scalarAction (P : ℕ → Prop) (f : R →+* S)
    (a : ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) (x : Rational R P) :
    rationalMap P f (rationalScalarAction R P a x) =
      rationalScalarAction S P a (rationalMap P f x) :=
  TateScalarExtension.map_action (fullLinearMap P f) _ _

/-- Ring maps preserve the rationalized away residue action on actual roots. -/
theorem rationalMap_awayScalarAction (p : ℕ) (f : R →+* S)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) (x : RationalAway R p) :
    rationalMap _ f (rationalAwayScalarAction R p a x) =
      rationalAwayScalarAction S p a (rationalMap _ f x) :=
  TateScalarExtension.map_action (awayLinearMap p f) _ _

/-- The same chosen comparison makes every ring-induced map finite-adelic linear. -/
theorem rationalMap_finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (f : R →+* S)
    (a : Global.FiniteAdeles ℚ) (x : Rational R P) :
    rationalMap P f (finiteAdeleAction R P h a x) =
      finiteAdeleAction S P h a (rationalMap P f x) :=
  TateScalarExtension.map_action (fullLinearMap P f) _ _

/-- The existing ring-induced map, bundled with its finite-adelic linearity. -/
def finiteAdeleMap (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (f : R →+* S) :
    let := finiteAdeleModule R P h
    let := finiteAdeleModule S P h
    Rational R P →ₗ[Global.FiniteAdeles ℚ] Rational S P := by
  let := finiteAdeleModule R P h
  let := finiteAdeleModule S P h
  exact { (rationalMap P f).toAddHom with
    map_smul' := rationalMap_finiteAdeleAction P h f }

@[simp] theorem finiteAdeleMap_apply (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (f : R →+* S) (x : Rational R P) :
    finiteAdeleMap P h f x = rationalMap P f x := rfl

variable (R)

/-- The natural root automorphisms commute with finite-adelic scalars. -/
theorem rationalAutomorphismAction_finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (f : R ≃+* R)
    (a : Global.FiniteAdeles ℚ) (x : Rational R P) :
    rationalAutomorphismAction R P f (finiteAdeleAction R P h a x) =
      finiteAdeleAction R P h a (rationalAutomorphismAction R P f x) := by
  change (rationalMapEquiv P f).toLinearMap _ =
    finiteAdeleAction R P h a ((rationalMapEquiv P f).toLinearMap x)
  rw [rationalMapEquiv_toLinearMap]
  exact rationalMap_finiteAdeleAction P h f.toRingHom a x

/-- The natural away root automorphisms commute with rationalized away scalars. -/
theorem rationalAutomorphismAction_awayScalarAction (p : ℕ) (f : R ≃+* R)
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) (x : RationalAway R p) :
    rationalAutomorphismAction R (fun n => Nat.Coprime n p) f
        (rationalAwayScalarAction R p a x) =
      rationalAwayScalarAction R p a
        (rationalAutomorphismAction R (fun n => Nat.Coprime n p) f x) := by
  change (rationalMapEquiv _ f).toLinearMap _ =
    rationalAwayScalarAction R p a ((rationalMapEquiv _ f).toLinearMap x)
  rw [rationalMapEquiv_toLinearMap]
  exact rationalMap_awayScalarAction p f.toRingHom a x

section Galois
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The existing field-Galois action commutes with finite-adelic scalars. -/
theorem rationalGaloisAction_finiteAdeleAction (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (σ : Gal(L/K))
    (a : Global.FiniteAdeles ℚ) (x : Rational L P) :
    rationalGaloisAction K L P σ (finiteAdeleAction L P h a x) =
      finiteAdeleAction L P h a (rationalGaloisAction K L P σ x) :=
  rationalAutomorphismAction_finiteAdeleAction L P h
    (MulSemiringAction.toRingAut Gal(L/K) L σ) a x

/-- The existing field-Galois action commutes with rationalized away scalars. -/
theorem rationalGaloisAction_awayScalarAction (p : ℕ) (σ : Gal(L/K))
    (a : ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p) (x : RationalAway L p) :
    rationalGaloisAction K L (fun n => Nat.Coprime n p) σ
        (rationalAwayScalarAction L p a x) =
      rationalAwayScalarAction L p a
        (rationalGaloisAction K L (fun n => Nat.Coprime n p) σ x) :=
  rationalAutomorphismAction_awayScalarAction L p
    (MulSemiringAction.toRingAut Gal(L/K) L σ) a x

end Galois
end Langlands.TateTwist.Divisibility
