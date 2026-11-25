/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Derivations and localization of modules

A derivation `d : R → M` (an additive map satisfying the Leibniz rule) extends to the
localizations at a submonoid `S`, by the quotient rule `d(a/s) = (s • da - a • ds)/s²`.

## Main definitions

- `LocalizedModule.derivationLift`: the extension `S⁻¹R → S⁻¹M` of `d`.

## Main results

- `LocalizedModule.derivationLift_add`, `LocalizedModule.derivationLift_mul`: the extension
  is additive and satisfies the Leibniz rule.
-/

@[expose] public section

namespace LocalizedModule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submonoid R}

lemma mk_smul_mk' (a : R) (m : M) (s t : S) :
    (mk a s : LocalizedModule S R) • mk m t = mk (a • m) (s * t) :=
  mk_smul_mk a m s t

variable (S) (d : R →+ M) (hd : ∀ a b, d (a * b) = a • d b + b • d a)

include hd in
lemma derivationLift_wd (p p' : R × S) (h : p ≈ p') :
    mk ((p.2 : R) • d p.1 - p.1 • d p.2) (p.2 * p.2) =
      mk ((p'.2 : R) • d p'.1 - p'.1 • d p'.2) (p'.2 * p'.2) := by
  obtain ⟨a, s⟩ := p
  obtain ⟨a', s'⟩ := p'
  obtain ⟨u, hu⟩ := h
  simp only [Submonoid.smul_def, smul_eq_mul] at hu
  have dE := congrArg d hu
  simp only [hd] at dE
  refine mk_eq.mpr ⟨u * u, ?_⟩
  simp only [Submonoid.smul_def, Submonoid.coe_mul]
  linear_combination (norm := module) ((u : R) * s * s') • dE -
    hu • (((u : R) * s') • d s + ((u : R) * s) • d s' + ((s : R) * s') • d u)

/-- The extension of a derivation `d : R → M` to the localizations, `d(a/s) = (s da - a ds)/s²`. -/
noncomputable def derivationLift : LocalizedModule S R → LocalizedModule S M := fun x ↦
  x.liftOn (fun p ↦ mk ((p.2 : R) • d p.1 - p.1 • d p.2) (p.2 * p.2))
    (derivationLift_wd S d hd)


@[simp]
lemma derivationLift_mk (a : R) (s : S) :
    derivationLift S d hd (mk a s) = mk ((s : R) • d a - a • d s) (s * s) :=
  rfl

lemma derivationLift_add (x y : LocalizedModule S R) :
    derivationLift S d hd (x + y) = derivationLift S d hd x + derivationLift S d hd y := by
  induction x using induction_on with | h a s
  induction y using induction_on with | h b t
  rw [mk_add_mk, derivationLift_mk, derivationLift_mk, derivationLift_mk, mk_add_mk, mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_eq_mul, map_add, hd]
  module

lemma derivationLift_mul (x y : LocalizedModule S R) :
    derivationLift S d hd (x * y) = x • derivationLift S d hd y + y • derivationLift S d hd x := by
  induction x using induction_on with | h a s
  induction y using induction_on with | h b t
  rw [show (mk a s : LocalizedModule S R) * mk b t = mk (a * b) (s * t) from mk_mul_mk,
    derivationLift_mk, derivationLift_mk, derivationLift_mk, mk_smul_mk',
    mk_smul_mk', mk_add_mk, mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, hd]
  module

lemma derivationLift_mk_one (a : R) : derivationLift S d hd (mk a 1) = mk (d a) 1 := by
  rw [derivationLift_mk, mk_eq]
  refine ⟨1, ?_⟩
  have : d 1 = 0 := by simpa using hd 1 1
  simp [this]

end LocalizedModule
