/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Data.Int.GCD

/-! # Dense-open field-extension comparison ingredients -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- A sheaf killed by a noninvertible prime and having invertible-order torsion has
zero cohomology, as does its inverse image along any scheme morphism.
Source: Stacks Project, Tag 0GJA, proof (remark (c), positive-characteristic case).
(blueprint: lemma-removing-finitely-many-points--1)

Proof: For each geometric stalk element x the invertible-order condition gives n > 0
with n invertible on Spec k and n*x = 0. The identity-annihilation hypothesis gives
r*x = 0 after applying sheafFiber_map_smul. If r divided n, the factorization of the
unit n would force r to be a unit, contradicting noninvertibility. Since r is prime,
gcd(r,n)=1, and nsmul_eq_zero_iff_of_coprime gives x = 0. Every stalk is zero, so geometric
stalks detect that F is zero. The coefficient-forgetting functor and inverse image
preserve zero objects. Ext into a zero object is zero in every degree, so the two
cohomology groups are subsingletons. This includes the zero ring and empty X or Y. -/
theorem prime_torsion_nonunit_cohomology (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X Y : Scheme.{u}} (a : Y ⟶ X)
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : r • 𝟙 F = 0) (hr : ¬ IsUnit (r : Γ(Spec (.of k), ⊤)))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] (q : ℕ) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) ∧
    Subsingleton (Sheaf.H (((a)^*[AddCommGrpCat.{u + 1}]).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q) := by
  have hid : 𝟙 F = 0 := by
    apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro s
    let P := Scheme.pointSmallEtale (X.algClosurePoint s)
    let E := P.sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hz : E.map (0 : F ⟶ F) = 0 := by
      simpa only [zero_smul] using P.sheafFiber_map_smul (0 : ℕ) (𝟙 F)
    have hm : r • 𝟙 (E.obj F) = 0 := by
      have hh := congrArg E.map hF
      rw [P.sheafFiber_map_smul r (𝟙 F)] at hh
      rw [hz] at hh
      simpa only [CategoryTheory.Functor.map_id] using hh
    rw [CategoryTheory.Functor.map_id, hz]
    ext x
    obtain ⟨n, _, hn, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := Spec (.of k)) (AlgebraicClosure (X.residueField s)) (X.algClosurePoint s) x
    have hcop : r.Coprime n := by
      apply (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
      rintro ⟨m, rfl⟩
      apply hr
      exact isUnit_of_mul_isUnit_left (by simpa only [Nat.cast_mul] using hn)
    have hx' : r • x = 0 := by
      have hh := congrArg (fun t : E.obj F ⟶ E.obj F ↦ t.hom x) hm
      simpa using hh
    simpa using (nsmul_eq_zero_iff_of_coprime hcop).mp ⟨hx', hx⟩
  let A := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  have ha : Limits.IsZero A := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    have hh := congrArg
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map) hid
    have hz : (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map (0 : F ⟶ F) = 0 := by
      ext V x
      rfl
    simpa only [CategoryTheory.Functor.map_id, hz] using hh
  have hb : Limits.IsZero (((a)^*[AddCommGrpCat.{u + 1}]).obj A) :=
    CategoryTheory.Functor.map_isZero _ ha
  exact ⟨Sheaf.subsingleton_H_of_isZero ha q, Sheaf.subsingleton_H_of_isZero hb q⟩

end AlgebraicGeometry.IsCurve
