/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningObstruction

/-! # Factoring a principal ideal transition through the structure sheaf

## References

* Stacks Project, Tag 0H3D, the left vertical map in its diagram
* Stacks Project, Tag 0H3D, the map induced by multiplication by g^c
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

/-- A uniform power-torsion bound persists under localization. -/
private theorem principal_localization_kill
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (g : R) (c j : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0)
    (z : S) (hz : algebraMap R S g ^ j * z = 0) :
    algebraMap R S g ^ c * z = 0 := by
  obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj M z
  have hr : algebraMap R S (g ^ j * r) = 0 := by
    rw [map_mul, map_pow, ← hs, ← mul_assoc, hz, zero_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff M S _).mp hr
  have hc : g ^ c * (t * r) = 0 := hkill j (t * r) (by
    simpa only [mul_left_comm] using ht)
  have hcr : algebraMap R S (g ^ c * r) = 0 := by
    apply (IsLocalization.map_eq_zero_iff M S _).mpr
    exact ⟨t, by simpa only [mul_left_comm] using hc⟩
  apply (IsUnit.mul_left_eq_zero (IsLocalization.map_units S s)).mp
  rw [mul_assoc, hs, ← map_pow, ← map_mul]
  exact hcr

/-- Check the power-torsion bound on stalks of an open subscheme of Spec R. -/
private theorem principal_sections_kill
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (c j : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0)
    (U : W.toScheme.Opens) (s : Γ(W.toScheme, U))
    (hs : W.toScheme.presheaf.map (homOfLE le_top).op
      ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ j) * s = 0) :
    W.toScheme.presheaf.map (homOfLE le_top).op
      ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ c) * s = 0 := by
  apply TopCat.Presheaf.section_ext W.toScheme.sheaf U
  intro x hx
  let e := (W.stalkIso x).hom
  apply (ConcreteCategory.bijective_of_isIso e).1
  simp only [map_zero]
  let : Algebra R ((Spec (.of R)).presheaf.stalk x.1) :=
    inferInstanceAs (Algebra R ((structurePresheafInCommRingCat R).stalk x.1))
  have : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk x.1) x.1.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((structurePresheafInCommRingCat R).stalk x.1) x.1.asIdeal)
  let z := e (W.toScheme.presheaf.germ U x hx s)
  have he : e (W.toScheme.presheaf.germ U x hx
      (W.toScheme.presheaf.map (homOfLE le_top).op
        (((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g))) =
      algebraMap R ((Spec (.of R)).presheaf.stalk x.1) g := by
    rw [W.toScheme.presheaf.germ_res_apply]
    change (W.stalkIso x).hom
      (W.toScheme.presheaf.germ ⊤ x trivial
        (W.ι.appTop ((ΓSpecIso (.of R)).inv g))) = _
    erw [← W.ι.germ_stalkMap_apply ⊤ x trivial]
    rw [← W.stalkIso_inv]
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
    rfl
  have hz : algebraMap R ((Spec (.of R)).presheaf.stalk x.1) g ^ j * z = 0 := by
    have hh := congrArg (fun t ↦ e (W.toScheme.presheaf.germ U x hx t)) hs
    simpa only [map_mul, map_pow, he, map_zero, z] using hh
  have hc := principal_localization_kill x.1.asIdeal.primeCompl g c j hkill z hz
  change e (W.toScheme.presheaf.germ U x hx _) = 0
  simpa only [map_mul, map_pow, he, map_zero, z] using hc

/-- Bounded principal torsion lets the inclusion of higher powers factor through O_W. -/
theorem principal_thickening_ideal_factor
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (c n : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0) :
    ∃ d : principalThickeningIdeal R g W (n + c) ⟶
        SheafOfModules.unit W.toScheme.ringCatSheaf,
      d ≫ principalThickeningMultiplication R g W n =
        image.ι (principalThickeningMultiplication R g W (n + c)) := by
  let a : Γ(W.toScheme, ⊤) := ((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g
  let O := SheafOfModules.unit W.toScheme.ringCatSheaf
  let f := principalThickeningMultiplication R g W (n + c)
  let b : O ⟶ O := Modules.smulHom O (a ^ c)
  have hk : kernel.ι f ≫ b = 0 := by
    ext U x
    have hh := congrArg (fun φ ↦ φ.val.app U x) (kernel.condition f)
    simp only [ConcreteCategory.comp_apply, f, principalThickeningMultiplication] at hh
    apply principal_sections_kill R g W c ((n + c) + 1) hkill U.unop ((kernel.ι f).val.app U x)
    exact hh
  refine ⟨(Abelian.coimageIsoImage' f).inv ≫ cokernel.desc (kernel.ι f) b hk, ?_⟩
  apply (cancel_epi (factorThruImage f)).mp
  simp only [← Category.assoc]
  rw [Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc, image.fac]
  change Modules.smulHom O (a ^ c) ≫ Modules.smulHom O (a ^ (n + 1)) =
    Modules.smulHom O (a ^ ((n + c) + 1))
  rw [← Modules.smulHom_mul, ← pow_add]
  congr 2
  omega

end
end AlgebraicGeometry.Scheme
