/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.FiniteFreeKernelH1Vanishing
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Finite basic-open covers generate the unit ideal under ideal H¹ vanishing

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
last two paragraphs of the proof (blueprint: lem-pqf-h1-finite-basic-cover-unit-ideal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem globalSections_surjective_of_kernel_h1_zero (X : Scheme.{u})
    {M N : X.Modules} (p : M ⟶ N) [Epi p]
    (hK : Subsingleton
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (kernel p))) :
    Function.Surjective (Scheme.Modules.Hom.app p ⊤) := by
  let F := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
  obtain ⟨δ, _, hδ⟩ := hS.exists_rightDerived_full_long_exact F
  obtain ⟨_, w₁, _, he, _⟩ := hδ 0
  have hz : δ 0 = 0 := by
    exact (ModuleCat.isZero_of_subsingleton
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (kernel p))).eq_of_tgt _ _
  have : Epi ((F.rightDerived 0).map p) := he.epi_f hz
  have heq : F.map p =
      (F.rightDerivedZeroIsoSelf.app M).inv ≫ (F.rightDerived 0).map p ≫
        (F.rightDerivedZeroIsoSelf.app N).hom := by
    rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf p]
    simp
  have : Epi (F.map p) := by rw [heq]; infer_instance
  exact (ModuleCat.epi_iff_surjective (F.map p)).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Ideal H¹ vanishing makes any finite basic-open covering family generate one.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
last two paragraphs of the proof (blueprint: lem-pqf-h1-finite-basic-cover-unit-ideal).

Proof: Enumerate the finite set s by f₁,...,fₙ. The map O_X^n → O_X sending
eᵢ to fᵢ is surjective on stalks, since at every point one fᵢ is a unit.
Let F be its quasi-coherent kernel. Put Fᵢ = F ∩ O_X^i, using the first i
summands. Projection onto the i-th coordinate identifies Fᵢ/Fᵢ₋₁ with a
quasi-coherent ideal subsheaf of O_X. Begin with F₀ = 0. The exact segment
H¹(Fᵢ₋₁) → H¹(Fᵢ) → H¹(Fᵢ/Fᵢ₋₁), with both outer terms zero, proves
H¹(Fᵢ) = 0 by induction, hence H¹(F) = 0. The initial long exact segment
for 0 → F → O_X^n → O_X → 0 makes the map on global sections surjective.
A preimage of 1 gives coefficients aᵢ with sum aᵢ fᵢ = 1. Therefore
1 belongs to Ideal.span s and that ideal is the whole ring.
For the empty covering family, X is empty and its section ring is the zero
ring; the same conclusion holds. The basic opens need not be affine. -/
theorem span_eq_top_of_finite_basicOpen_cover_of_h1_ideal_zero (X : Scheme.{u})
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules))
    (s : Set Γ(X, ⊤)) (hs : s.Finite)
    (hcover : ∀ x : X, ∃ f ∈ s, x ∈ X.basicOpen f) :
    Ideal.span s = ⊤ := by
  classical
  let : Fintype s := hs.fintype
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let σ : s → O.sections := fun f ↦ PresheafOfModules.sectionsMk
    (fun U ↦ X.presheaf.map (homOfLE le_top).op f.val)
    (fun {_ _} g ↦ by
      change X.presheaf.map g (X.presheaf.map _ f.val) = _
      rw [← Functor.map_comp_apply]; congr 1)
  let p : SheafOfModules.free (R := X.ringCatSheaf) s ⟶ O := O.freeHomEquiv.symm σ
  have hp : Epi p := by
    apply (Scheme.Modules.generating_sections_iff_stalk_span X O σ).mpr
    intro x
    obtain ⟨f, hf, hx⟩ := hcover x
    have hu := (X.mem_basicOpen_top f x).mp hx
    apply top_unique
    intro z _
    obtain ⟨v, hv⟩ := hu
    let e := (TopCat.Presheaf.germ O.val.presheaf ⊤ x trivial) (1 : Γ(X, ⊤))
    have hg : (TopCat.Presheaf.germ O.val.presheaf ⊤ x trivial)
        ((σ ⟨f, hf⟩).val (op ⊤)) = X.presheaf.germ ⊤ x trivial f • e := by
      change (TopCat.Presheaf.germ O.val.presheaf ⊤ x trivial)
        (X.presheaf.map (homOfLE le_top).op f) = _
      simp only [homOfLE_leOfHom, homOfLE_refl, op_id]
      simpa [e] using (PresheafOfModules.germ_smul (R := X.presheaf) O.val x ⊤ trivial
        f (1 : Γ(X, ⊤)))
    obtain ⟨U, hxU, t, rfl⟩ := O.presheaf.exists_germ_eq z
    have he : (TopCat.Presheaf.germ O.val.presheaf U x hxU) (1 : Γ(X, U)) = e := by
      have hmap : O.val.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
          (1 : Γ(X, ⊤)) = (1 : Γ(X, U)) := by
        change X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op 1 = 1
        exact map_one (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom
      have hr := TopCat.Presheaf.germ_res_apply O.val.presheaf
        (homOfLE le_top) x hxU (1 : Γ(X, ⊤))
      erw [hmap] at hr
      exact hr
    have hz : (TopCat.Presheaf.germ O.val.presheaf U x hxU) t =
        (X.presheaf.germ U x hxU t * ↑v⁻¹) •
        ((TopCat.Presheaf.germ O.val.presheaf ⊤ x trivial)
          ((σ ⟨f, hf⟩).val (op ⊤))) := by
      rw [hg, ← hv, smul_smul]
      simp only [mul_assoc, Units.inv_mul, mul_one]
      rw [← he]
      simpa using (PresheafOfModules.germ_smul (R := X.presheaf) O.val x U hxU
        t (1 : Γ(X, U)))
    change (TopCat.Presheaf.germ O.val.presheaf U x hxU) t ∈ _
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (⟨f, hf⟩ : s)))
  let : Epi p := hp
  obtain ⟨a, ha⟩ := globalSections_surjective_of_kernel_h1_zero X p
    (finite_free_kernel_h1_zero X hI p) (1 : Γ(X, ⊤))
  apply Ideal.eq_top_of_isUnit_mem (I := Ideal.span s) (x := 1)
  · rw [← ha]
    obtain ⟨c, rfl⟩ := (Scheme.Modules.freeSectionsEquiv (X := X) s).symm.surjective a
    change Scheme.Modules.Hom.app p ⊤
      (∑ i : s, Scheme.Modules.Hom.app (SheafOfModules.ιFree i) ⊤ (c i)) ∈ Ideal.span s
    rw [map_sum]
    apply Submodule.sum_mem
    intro i _
    have hi1 : (O.unitHomEquiv (SheafOfModules.ιFree i ≫ p)).val (op ⊤) =
        (i.val : Γ(X, ⊤)) := by
      change (O.freeHomEquiv p i).val (op ⊤) = _
      simp only [p, Equiv.apply_symm_apply]
      change X.presheaf.map (homOfLE le_top).op i.val = i.val
      simp
    have hi : Scheme.Modules.Hom.app (SheafOfModules.ιFree i ≫ p) ⊤ (c i) =
        c i * i.val := by
      rw [Scheme.Modules.unit_hom_app_top]
      change c i * (show Γ(X, ⊤) from
        (O.unitHomEquiv (SheafOfModules.ιFree i ≫ p)).val (op ⊤)) = _
      rw [hi1]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hi]
    exact Ideal.mul_mem_left (Ideal.span s) (c i) (Ideal.subset_span i.property)
  · exact isUnit_one

end AlgebraicGeometry
