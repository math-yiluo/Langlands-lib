/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PrincipalIdealDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingle

/-!
# Bounded complexes over a field split

Over a field `F`, every object of `Dᵇ_fd(F)` is a finite direct sum of shifts of `F[0]`: the
truncation triangles split, since `F`-modules are projective. We record this as a dévissage
principle (`DerivedCategory.prop_of_boundedFiniteCohomology_of_field`): a property of objects of
`D(F)`, closed under isomorphisms, binary biproducts and shifts, satisfied by zero objects and by
`F[0]`, holds on `Dᵇ_fd(F)`. Unlike `DerivedCategory.prop_of_boundedFiniteCohomology`, no closure
under extensions is required.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {F : Type (u + 1)} [Field F]
  (Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} F))) [Q.IsClosedUnderIsomorphisms]
  (h₀ : ∀ X, IsZero X → Q X) (hb : ∀ X Y, Q X → Q Y → Q (X ⊞ Y))
  (hs : ∀ X (n : ℤ), Q X → Q (X⟦n⟧))

include h₀ hb in
private lemma prop_single_pi
    (hF : Q ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F))) (n : ℕ) :
    Q ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F (Fin n → F))) := by
  induction n with
  | zero =>
    refine h₀ _ (Functor.map_isZero _ ?_)
    rw [ModuleCat.isZero_iff_subsingleton]
    infer_instance
  | succ n ih =>
    have := preservesBinaryBiproducts_of_preservesBiproducts
      (singleFunctor (ModuleCat.{u + 1} F) 0)
    exact Q.prop_of_iso ((singleFunctor _ 0).mapIso (ModuleCat.biprodIsoProd _ _ ≪≫
      (Fin.consLinearEquiv F (fun _ : Fin (n + 1) ↦ F)).toModuleIso))
      (Q.prop_of_iso ((singleFunctor _ 0).mapBiprod _ _).symm (hb _ _ hF ih))

include h₀ hb hs in
private lemma prop_single (hF : Q ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)))
    (b : ℤ) (M : ModuleCat.{u + 1} F) [Module.Finite F M] :
    Q ((singleFunctor (ModuleCat.{u + 1} F) b).obj M) := by
  have h := Q.prop_of_iso ((singleFunctor _ 0).mapIso
    (Module.finBasis F M).equivFun.toModuleIso.symm) (prop_single_pi Q h₀ hb hF _)
  exact Q.prop_of_iso (((singleFunctors (ModuleCat.{u + 1} F)).shiftIso (-b) b 0 (by lia)).app M)
    (hs _ _ h)

/-- Morphisms `M[-b] ⟶ Z` vanish when `Hᵇ(Z) = 0`, over a field. -/
private lemma eq_zero_of_singleFunctor (b : ℤ) (M : ModuleCat.{u + 1} F)
    (Z : DerivedCategory (ModuleCat.{u + 1} F))
    (hZ : IsZero ((homologyFunctor (ModuleCat.{u + 1} F) b).obj Z))
    (g : (singleFunctor (ModuleCat.{u + 1} F) b).obj M ⟶ Z) : g = 0 := by
  have : Projective M := inferInstanceAs (Projective (ModuleCat.of F M))
  apply (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} F)) b).map_injective
  rw [Functor.map_zero, ← cancel_epi
    (((singleFunctors (ModuleCat.{u + 1} F)).shiftIso b 0 b (by lia)).inv.app M), Limits.comp_zero]
  refine eq_zero_of_isZero_homology_zero M _ ?_ _
  exact hZ.of_iso (((homologyFunctor (ModuleCat.{u + 1} F) 0).shiftIso b 0 b (by lia)).app Z)

include h₀ hb hs in
private lemma prop_of_isGE_of_isLE_field
    (hF : Q ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F))) (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory (ModuleCat.{u + 1} F)), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, Module.Finite F ((homologyFunctor (ModuleCat.{u + 1} F) q).obj M)) → Q M := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact h₀ M (TStructure.t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor _ (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀' : IsZero ((homologyFunctor _ b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀' h₁
    have : Module.Finite F ((homologyFunctor (ModuleCat.{u + 1} F) b).obj
        ((TStructure.t.triangleLTGE b).obj M).obj₂) := hM b
    have hY : Module.Finite F Y := Module.Finite.equiv
      (asIso ((homologyFunctor _ b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor _ b).mapIso e ≪≫
          (singleFunctorCompHomologyFunctorIso _ b).app Y).toLinearEquiv
    have h₃ : Q ((TStructure.t.triangleLTGE b).obj M).obj₃ :=
      Q.prop_of_iso e.symm (prop_single Q h₀ hb hs hF b Y)
    have hT₁ : Q ((TStructure.t.triangleLTGE b).obj M).obj₁ := by
      refine ih a _ ?_ ?_ fun q ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · by_cases hq : q < b
        · have : IsIso ((homologyFunctor _ q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
            isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
              (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
          have : Module.Finite F ((homologyFunctor (ModuleCat.{u + 1} F) q).obj
              ((TStructure.t.triangleLTGE b).obj M).obj₂) := hM q
          exact Module.Finite.equiv
            (asIso ((homologyFunctor _ q).map
              ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm.toLinearEquiv
        · have : Subsingleton ((homologyFunctor (ModuleCat.{u + 1} F) q).obj
              ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
            ModuleCat.isZero_iff_subsingleton.1 (isZero_of_isLE _ (b - 1) _ (by lia))
          infer_instance
    have hmor₃ : ((TStructure.t.triangleLTGE b).obj M).mor₃ = 0 := by
      rw [← cancel_epi e.inv, Limits.comp_zero]
      have : ((TStructure.t.triangleLTGE b).obj M).obj₁.IsLE (b - 1) :=
        TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      have : (((TStructure.t.triangleLTGE b).obj M).obj₁⟦(1 : ℤ)⟧).IsLE (b - 2) :=
        TStructure.t.isLE_shift _ (b - 1) 1 (b - 2)
      refine eq_zero_of_singleFunctor b Y _ ?_ _
      exact (isZero_of_isLE (((TStructure.t.triangleLTGE b).obj M).obj₁⟦(1 : ℤ)⟧) (b - 2) b
        (by lia))
    obtain ⟨e', -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT hmor₃
    exact Q.prop_of_iso e'.symm (hb _ _ hT₁ h₃)

include h₀ hb hs in
/-- Over a field `F`, a property of objects of `D(F)` closed under isomorphisms, binary
biproducts and shifts, and satisfied by zero objects and `F[0]`, holds on `Dᵇ_fd(F)`. -/
theorem prop_of_boundedFiniteCohomology_of_field
    (hF : Q ((singleFunctor (ModuleCat.{u + 1} F) 0).obj (ModuleCat.of F F)))
    {M : DerivedCategory (ModuleCat.{u + 1} F)} (hM : boundedFiniteCohomology F M) : Q M := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb'⟩⟩, hfin⟩ := hM
  have : M.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le M b _ (by lia)
  exact prop_of_isGE_of_isLE_field Q h₀ hb hs hF (b - a + 1).toNat a M ha this hfin

end DerivedCategory
