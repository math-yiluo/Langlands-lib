/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.LocalizationCech.ExtendedLocalizationCechSupplement
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-! # Signed contraction of the sheaf Koszul complex

Source: Stacks Project, Tags 0626, 0663, 0913 and 099H
(blueprint: lem-weil-pbc-localization-koszul-contractions).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section


set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.LocalizationCech

section Generic
variable {D : Type*} [Category D] [Abelian D]
private theorem scalarNat_homology
    (z : 𝟭 D ⟶ 𝟭 D) (K : CochainComplex D ℤ) (μ : End K)
    (hμ : ∀ q, μ.asHom.f q = z.app (K.X q)) (q : ℤ) :
    HomologicalComplex.homologyMap μ.asHom q = z.app (K.homology q) := by
  have hc : HomologicalComplex.cyclesMap μ.asHom q = z.app (K.cycles q) := by
    apply (cancel_mono (K.iCycles q)).1
    rw [HomologicalComplex.cyclesMap_i, hμ]
    exact z.naturality (K.iCycles q)
  apply (cancel_epi (K.homologyπ q)).1
  rw [HomologicalComplex.homologyπ_naturality, hc]
  exact (z.naturality (K.homologyπ q)).symm
end Generic

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionScalarNat
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections) (e : ℕ) :
    𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) ⟶
      𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) where
  app M := ⟨{
    app X := ModuleCat.ofHom
      (LinearMap.lsmul (R.obj.obj X) (M.val.obj X)
        ((show R.obj.obj X from s.val X) ^ e))
    naturality {X Y} f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((show R.obj.obj Y from s.val Y) ^ e) •
          (show M.val.obj Y from M.val.map f x) =
        M.val.map f (((show R.obj.obj X from s.val X) ^ e) • x)
      rw [M.val.map_smul]
      have hs : R.obj.map f (show R.obj.obj X from s.val X) =
          (show R.obj.obj Y from s.val Y) := s.property f
      change ((show R.obj.obj Y from s.val Y) ^ e) •
          (show M.val.obj Y from M.val.map f x) =
        R.obj.map f ((show R.obj.obj X from s.val X) ^ e) •
          (show M.val.obj Y from M.val.map f x)
      rw [map_pow, hs] }⟩
  naturality M N g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((g.val.app X).hom.map_smul ((show R.obj.obj X from s.val X) ^ e) x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sectionScalarNat_unit
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections) (e : ℕ) :
    (sectionScalarNat R s e).app (unit (rings R)) = (scalar R s ^ e).asHom := by
  induction e with
  | zero =>
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro X
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [sectionScalarNat]
  | succ e ih =>
      rw [pow_succ, End.mul_asHom, ← ih]
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro X
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change R.obj.obj X at x
      change ((show R.obj.obj X from s.val X) ^ (e + 1)) * x =
        ((show R.obj.obj X from s.val X) ^ e) *
          (x * (show R.obj.obj X from s.val X))
      rw [pow_succ]
      ring

private theorem span_pow_le_of_generator_powers
    {S : Type*} [CommRing S] {ι : Type*} (s : Finset ι) (f : ι → S)
    (e : ℕ) (A : Ideal S) (h : ∀ j ∈ s, f j ^ e ∈ A) :
    (Ideal.span (f '' (s : Set ι))) ^ (s.card * e + 1) ≤ A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hs : (Ideal.span (f '' (s : Set ι))) ^ (s.card * e + 1) ≤ A :=
      ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk))
    have hexp : (insert j s).card * e + 1 = e + (s.card * e + 1) := by
      rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul]
      omega
    rw [hexp, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
    apply Ideal.sup_pow_add_le_pow_sup_pow.trans
    apply sup_le _ hs
    rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact h j (Finset.mem_insert_self j s)

end SheafOfModules.LocalizationCech
