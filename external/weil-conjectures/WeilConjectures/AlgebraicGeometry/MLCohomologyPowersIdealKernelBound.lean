/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealTransitionMaps
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealImageBound
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Cohomology reductions: KernelBound
Source: Stacks Project, Lemma 02OB. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Proof: form the short exact sequence 0 -> J^n F -> F -> F/J^n F -> 0,
where J is the extended ideal. The category of scheme modules has enough injectives;
the cohomological delta-functor identifies the kernel of reduction with the image of
H^p(J^n F) -> H^p(F). Apply cohomology_powers_ideal_image_bound in degree p
with target exponent zero. It bounds the image in H^p(J^0 F) by I^(n-c) times
that module for n >= c. The transition factorization identifies the inclusion
into F with the transition to J^0 F followed by its inclusion into F. Mapping
this bound along the latter A-linear map gives I^(n-c) H^p(F).
Restriction of scalars preserves exactness. Only the image estimate is used.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OB,
part (1) (blueprint: ml-cohomology-powers-ideal-kernel-bound). -/
theorem ml_cohomology_powers_ideal_kernel_bound
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ c : ℕ,
      (∀ n : ℕ, 1 ≤ n → c ≤ n →
        LinearMap.ker (((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f) n F))).hom) ≤
          I ^ (n - c) • (⊤ : Submodule A
            ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
              ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)))) := by
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f
  let H := RingedSpace.moduleCohomology X.toRingedSpace p
  let R := ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
  obtain ⟨i, hi⟩ := cohomology_powers_ideal_transition_maps J F
  obtain ⟨c, hc⟩ := cohomology_powers_ideal_image_bound A I f J rfl F hF p i hi
  have himage := hc c (le_refl c)
  obtain ⟨G, hG⟩ := (sheafCohomologyAndHigherDirectImages.{u, u + 1, u + 1} X).1
  refine ⟨c, ?_⟩
  intro n _hn hcn
  let a := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F
  have : Mono a := by
    dsimp [a, Scheme.idealModuleProductι]
    infer_instance
  let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
  have he := G.exact_middle S hS p
  rw [hG] at he
  obtain ⟨hz, hexact⟩ := he
  have hker := (ModuleCat.restrictScalars_map_exact
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom _ hexact).moduleCat_range_eq_ker
  change LinearMap.range (R.map (H.map a)).hom =
    LinearMap.ker (R.map (H.map (formalModuleQuotientπ J n F))).hom at hker
  change LinearMap.ker (R.map (H.map (formalModuleQuotientπ J n F))).hom ≤ _
  rw [← hker]
  have hb := himage 0 n (by simpa using hcn)
  change LinearMap.range (R.map (H.map (i (0 + n) 0 (Nat.zero_le (0 + n))))).hom ≤
    I ^ (n - (c - 0)) • ⊤ at hb
  rw [Nat.zero_add, Nat.sub_zero] at hb
  have ha : R.map (H.map a) =
      R.map (H.map (i n 0 (Nat.zero_le n))) ≫
        R.map (H.map (Scheme.idealModuleProductι
          (Scheme.idealSheafPower J.toModulesι 0).2 F)) := by
    rw [← R.map_comp, ← H.map_comp, hi]
  rw [ha, ModuleCat.hom_comp, LinearMap.range_comp]
  let b := (R.map (H.map (Scheme.idealModuleProductι
    (Scheme.idealSheafPower J.toModulesι 0).2 F))).hom
  calc
    _ ≤ Submodule.map b (I ^ (n - c) • ⊤) := Submodule.map_mono hb
    _ = I ^ (n - c) • (⊤ : Submodule A _).map b := Submodule.map_smul'' _ _ _
    _ ≤ I ^ (n - c) • ⊤ := smul_mono_right _ le_top

end AlgebraicGeometry
