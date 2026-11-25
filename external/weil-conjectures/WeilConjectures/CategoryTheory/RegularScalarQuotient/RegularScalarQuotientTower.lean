/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Regular scalar quotient towers

Source: Stacks 099M and 0941, the strict principal quotient construction.
(blueprint: lem-sfb-regular-scalar-quotient-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u r
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RegularScalarQuotient

variable {R : Type r} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (s : R) (V : C)

/-- The ordinary quotient by the nth scalar power, including exponent zero.
Source: Stacks 099M (blueprint: lem-sfb-regular-scalar-quotient-tower). -/
abbrev obj (n : ℕ) : C := cokernel (s ^ n • 𝟙 V)

/-- Higher powers vanish under smaller quotient projections.
Source: Stacks 099M (blueprint: lem-sfb-regular-scalar-quotient-tower). -/
theorem power_zero {n m : ℕ} (h : n ≤ m) :
    (s ^ m • 𝟙 V) ≫ cokernel.π (s ^ n • 𝟙 V) = 0 := by
  rw [show s ^ m = s ^ (m - n) * s ^ n by rw [← pow_add, Nat.sub_add_cancel h],
    ← smul_smul, Linear.smul_comp, cokernel.condition, smul_zero]

/-- The canonical quotient transition.
Source: Stacks 099M (blueprint: lem-sfb-regular-scalar-quotient-tower). -/
def map {n m : ℕ} (h : n ≤ m) : obj s V m ⟶ obj s V n :=
  cokernel.desc _ (cokernel.π _) (power_zero s V h)

/-- The quotient transitions preserve the quotient projections.
Source: Stacks 099M (blueprint: lem-sfb-regular-scalar-quotient-tower). -/
@[reassoc (attr := simp)]
theorem π_map {n m : ℕ} (h : n ≤ m) :
    cokernel.π (s ^ m • 𝟙 V) ≫ map s V h = cokernel.π (s ^ n • 𝟙 V) :=
  cokernel.π_desc _ _ _

/-- Quotient transitions are epimorphisms.
Source: Stacks 099M (blueprint: lem-sfb-regular-scalar-quotient-tower). -/
instance map_epi {n m : ℕ} (h : n ≤ m) : Epi (map s V h) :=
  epi_of_epi_fac (π_map s V h)

/-- All principal quotients with their canonical transitions.
Source: Stacks 099M (blueprint: lem-sfb-regular-scalar-quotient-tower). -/
def tower : ℕᵒᵖ ⥤ C where
  obj n := obj s V n.unop
  map f := map s V (leOfHom f.unop)
  map_id n := by apply coequalizer.hom_ext; simp
  map_comp f g := by apply coequalizer.hom_ext; simp

private theorem annihilated (n : ℕ) : s ^ n • 𝟙 (obj s V n) = 0 := by
  apply (cancel_epi (cokernel.π (s ^ n • 𝟙 V))).1
  simp only [Linear.comp_smul, Category.comp_id, comp_zero]
  simpa only [Linear.smul_comp, Category.id_comp] using cokernel.condition (s ^ n • 𝟙 V)

private theorem map_scalar_zero {n m : ℕ} (h : n ≤ m) :
    (s ^ n • 𝟙 (obj s V m)) ≫ map s V h = 0 := by
  rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id (map s V h),
    ← Linear.comp_smul, annihilated s V n, comp_zero]

private def quotientIsCokernel {n m : ℕ} (h : n ≤ m) :
    IsColimit (CokernelCofork.ofπ (map s V h) (map_scalar_zero s V h)) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro Z f hf
  refine ⟨cokernel.desc (s ^ n • 𝟙 V) (cokernel.π (s ^ m • 𝟙 V) ≫ f) ?_, ?_⟩
  · calc
      _ = cokernel.π (s ^ m • 𝟙 V) ≫ ((s ^ n • 𝟙 (obj s V m)) ≫ f) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
      _ = 0 := by rw [hf, comp_zero]
  · apply coequalizer.hom_ext
    simp

private theorem exact_scalar (a b : ℕ) (hreg : Mono (s ^ b • 𝟙 V)) :
    (ShortComplex.mk (s ^ a • 𝟙 (obj s V (a + b)))
      (s ^ b • 𝟙 (obj s V (a + b))) (by
        rw [Linear.smul_comp, Category.id_comp, smul_smul, ← pow_add, add_comm,
          annihilated])).Exact := by
  apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
  intro A x hx
  obtain ⟨A', p, hp, y, hy⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π (s ^ (a + b) • 𝟙 V)) x
  have hz : (y ≫ (s ^ b • 𝟙 V)) ≫ cokernel.π (s ^ (a + b) • 𝟙 V) = 0 := by
    calc
      _ = (y ≫ cokernel.π (s ^ (a + b) • 𝟙 V)) ≫
          (s ^ b • 𝟙 (obj s V (a + b))) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.comp_id]
      _ = (p ≫ x) ≫ (s ^ b • 𝟙 (obj s V (a + b))) := by rw [hy]
      _ = 0 := by rw [Category.assoc, hx, comp_zero]
  obtain ⟨A'', q, hq, z, hz⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
      (cokernelIsCokernel (s ^ (a + b) • 𝟙 V)) _).1 hz
  have he : q ≫ y = z ≫ (s ^ a • 𝟙 V) := by
    apply (cancel_mono (s ^ b • 𝟙 V)).1
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.comp_id,
      smul_smul, ← pow_add, add_comm] using hz
  refine ⟨A'', q ≫ p, inferInstance, z ≫ cokernel.π (s ^ (a + b) • 𝟙 V), ?_⟩
  change (q ≫ p) ≫ x = (z ≫ cokernel.π _) ≫ (s ^ a • 𝟙 _)
  rw [Category.assoc, hy, ← Category.assoc, he]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.comp_id]

/-- A regular scalar gives a normalized adic tower of ordinary quotient complexes.
Source: Stacks 099M and 0941
(blueprint: lem-sfb-regular-scalar-quotient-tower).
Proof: cancellation of the quotient epimorphism proves scalar annihilation. The
universal property of the two successive cokernels identifies reduction to a
smaller exponent with its ordinary quotient. For exactness, lift an element of
the kernel through the quotient epimorphism after an epimorphic refinement.
Its scalar multiple lifts through the defining scalar map after a second
refinement. Cancel the regular scalar power on the original complex. The lift
is then a multiple of the complementary scalar power, as required. This includes
exponent zero, where the scalar is the identity and the quotient is zero. -/
theorem normalized {B : Type u} [Category.{v} B] [Abelian B] [Linear R B]
    (P : CochainComplex B ℤ) (hP : ∀ n : ℕ, Mono (s ^ n • 𝟙 P)) :
    CochainComplex.IsNormalizedAdicTower s (tower s P) where
  smul_eq_zero := annihilated s P
  quasiIso_cokernelDesc {n m} h := by
    have : IsIso (cokernel.desc (s ^ n • 𝟙 (obj s P m)) (map s P h) (map_scalar_zero s P h)) :=
      by
        let e := (cokernelIsCokernel (s ^ n • 𝟙 (obj s P m))).coconePointUniqueUpToIso
          (quotientIsCokernel s P h)
        have he : cokernel.desc (s ^ n • 𝟙 (obj s P m)) (map s P h)
            (map_scalar_zero s P h) = e.hom := by
          apply coequalizer.hom_ext
          simp only [cokernel.π_desc, e]
          exact ((cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
            (quotientIsCokernel s P h) WalkingParallelPair.one).symm
        rw [he]
        infer_instance
    change QuasiIso (cokernel.desc (s ^ n • 𝟙 (obj s P m))
      (map s P h) (map_scalar_zero s P h))
    infer_instance
  exact_smul a b := exact_scalar s P a b (hP b)

end CategoryTheory.RegularScalarQuotient
