/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # CoherentFormalModulesAffineQuotient

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem scalar_zero_of_product_zero {X : Scheme.{u}} {K F : X.Modules}
    (ι : K ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (r : Γ(X, U)) (x : Γ(F, U))
    (hr : r ∈ Set.range (ι.app U))
    (hz : IsZero (Scheme.idealModuleProduct ι F)) : r • x = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := ι ▷ F ≫ (λ_ F).hom
  have ha : a = 0 := by
    rw [← image.fac a]
    have hi : image.ι a = 0 := hz.eq_zero_of_src _
    rw [hi, comp_zero]
  obtain ⟨t, ht⟩ := hr
  have h := congrArg (fun f ↦ f.app U (Scheme.Modules.tmulSection t x)) ha
  change (λ_ F).hom.app U ((ι ▷ F).app U (Scheme.Modules.tmulSection t x)) = 0 at h
  rw [Scheme.Modules.whiskerRight_app_tmulSection,
    Scheme.Modules.leftUnitor_hom_app_tmulSection'] at h
  exact ht ▸ h

private theorem finite_of_completion_generators
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (k : ℕ)
    (M : Type u) [AddCommGroup M] [Module (AdicCompletion I A) M]
    [Module A M] [IsScalarTower A (AdicCompletion I A) M]
    [Module.Finite (AdicCompletion I A) M]
    (P : Type u) [AddCommGroup P] [Module A P]
    (q : M →ₗ[A] P) (hq : Function.Surjective q)
    (hz : ∀ a ∈ I ^ k, ∀ x : M, q (a • x) = 0) : Module.Finite A P := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule (AdicCompletion I A) M).FG)
  have hzero (c : AdicCompletion I A) (hc : c ∈ I ^ k •
      (⊤ : Submodule A (AdicCompletion I A))) (x : M) : q (c • x) = 0 := by
    refine Submodule.smul_induction_on hc (fun a ha b _ ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [smul_assoc]
      exact hz a ha (b • x)
    · simp only [add_smul, map_add, ha, hb, add_zero]
  refine ⟨Submodule.fg_def.mpr ⟨q '' (s : Set M), s.finite_toSet.image q, ?_⟩⟩
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨x, rfl⟩ := hq y
  have hx : x ∈ Submodule.span (AdicCompletion I A) (s : Set M) := by
    rw [hs]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul b x _ ih =>
    obtain ⟨a, ha⟩ := (I ^ k • (⊤ : Submodule A A)).mkQ_surjective
      (AdicCompletion.eval I A k b)
    have hd : b - AdicCompletion.of I A a ∈
        I ^ k • (⊤ : Submodule A (AdicCompletion I A)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing]
      change AdicCompletion.eval I A k (b - AdicCompletion.of I A a) = 0
      rw [map_sub, AdicCompletion.eval_of, ha, sub_self]
    have he : q (b • x) = a • q x := by
      have hh := hzero _ hd x
      rw [sub_smul, map_sub, sub_eq_zero] at hh
      rw [hh]
      change q ((algebraMap A (AdicCompletion I A) a) • x) = _
      rw [algebraMap_smul, q.map_smul]
    rw [he]
    exact Submodule.smul_mem _ a ih

set_option backward.isDefEq.respectTransparency false in
/-- Quotient systems of finite completed modules satisfy the coherent formal conditions.
Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof reduction to module
systems; Algebra 05GG (completion modulo an ideal power), and Schemes 01I7/01IB.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-quotient).

Proof: Write B for the completion. Since A is Noetherian, I is finitely generated and
B/I^(n+1)B = A/I^(n+1). For finite B-module N, reducing a finite generating family
shows N/I^(n+1)N is finite over A/I^(n+1), hence over A. Affine tilde is exact and
identifies ideal products and their cokernels with module ideal products and quotients.
Consequently the nth sheaf in the displayed completion is canonically tilde of this
finite A-module. It is quasi-coherent of finite type, hence coherent on Spec A.
Multiplication by I^(n+1) on this quotient is zero, giving the annihilation condition.
For successive levels, quotienting N/I^(n+2)N by I^(n+1) gives N/I^(n+1)N because
I^(n+2)N is contained in I^(n+1)N. Applying tilde and the cokernel comparison gives
the required quotient isomorphism. Its composite with the projection is the canonical
reduction map, which is exactly formalCompletionFunctor's transition. These are the
three clauses of IsCoherentFormalModule. -/
theorem coherentFormalModules_affine_quotient_coherent
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (N : ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N)) :
    IsCoherentFormalModule J ((ObjectProperty.ι
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ⋙
      tilde.functor (CommRingCat.of A) ⋙ formalCompletionFunctor J).obj N) := by
  let F := (tilde.functor (CommRingCat.of A)).obj
    ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj)
  change IsCoherentFormalModule J (formalCompletionSystem J F)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change RingedSpace.IsCoherent _ (formalModuleQuotient J (n + 1) F)
    have : F.IsQuasicoherent := by
      exact inferInstanceAs (tilde.{u} (R := CommRingCat.of A)
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          N.obj)).IsQuasicoherent
    have := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J F).2.2.1
      (n + 1) (Nat.succ_pos n)
    have := idealModuleProduct_quasicoherent
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 F
    have := Scheme.Modules.isQuasicoherent_cokernel
      (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 F)
    apply (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mpr
    refine ⟨by assumption, ?_⟩
    let M : ModuleCat.{u} (CommRingCat.of A) :=
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N.obj
    let Q := formalModuleQuotient J (n + 1) F
    have : Q.IsQuasicoherent := by
      dsimp only [Q, formalModuleQuotient]
      infer_instance
    let π := formalModuleQuotientπ J (n + 1) F
    let q : M ⟶ (moduleSpecΓFunctor (R := CommRingCat.of A)).obj Q :=
      (tilde.isoTop (R := CommRingCat.of A) M).hom ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map π
    let U : (Spec (CommRingCat.of A)).affineOpens :=
      ⟨⊤, isAffineOpen_top _⟩
    have hsurj : Function.Surjective q := by
      have hp := (Scheme.Modules.quasiCoherent_cokernel_image
        (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 F)
        ).2.2.2.2.2.2.2.2 U
      exact hp.2.1.comp ((tilde.isoTop (R := CommRingCat.of A) M).toLinearEquiv.surjective)
    have hz : ∀ a ∈ I ^ (n + 1), ∀ x : M, q (a • x) = 0 := by
      intro a ha x
      rw [q.hom.map_smul]
      let r : Γ(Spec (CommRingCat.of A), ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv a
      have hr : r ∈ J.ideal U ^ (n + 1) := by
        rw [hJ, Scheme.IdealSheafData.ideal_top_ofIdealTop, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ha
      have hp := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J F
        ).2.2.2.1 U).2.2.2 (n + 1) (Nat.succ_pos n)
      have hrange : r ∈ Set.range
          ((Scheme.idealSheafPower J.toModulesι (n + 1)).2.app ⊤) := by
        rw [hp]
        exact hr
      have hzero := idealModuleProduct_quotient_zero (F := F)
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2
      have hh := scalar_zero_of_product_zero
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 ⊤ r (q x) hrange hzero
      exact (Scheme.Modules.smul_top_eq Q a (q x)).trans hh
    have hfinite : Module.Finite A ((moduleSpecΓFunctor
        (R := CommRingCat.of A)).obj Q) := by
      let : Module (AdicCompletion I A) M := N.obj.isModule
      have : IsScalarTower A (AdicCompletion I A) M :=
        IsScalarTower.of_algebraMap_smul (fun a x ↦
          (ModuleCat.restrictScalars.smul_def (algebraMap A (AdicCompletion I A))
            a x).symm)
      have : Module.Finite (AdicCompletion I A) M := N.property
      exact finite_of_completion_generators A I (n + 1) M _ q.hom hsurj hz
    let : Module A Γ(Q, ⊤) := inferInstanceAs
      (Module A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj Q))
    let : Algebra A Γ(Spec (CommRingCat.of A), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toAlgebra
    have : IsScalarTower A Γ(Spec (CommRingCat.of A), ⊤) Γ(Q, ⊤) :=
      IsScalarTower.of_algebraMap_smul (fun a x ↦
        (Scheme.Modules.smul_top_eq Q a x).symm)
    have : Module.Finite A Γ(Q, ⊤) := hfinite
    have : Module.Finite Γ(Spec (CommRingCat.of A), ⊤) Γ(Q, ⊤) :=
      Module.Finite.of_restrictScalars_finite A _ _
    exact ((Scheme.Modules.quasicoherent_finite_type_affine _).2 Q inferInstance).2.1
      PUnit.{u + 1} (fun _ ↦ ⊤) (by simp) (fun _ ↦ isAffineOpen_top _)
      (fun _ ↦ inferInstance) |>.1
  · intro n
    exact idealModuleProduct_quotient_zero (Scheme.idealSheafPower J.toModulesι (n + 1)).2
  · intro n
    exact formalModuleQuotient_iterated J F (Nat.le_succ (n + 1))

/-- The canonical quotient functor, lifted to coherent formal systems.
Its objects and maps are the existing sheaf quotient construction; only the proof of
membership in the full subcategory uses the preceding theorem.
Source: Stacks Project, Lemma 087W (blueprint:
lem-weil-pbc-coherent-formal-modules-affine-quotient). 
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-quotient)
-/
noncomputable def coherentFormalModules_affine_quotientFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⥤
      CoherentFormalModule (Spec (CommRingCat.of A)) J :=
  (IsCoherentFormalModule J).lift
    (ObjectProperty.ι
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ⋙
      tilde.functor (CommRingCat.of A) ⋙ formalCompletionFunctor J)
    (coherentFormalModules_affine_quotient_coherent A I J hJ)

end

end AlgebraicGeometry
