/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-! # Scalar faithfulness and homology on a geometric point

Source: blueprint lemma-cohomology-projective-line-trace, the geometric Chern component.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option allowUnsafeReducibility true in
attribute [local reducible] ordinaryFiniteDegreeZero ordinaryFiniteLine ordinaryFiniteUnit

private theorem kummer_mono_of_smul_eq_zero
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsSepClosed k]
    {G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : ordinaryFiniteConstant A (Spec (.of k)) ⟶ G)
    (hf : ∀ c : A, c • f = 0 → c = 0) : Mono f := by
  let E := constantSheafEquivalenceOfIsSepClosed A (k := k)
  let S := E.inverse
  let eU : ModuleCat.of A A ≅ S.obj (ordinaryFiniteConstant A (Spec (.of k))) :=
    E.unitIso.app (ModuleCat.of A A)
  have hsmul : ∀ (c : A) x, S.map (c • f) x = c • S.map f x := fun _ _ ↦ rfl
  have hgen : ∀ d : A, eU.hom d = d • eU.hom (1 : A) := fun d ↦ by
    rw [← map_smul, smul_eq_mul, mul_one]
  suffices hinj : Function.Injective (S.map f) from
    Functor.mono_of_mono_map S ((ModuleCat.mono_iff_injective _).2 hinj)
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨c, rfl⟩ : ∃ c₀ : A, eU.hom c₀ = m := ⟨eU.inv m, by simp⟩
  have hc : S.map (c • f) = 0 := by
    ext x
    obtain ⟨d, rfl⟩ : ∃ d₀ : A, eU.hom d₀ = x := ⟨eU.inv x, by simp⟩
    rw [hsmul, hgen d, map_smul, smul_comm, ← map_smul, ← hgen c, hm, smul_zero]
    rfl
  rw [hf c (S.map_injective (by rw [hc, Functor.map_zero]))]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_mono_homology_zero_core
    (A : Type*) [CommRing A]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Linear A C]
    (P : C) [Projective P]
    (hP : ∀ (F : C) (ψ : P ⟶ F), (∀ a : A, a • ψ = 0 → a = 0) → Mono ψ)
    (K : DerivedCategory C) (β : (DerivedCategory.singleFunctor _ 0).obj P ⟶ K)
    (hβ : ∀ a : A,
      (DerivedCategory.singleFunctor _ 0).map (a • 𝟙 P) ≫ β = 0 → a = 0) :
    Mono ((DerivedCategory.homologyFunctor _ 0).map β) := by
  let H := DerivedCategory.homologyFunctor C 0
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app P
  suffices h : Mono (e.inv ≫ H.map β) by
    have heq : H.map β = e.hom ≫ (e.inv ≫ H.map β) := by simp
    rw [heq]
    infer_instance
  refine hP _ _ fun a ha ↦ hβ a ?_
  apply (DerivedCategory.homSingleEquivOfProjective P 0 K).injective
  simp only [DerivedCategory.homSingleEquivOfProjective_apply,
    DerivedCategory.homSingleToHomology, Functor.map_zero, comp_zero]
  change e.inv ≫ H.map ((DerivedCategory.singleFunctor _ 0).map (a • 𝟙 P) ≫ β) = 0
  rw [Functor.map_comp]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.naturality
    (a • 𝟙 P)
  change (a • 𝟙 P) ≫ e.inv =
    e.inv ≫ H.map ((DerivedCategory.singleFunctor _ 0).map (a • 𝟙 P)) at hn
  rw [← Category.assoc, ← hn]
  simpa only [Linear.smul_comp, Category.id_comp, Category.assoc] using ha

/-- A scalar-faithful arrow from the constant unit on a separably closed point
is monic on zeroth homology.
Source: blueprint lemma-cohomology-projective-line-trace, geometric Chern component.
(auxiliary; not a blueprint node).

Proof: the constant module on a separably closed point is projective. The
projective single-object Hom comparison detects the derived arrow on H0. Under
the equivalence with modules, every element of the rank-one source is a scalar
multiple of one. Scalar faithfulness therefore makes the H0 map injective,
which is equivalent to its being monic. This includes the zero ring. -/
theorem ordinaryFiniteUnit_mono_homology_zero
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsSepClosed k]
    {K : DerivedCategoryModule A (Spec (.of k))}
    (β : ordinaryFiniteUnit A (Spec (.of k)) ⟶ K)
    (hβ : ∀ c : A, (DerivedCategory.singleFunctor _ 0).map
      (c • 𝟙 (ordinaryFiniteConstant A (Spec (.of k)))) ≫ β = 0 → c = 0) :
    Mono ((DerivedCategory.homologyFunctor _ 0).map β) := by
  have : Projective (ordinaryFiniteConstant A (Spec (.of k))) :=
    Scheme.projective_constantSheaf_moduleCat_of_iso (Iso.refl (Spec (.of k))) A
  exact kummer_mono_homology_zero_core A (ordinaryFiniteConstant A (Spec (.of k)))
    (fun _ ψ hψ ↦ kummer_mono_of_smul_eq_zero A k ψ hψ) K β hβ

private theorem kummer_isIso_of_mono_card
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsSepClosed k]
    {F G : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)}
    (ψ : F ⟶ G) [Mono ψ]
    [Finite ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj F)]
    [Finite ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj G)]
    (h : Nat.card ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj G) ≤
      Nat.card ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj F)) :
    IsIso ψ := by
  let S := (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse
  have hinj : Function.Injective (S.map ψ) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : IsIso (S.map ψ) :=
    (LinearEquiv.ofBijective (S.map ψ).hom
      (hinj.bijective_of_nat_card_le h)).toModuleIso.isIso_hom
  exact isIso_of_reflects_iso ψ S

private theorem kummer_fibre_source_unit_equiv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsSepClosed k] :
    Nonempty (
      ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj
        ((DerivedCategory.homologyFunctor _ 0).obj
          (ordinaryFiniteUnit A (Spec (.of k))))) ≃ A) := by
  let G := (constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse
  exact ⟨(CategoryTheory.Iso.toLinearEquiv
    (G.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _) ≪≫
      ((constantSheafEquivalenceOfIsSepClosed A (k := k)).unitIso.app
        (ModuleCat.of A A)).symm)).toEquiv⟩

end AlgebraicGeometry.Etale
