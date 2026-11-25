/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedCompletionDiagram

/-! # Section presentation of the embedded first residue maps

## References

* Stacks Project, Tag 093M
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallMap

attribute [local irreducible] ConstantCompletion.completed

section Transport
universe v

private theorem principal_kernel_transport
    {R S R' S' : Type v} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (q : R →+* S) (p : R' →+* S') (a : R ≃+* R') (c : S ≃+* S')
    (h : ∀ x, c (q x) = p (a x)) (t : R')
    (hk : RingHom.ker p = Ideal.span {t}) :
    RingHom.ker q = Ideal.span {a.symm t} := by
  ext x
  change q x = 0 ↔ _
  rw [← c.map_eq_zero_iff, h]
  change a x ∈ RingHom.ker p ↔ _
  rw [hk, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨a.symm y, ?_⟩
    exact a.injective (by simpa only [map_mul, a.apply_symm_apply] using hy)
  · rintro ⟨y, hy⟩
    refine ⟨a y, ?_⟩
    simpa only [map_mul, a.apply_symm_apply] using congrArg a hy

private theorem iso_square_surjective
    {R S R' S' : Type v} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (q : R →+* S) (p : R' →+* S') (a : R ≃+* R') (c : S ≃+* S')
    (h : ∀ x, c (q x) = p (a x)) (hp : Function.Surjective p) :
    Function.Surjective q := by
  intro y
  obtain ⟨x, hx⟩ := hp (c y)
  refine ⟨a.symm x, c.injective ?_⟩
  rw [h, a.apply_symm_apply, hx]

private def section_pull_iso
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{v}} (a : R ≅ S)
    (s : (S.obj ⋙ forget CommRingCat).sections) :
    (R.obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ a.inv.hom.app U (s.val U), fun f ↦ by
    change R.obj.map f (a.inv.hom.app _ (s.val _)) = _
    rw [← ConcreteCategory.comp_apply, ← a.inv.hom.naturality]
    change a.inv.hom.app _ (S.obj.map f (s.val _)) = _
    exact congrArg (a.inv.hom.app _) (s.property f)⟩

private def section_ring_equiv
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{v}} (a : R ≅ S) (U : Cᵒᵖ) :
    R.obj.obj U ≃+* S.obj.obj U :=
  (((sheafToPresheaf J CommRingCat.{v}) ⋙
    (CategoryTheory.evaluation _ _).obj U).mapIso a).commRingCatIsoToRingEquiv

private theorem span_principal_images
    {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (t : A) (ht : Ideal.span {t} = I) :
    Ideal.span (Set.range (fun x : I ↦ f x)) = Ideal.span {f t} := by
  subst I
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp x.property
    change f (x : A) ∈ Ideal.span {f t}
    rw [hy, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.subset_span ⟨⟨t, Ideal.subset_span (Set.mem_singleton _)⟩, rfl⟩

private theorem principal_completion_kernels
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsNoetherianRing A] (t : A) (U : C) :
    Function.Surjective ((ConstantCompletion.quotient J A (Ideal.span {t}) 0).hom.app
      (op U)) ∧
    RingHom.ker ((ConstantCompletion.quotient J A (Ideal.span {t}) 0).hom.app
      (op U)).hom = Ideal.span {(ConstantCompletion.constantSection (J := J) t).val (op U)} ∧
    RingHom.ker ((ConstantCompletion.projection J A (Ideal.span {t}) 0).hom.app
      (op U)).hom = Ideal.span {(ConstantCompletion.algebraSection
        (ConstantCompletion.coefficientMap J A (Ideal.span {t})) t).val (op U)} := by
  obtain ⟨_, hp, hq⟩ := ConstantCompletion.flat_and_quotients J A (Ideal.span {t})
  refine ⟨(hq 0 U).1, ?_, ?_⟩
  · rw [(hq 0 U).2]
    dsimp only [ConstantCompletion.constantSection, CommRingCat.commRingObj]
    let f : A →+* (ConstantCompletion.constant J A).obj.obj (op U) :=
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
    exact span_principal_images f ((Ideal.span {t}) ^ (0 + 1)) t
      (by simp only [Nat.zero_add, pow_one])
  · rw [(hp 0 U).2]
    dsimp only [ConstantCompletion.algebraSection, ConstantCompletion.constantSection,
      CommRingCat.commRingObj]
    let f : A →+* (ConstantCompletion.completed J A (Ideal.span {t})).obj.obj (op U) :=
      ((ConstantCompletion.coefficientMap J A (Ideal.span {t})).hom.app (op U)).hom.comp
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
    exact span_principal_images f ((Ideal.span {t}) ^ (0 + 1)) t
      (by simp only [Nat.zero_add, pow_one])

private theorem residue_sections_of_completion
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsNoetherianRing A] (t : A)
    {R B S T : Sheaf J CommRingCat.{v}}
    (φ : R ⟶ B) (q : R ⟶ S) (qB : B ⟶ T)
    (a : R ≅ ConstantCompletion.constant J A)
    (b : B ≅ ConstantCompletion.completed J A (Ideal.span {t}))
    (c : S ≅ ConstantCompletion.finite J A (Ideal.span {t}) 0)
    (d : T ≅ ConstantCompletion.finite J A (Ideal.span {t}) 0)
    (hφ : φ ≫ b.hom = a.hom ≫ ConstantCompletion.coefficientMap J A (Ideal.span {t}))
    (hq : q ≫ c.hom = a.hom ≫ ConstantCompletion.quotient J A (Ideal.span {t}) 0)
    (hp : qB ≫ d.hom = b.hom ≫ ConstantCompletion.projection J A (Ideal.span {t}) 0) :
    ∃ (e : S ≅ T) (r : (R.obj ⋙ forget CommRingCat).sections),
      Presheaf.IsLocallySurjective J q.hom ∧
      φ ≫ qB = q ≫ e.hom ∧
      (∀ U : C, RingHom.ker (q.hom.app (op U)).hom = Ideal.span {r.val (op U)}) ∧
      (∀ U : C, RingHom.ker (qB.hom.app (op U)).hom =
        Ideal.span {φ.hom.app (op U) (r.val (op U))}) := by
  let I : Ideal A := Ideal.span {t}
  let r := section_pull_iso a (ConstantCompletion.constantSection (J := J) t)
  have hφ' (U : Cᵒᵖ) (x : R.obj.obj U) :
      b.hom.hom.app U (φ.hom.app U x) =
        (ConstantCompletion.coefficientMap J A I).hom.app U (a.hom.hom.app U x) :=
    congrArg (fun f : R ⟶ ConstantCompletion.completed J A I ↦ f.hom.app U x) hφ
  have hq' (U : Cᵒᵖ) (x : R.obj.obj U) :=
    congrArg (fun f : R ⟶ ConstantCompletion.finite J A I 0 ↦ f.hom.app U x) hq
  have hp' (U : Cᵒᵖ) (x : B.obj.obj U) :=
    congrArg (fun f : B ⟶ ConstantCompletion.finite J A I 0 ↦ f.hom.app U x) hp
  have hker (U : C) := principal_completion_kernels J A t U
  refine ⟨c ≪≫ d.symm, r, ?_, ?_, ?_, ?_⟩
  · apply Presheaf.isLocallySurjective_of_surjective
    intro U
    exact iso_square_surjective (q.hom.app U).hom
      ((ConstantCompletion.quotient J A I 0).hom.app U).hom
      (section_ring_equiv a U) (section_ring_equiv c U) (hq' U) (hker U.unop).1
  · apply (cancel_mono d.hom).mp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [hp, ← Category.assoc, hφ, Category.assoc]
    have hc : ConstantCompletion.coefficientMap J A I ≫
        ConstantCompletion.projection J A I 0 = ConstantCompletion.quotient J A I 0 := by
      exact limit.lift_π (ConstantCompletion.quotientCone J A I) (op 0)
    rw [hc]
    exact hq.symm
  · intro U
    exact principal_kernel_transport (q.hom.app (op U)).hom
      ((ConstantCompletion.quotient J A I 0).hom.app (op U)).hom
      (section_ring_equiv a (op U)) (section_ring_equiv c (op U)) (hq' (op U))
      _ (hker U).2.1
  · intro U
    have hk := principal_kernel_transport (qB.hom.app (op U)).hom
      ((ConstantCompletion.projection J A I 0).hom.app (op U)).hom
      (section_ring_equiv b (op U)) (section_ring_equiv d (op U)) (hp' (op U))
      _ (hker U).2.2
    rw [hk]
    congr 1
    apply congrArg Set.singleton
    apply (section_ring_equiv b (op U)).injective
    rw [RingEquiv.apply_symm_apply]
    change (ConstantCompletion.algebraSection
      (ConstantCompletion.coefficientMap J A I) t).val (op U) =
        b.hom.hom.app (op U) (φ.hom.app (op U) (r.val (op U)))
    rw [hφ']
    change _ = (ConstantCompletion.coefficientMap J A I).hom.app (op U)
      ((section_ring_equiv a (op U)) ((section_ring_equiv a (op U)).symm
        ((ConstantCompletion.constantSection (J := J) t).val (op U))))
    rw [RingEquiv.apply_symm_apply]
    rfl

private theorem residue_sections_of_completion_exists
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsNoetherianRing A] (t : A)
    {R B S T : Sheaf J CommRingCat.{v}}
    (φ : R ⟶ B) (q : R ⟶ S) (qB : B ⟶ T)
    (h : ∃ (a : R ≅ ConstantCompletion.constant J A)
      (b : B ≅ ConstantCompletion.completed J A (Ideal.span {t}))
      (c : S ≅ ConstantCompletion.finite J A (Ideal.span {t}) 0)
      (d : T ≅ ConstantCompletion.finite J A (Ideal.span {t}) 0),
      φ ≫ b.hom = a.hom ≫ ConstantCompletion.coefficientMap J A (Ideal.span {t}) ∧
      q ≫ c.hom = a.hom ≫ ConstantCompletion.quotient J A (Ideal.span {t}) 0 ∧
      qB ≫ d.hom = b.hom ≫ ConstantCompletion.projection J A (Ideal.span {t}) 0) :
    ∃ (e : S ≅ T) (r : (R.obj ⋙ forget CommRingCat).sections),
      Presheaf.IsLocallySurjective J q.hom ∧
      φ ≫ qB = q ≫ e.hom ∧
      (∀ U : C, RingHom.ker (q.hom.app (op U)).hom = Ideal.span {r.val (op U)}) ∧
      (∀ U : C, RingHom.ker (qB.hom.app (op U)).hom =
        Ideal.span {φ.hom.app (op U) (r.val (op U))}) := by
  obtain ⟨a, b, c, d, hφ, hq, hp⟩ := h
  exact residue_sections_of_completion J A t φ q qB a b c d hφ hq hp

end Transport

attribute [-instance] integralModel_coefficientMonObj in
/-- The first residue maps have their common finite quotient and principal section
kernels, with the actual constant-to-continuous scalar map in the comparison square.
-/
theorem integralModelsEmbeddedResidueSections
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    let φ := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X)
    let q := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X)
    let qB := IntegralModelsStacks.smallMap X
      (completedCoefficientMap X (completedReduction ℓ E π 0)).hom
    ∃ (e : (Arrow.mk q).right ≅ (Arrow.mk qB).right)
      (r : ((Arrow.mk φ).left.obj ⋙ forget CommRingCat.{u + 1}).sections),
      Presheaf.IsLocallySurjective (Scheme.coefficientProEtaleModelTopology.{u, u} X) q.hom ∧
      φ ≫ qB = q ≫ e.hom ∧
      (∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
        RingHom.ker (q.hom.app (op U)).hom = Ideal.span {r.val (op U)}) ∧
      (∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
        RingHom.ker (qB.hom.app (op U)).hom =
          Ideal.span {φ.hom.app (op U) (r.val (op U))}) := by
  let : IsNoetherianRing (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) :=
    isNoetherianRing_of_ringEquiv (PadicAlgCl.integers ℓ E.1) ULift.ringEquiv.symm
  exact residue_sections_of_completion_exists
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (ULift.up π)
    _ _ _ ⟨integralModelsEmbeddedConstantIso ℓ E X,
      integralModelsEmbeddedCompletedIso ℓ E π hπ X,
      integralModelsEmbeddedResidueIso ℓ E π X,
      integralModelsEmbeddedReductionIso ℓ E π hπ X,
      integralModelsEmbedded_scalar_square ℓ E π hπ X,
      integralModelsEmbedded_residue_square ℓ E π X,
      integralModelsEmbedded_reduction_square ℓ E π hπ X⟩

end AlgebraicGeometry.ProEtale
