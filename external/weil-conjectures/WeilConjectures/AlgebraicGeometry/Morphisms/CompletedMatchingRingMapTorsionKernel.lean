/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # CompletedMatchingRingMapTorsionKernel

## References

* Stacks Project, Tags 0BLH, 05ER and 05EU
* Stacks Project, Tag 05ER, torsion-submodule base-change kernel argument
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Transport the torsion-submodule base-change bijection of Stacks 05EC (1)
through the standard ring-pushout/tensor-product isomorphism. -/
private theorem pushout_torsion_descends
    {R : Type u} [CommRing R] (B C : CommRingCat.{u})
    (f : CommRingCat.of R ⟶ B) (g : CommRingCat.of R ⟶ C)
    (I : Ideal R) (hI : I.FG) (hflat : RingHom.Flat g.hom)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map g.hom) g.hom Ideal.le_comap_map))
    (x : (pushout f g : CommRingCat)) (n : ℕ)
    (hx : ∀ a ∈ I ^ n, (f ≫ pushout.inl f g).hom a * x = 0) :
    ∃ b : B, ∃ k : ℕ,
      (∀ a ∈ I ^ k, f.hom a * b = 0) ∧ (pushout.inl f g).hom b = x := by
  let : Algebra R B := f.hom.toAlgebra
  let : Algebra R C := g.hom.toAlgebra
  let H := (CommRingCat.isPushout_tensorProduct R C B).flip
  let e := H.isoPushout
  have he (b : B) : e.inv.hom ((pushout.inl f g).hom b) =
      TensorProduct.tmul R (1 : C) b := by
    exact congrArg (fun h : B ⟶ CommRingCat.of (TensorProduct R C B) ↦ h.hom b)
      H.inl_isoPushout_inv
  have hea (a : R) : e.inv.hom ((f ≫ pushout.inl f g).hom a) =
      algebraMap R (TensorProduct R C B) a := by
    change e.inv.hom ((pushout.inl f g).hom (f.hom a)) = _
    rw [he]
    exact ((Algebra.TensorProduct.includeRight (R := R) (A := C) (B := B)).commutes a)
  have ht : e.inv.hom x ∈ Ideal.primaryComponent (TensorProduct R C B) I := by
    apply (Ideal.primaryComponent_mem _ _ _).mpr
    refine ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr ?_⟩
    intro a
    rw [Algebra.smul_def, ← hea, ← map_mul, hx a a.property, map_zero]
  obtain ⟨b, hb⟩ := (Ideal.primaryComponent_baseChange_bijective I hI hflat hquot B).2
    ⟨e.inv.hom x, ht⟩
  obtain ⟨k, hk⟩ := (Ideal.primaryComponent_mem B I (b : B)).mp b.property
  refine ⟨b, k, ?_, ?_⟩
  · intro a ha
    exact (Submodule.mem_torsionBySet_iff _ _).mp hk ⟨a, ha⟩
  · apply e.symm.commRingCatIsoToRingEquiv.injective
    change e.inv.hom ((pushout.inl f g).hom (b : B)) = e.inv.hom x
    rw [he]
    exact congrArg Subtype.val hb

/-- A maximal-ideal-power torsion section on a scheme over the punctured spectrum is zero.
At every point the image prime is strictly below the maximal ideal. Choose an element
of the maximal ideal outside that prime. Its image is invertible in the stalk, while
its nth power annihilates the section. Thus the section has zero germ everywhere,
and sheaf separatedness implies that it is zero. No finiteness assumption is needed. -/
private theorem punctured_torsion_section_zero
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme)
    (b : Γ(Y, ⊤)) (n : ℕ)
    (hb : ∀ a ∈ IsLocalRing.maximalIdeal A ^ n,
      ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom a * b = 0) : b = 0 := by
  apply TopCat.Presheaf.section_ext Y.sheaf ⊤ b 0
  intro y hy
  let p : PrimeSpectrum A := (q ≫ U.ι) y
  have hp : p ≠ IsLocalRing.closedPoint A := (hU p).mp (q y).property
  have hm : ¬ IsLocalRing.maximalIdeal A ≤ p.asIdeal := by
    intro h
    apply hp
    apply PrimeSpectrum.ext
    exact le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h
  obtain ⟨a, ha, hpa⟩ := IsConcreteLE.not_le_iff_exists.mp hm
  let t : Γ(Y, ⊤) :=
    ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom a
  have ht : y ∈ Y.basicOpen t := by
    change y ∈ Y.basicOpen ((q ≫ U.ι).appTop ((ΓSpecIso (.of A)).inv a))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    exact hpa
  rw [map_zero]
  apply germ_eq_zero_of_pow_mul_eq_zero ⟨y, hy⟩ ht
  change t ^ n * b = 0
  simpa only [map_pow] using hb (a ^ n) (Ideal.pow_mem_pow ha n)

/-- The comparison kills no nonzero maximal-ideal-power torsion element. -/
theorem completedRingMap_torsion_kernel_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ x (n : ℕ),
      (∀ a ∈ IsLocalRing.maximalIdeal A ^ n,
        (D.baseMap ≫ pushout.inl _ _).hom a * x = 0) →
      D.completedRingMap x = 0 → x = 0 := by
  intro x n hx hc
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let g : CommRingCat.of A ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap A C)
  have hflat : RingHom.Flat g.hom := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hquot : Function.Bijective
      (Ideal.quotientMap (m.map g.hom) g.hom Ideal.le_comap_map) := by
    constructor
    · apply Ideal.quotientMap_injective'
      change (m.map (algebraMap A C)).comap (algebraMap A C) ≤ m
      rw [← AdicCompletion.maximalIdeal_eq_map]
      exact le_of_eq (IsLocalRing.maximalIdeal_comap (algebraMap A C))
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective A).2
        (IsLocalRing.residue C c)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal C)
        (algebraMap A C a) = Ideal.Quotient.mk (IsLocalRing.maximalIdeal C) c at ha
      refine ⟨Ideal.Quotient.mk m a, ?_⟩
      rw [Ideal.quotientMap_mk]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ha
      rwa [AdicCompletion.maximalIdeal_eq_map] at h
  obtain ⟨b, k, hb, hbx⟩ := pushout_torsion_descends D.matchingRing (.of C)
    D.baseMap g m m.fg_of_isNoetherianRing hflat hquot x n hx
  have hs : (pullback.snd
      (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop).hom b = 0 := by
    rw [← hbx] at hc
    change ((pushout.inl D.baseMap g) ≫ D.completedRingMap).hom b = 0 at hc
    simpa only [completedRingMap, pushout.inl_desc] using! hc
  have hf : (pullback.fst
      (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop).hom b = 0 := by
    apply punctured_torsion_section_zero hU q _ k
    intro a ha
    have h := congrArg (fun z ↦ (pullback.fst
      (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop).hom z)
      (hb a ha)
    rw [map_mul, map_zero] at h
    change (D.baseMap ≫ pullback.fst _ _).hom a * _ = 0 at h
    simpa only [baseMap, Category.assoc, pullback.lift_fst] using h
  have hbzero : b = 0 := by
    apply Concrete.isLimit_ext _ (pullbackIsPullback
      (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop) b 0
    intro j
    cases j with
    | some j =>
      cases j with
      | left => exact hf.trans (map_zero _).symm
      | right => exact hs.trans (map_zero _).symm
    | none =>
      change (pullback.fst _ _ ≫ (pullback.fst q (completionSpecMap A ∣_ U)).appTop) b = _
      simp only [CommRingCat.comp_apply, hf, map_zero]
  rw [← hbx, hbzero, map_zero]

end AlgebraicGeometry.Scheme.CompletionGluingData
