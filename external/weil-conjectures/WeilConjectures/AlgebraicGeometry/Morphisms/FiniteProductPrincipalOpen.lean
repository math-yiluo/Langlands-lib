/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict

/-! # Principal opens in spectra of finite products

## References

* Stacks Project, Tag 01I1 (affine schemes), and the finite product description of spectra in
  Mathlib.AlgebraicGeometry.Limits
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A principal open of a finite product spectrum is the coproduct of the component opens. -/
theorem finite_product_principal_open
    (H : CommRingCat.{u}) (h : H) (m : ℕ)
    (F : Fin m → Type u) [∀ i, CommRing (F i)] [∀ i, Algebra H (F i)] :
    let B := ∀ i : Fin m, F i
    let U := fun i : Fin m ↦ PrimeSpectrum.basicOpen (algebraMap H (F i) h)
    let V := PrimeSpectrum.basicOpen (algebraMap H B h)
    ∃ e : (∐ fun i : Fin m ↦
        Scheme.Opens.toScheme (X := Spec (CommRingCat.of (F i))) (U i)) ≅
        Scheme.Opens.toScheme (X := Spec (CommRingCat.of B)) V,
      e.hom ≫ Scheme.Opens.ι (X := Spec (CommRingCat.of B)) V ≫
        Spec.map (CommRingCat.ofHom (algebraMap H B)) =
        Sigma.desc (fun i : Fin m ↦
          Scheme.Opens.ι (X := Spec (CommRingCat.of (F i))) (U i) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H (F i)))) := by
  classical
  dsimp only
  let B := ∀ i : Fin m, F i
  let X := fun i : Fin m ↦ Spec (CommRingCat.of (F i))
  let U : ∀ i : Fin m, (X i).Opens :=
    fun i ↦ PrimeSpectrum.basicOpen (algebraMap H (F i) h)
  let V : (Spec (CommRingCat.of B)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H B h)
  let q := fun i : Fin m ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom F i))
  let re := RingEquiv.piCongrLeft' F (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m).symm
  let E : (∐ X) ≅ Spec (CommRingCat.of B) :=
    (Sigma.reindex (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m) X).symm ≪≫
      asIso (sigmaSpec (fun i : ULift.{u} (Fin m) ↦ CommRingCat.of (F i.down))) ≪≫
      Scheme.Spec.mapIso re.toCommRingCatIso.op
  have hE (i : Fin m) : Sigma.ι X i ≫ E.hom = q i := by
    dsimp only [E, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [← Category.assoc, ← Category.assoc]
    erw [Sigma.ι_reindex_inv
      (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m) X (ULift.up i)]
    erw [ι_sigmaSpec]
    change Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun i : ULift.{u} (Fin m) ↦ F i.down) (ULift.up i))) ≫
      Spec.map (CommRingCat.ofHom re.toRingHom) = q i
    rw [← Spec.map_comp]
    congr 1
  let a := fun i : Fin m ↦ (U i).ι ≫ q i
  have hpre (i : Fin m) : q i ⁻¹ᵁ V = U i := by
    change PrimeSpectrum.basicOpen
      ((Pi.evalRingHom F i) (algebraMap H B h)) = U i
    rfl
  have hdisj : Pairwise (Function.onFun Disjoint (fun i ↦ Set.range (a i))) := by
    intro i j hij
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
    have heq' : q i x.val = q j y.val := heq
    have hz : Sigma.ι X i x.val = Sigma.ι X j y.val := by
      apply E.hom.homeomorph.injective
      change E.hom ((Sigma.ι X i) x.val) = E.hom ((Sigma.ι X j) y.val)
      simpa only [← Scheme.Hom.comp_apply, hE] using heq'
    have := (sigmaι_eq_iff X i j x.val y.val).mp hz
    exact hij (congrArg Sigma.fst this)
  have : IsOpenImmersion (Sigma.desc a) := isOpenImmersion_sigmaDesc _ a hdisj
  have hrange : Set.range (Sigma.desc a) = (V : Set (Spec (CommRingCat.of B))) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      let c := sigmaOpenCover (fun i ↦ (U i).toScheme)
      obtain ⟨x, hx⟩ := c.covers w
      let i := c.idx w
      have hx' : Sigma.ι (fun i ↦ (U i).toScheme) i x = w := hx
      rw [← hx']
      have hm : x.val ∈ q i ⁻¹ᵁ V := by
        rw [hpre i]
        exact x.property
      change q i x.val ∈ V at hm
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      exact hm
    · intro hz
      obtain ⟨w, hw⟩ := E.hom.homeomorph.surjective z
      let c := sigmaOpenCover X
      obtain ⟨x, hx'⟩ := c.covers w
      let i := c.idx w
      have hx'' : Sigma.ι X i x = w := hx'
      rw [← hx''] at hw
      change E.hom ((Sigma.ι X i) x) = z at hw
      have hx : q i x = z := by
        simpa only [← Scheme.Hom.comp_apply, hE] using hw
      have hxU : x ∈ U i := by
        rw [← hpre i]
        change q i x ∈ V
        rwa [hx]
      refine ⟨Sigma.ι (fun i ↦ (U i).toScheme) i ⟨x, hxU⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      exact hx
  let e := IsOpenImmersion.isoOfRangeEq (Sigma.desc a) V.ι
    (hrange.trans (Scheme.Opens.range_ι V).symm)
  refine ⟨e, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, a, Category.assoc]
  congr 1
  dsimp only [q]
  rw [← Spec.map_comp]
  rfl


end AlgebraicGeometry.Scheme
