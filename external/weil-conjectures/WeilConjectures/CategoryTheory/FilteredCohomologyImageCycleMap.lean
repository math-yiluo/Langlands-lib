/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import all WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation
import all WeilConjectures.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries

/-! # Images and inverse images of filtered cycles in cohomology

Source: Stacks Project, Section 12.24, Equation 12.24.5.2 and Tag 012Q.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

private theorem pullback_bot_eq_kernel {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply le_kernelSubobject
    exact (Subobject.bot_factors_iff_zero _).mp
      ((Subobject.factors_pullback_obj_iff f ⊥ _).mp
        ((Subobject.le_iff_factors_arrow _ _).mp le_rfl))
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    exact (Subobject.bot_factors_iff_zero _).mpr (kernelSubobject_arrow_comp f)

private theorem step_cycles_image {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
    imageSubobject (HomologicalComplex.cyclesMap (L.step p).arrow n ≫ K.iCycles n) =
      L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
  let V : CochainComplex C ℤ := L.step p
  let m := (L.step p).arrow
  have hm (i : ℤ) : Mono (m.f i) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).map m)
    infer_instance
  let S := L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥
  have hS : S ≤ Subobject.mk (m.f n) := by
    simpa only [S, m, complexStep, imageSubobject_mono] using
      (inf_le_left : S ≤ L.complexStep p n)
  let a : (S : C) ⟶ V.X n :=
    Subobject.ofLE S (Subobject.mk (m.f n)) hS ≫ (Subobject.underlyingIso (m.f n)).hom
  have ha : a ≫ m.f n = S.arrow := by simp [a]
  have hz : S.arrow ≫ K.d n (n + 1) = 0 := by
    apply (kernelSubobject_factors_iff _ _).mp
    apply (Subobject.le_iff_factors_arrow _ _).mp
    simpa only [S, pullback_bot_eq_kernel] using (inf_le_right : S ≤ _)
  have had : a ≫ V.d n (n + 1) = 0 := by
    apply (cancel_mono (m.f (n + 1))).mp
    rw [Category.assoc, ← m.comm, ← Category.assoc, ha, hz, zero_comp]
  let t := V.liftCycles a (n + 1) (by simp) had
  apply le_antisymm
  · apply le_inf
    · rw [HomologicalComplex.cyclesMap_i]
      exact imageSubobject_comp_le _ _
    · rw [pullback_bot_eq_kernel]
      apply (Subobject.imageSubobject_le_iff _ _).mpr
      apply kernelSubobject_factors
      simp
  · rw [imageSubobject_mono]
    apply Subobject.le_mk_of_comm t
    rw [HomologicalComplex.cyclesMap_i, ← Category.assoc, HomologicalComplex.liftCycles_i]
    exact ha

private theorem cycle_class_image {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ)
    (c : ((L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ :
      Subobject (K.X n)) : C) ⟶ K.cycles n)
    (hc : c ≫ K.iCycles n =
      (L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥).arrow) :
    imageSubobject (c ≫ K.homologyπ n) = (L.homologyFiltration n).step p := by
  let S := L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let g := HomologicalComplex.cyclesMap (L.step p).arrow n
  have h : S.Factors (g ≫ K.iCycles n) := by
    apply (Subobject.imageSubobject_le_iff _ _).mp
    exact le_of_eq (step_cycles_image L p n)
  let t := S.factorThru (g ≫ K.iCycles n) h
  have ht : t ≫ S.arrow = g ≫ K.iCycles n := Subobject.factorThru_arrow _ _ _
  have : Epi t := epi_of_imageSubobject_comp_arrow_eq t
    (ht ▸ step_cycles_image L p n)
  have htc : t ≫ c = g := by
    rw [← cancel_mono (K.iCycles n), Category.assoc, hc]
    exact ht
  change _ = imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n)
  rw [← imageSubobject_comp_of_epi t, ← Category.assoc, htc,
    ← HomologicalComplex.homologyπ_naturality, imageSubobject_comp_of_epi]

private theorem pullback_exists_epi {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (q : X ⟶ Y) [Epi q] (T : Subobject X) :
    (Subobject.pullback q).obj ((Subobject.«exists» q).obj T) =
      kernelSubobject q ⊔ T := by
  have hc := Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι q) (kernel.condition q))
    (kernelIsKernel q)
  have hc' := IsCokernel.ofIsoComp (kernel.ι q) (kernelSubobject q).arrow
    (kernelSubobjectIso q).symm (kernelSubobject_arrow' q) hc
  simpa only [Subobject.mk_arrow] using
    pullback_exists_isCokernel (kernelSubobject q).arrow q
      (kernelSubobject_arrow_comp q) hc' T

private theorem cycles_subobject {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    Subobject.mk (K.iCycles n) = (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
  rw [pullback_bot_eq_kernel]
  apply le_antisymm
  · apply le_kernelSubobject
    rw [← Subobject.underlyingIso_hom_comp_eq_mk (K.iCycles n), Category.assoc,
      K.iCycles_d, comp_zero]
  · apply Subobject.le_mk_of_comm
      (K.liftCycles (kernelSubobject (K.d n (n + 1))).arrow (n + 1) (by simp)
        (kernelSubobject_arrow_comp _))
    exact K.liftCycles_i _ _ _ _

/-- The class map from filtered cycles has the expected image and inverse image.
Source: Stacks Project, Section 12.24, Equation 12.24.5.2 and Tag 012Q.
(blueprint: new-cohomology-image-cycle-map).

Proof. Write A = L^pK^n, A' = L^(p+1)K^n, Z = ker(d^n), B = im(d^(n-1)),
and S = A intersection Z. Since the inclusion L^pK into K is degreewise monic,
its induced map on cycles identifies the cycles of L^pK with S: this follows
by taking the pullback of the outgoing differential kernel along the inclusion.
The equation c followed by the ambient cycle inclusion equals S.arrow identifies
c with this cycle map, after that identification, by uniqueness of kernel lifts.
Naturality of the cycle-to-homology projection and its epimorphy then show that
the image of c followed by homologyπ is the image of H^n(L^pK) in H^n(K).
This proves the first equality, and the same argument at p+1 identifies the next
image step with the image of A' intersection Z under the ambient class map.
The ambient class map Z onto H^n(K) is epic and has kernel B, viewed inside Z.
The inverse image of the image of A' intersection Z under this epimorphism is
B + (A' intersection Z). Restricting this subobject to S gives the inverse image
under c followed by homologyπ. The modular identity for subobjects gives
S intersection (B + (A' intersection Z)) =
(A intersection B) + (A' intersection Z), because B is contained in Z by d²=0
and A' is contained in A by antitonicity. Pulling back along S.arrow yields the
second equality. These are identities of constructed subobjects, requiring no
finiteness, stationarity or choice of an unproved witness.
-/
theorem cohomologyImage_cycle_map
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ)
    (c : ((L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ :
      Subobject (K.X n)) : C) ⟶
      K.cycles n)
    (hc : c ≫ K.iCycles n =
      (L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥).arrow) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let f := c ≫ K.homologyπ n
  imageSubobject f = (L.homologyFiltration n).step p ∧
    (Subobject.pullback f).obj ((L.homologyFiltration n).step (p + 1)) =
      (Subobject.pullback (A ⊓ Z).arrow).obj ((A ⊓ B) ⊔ (A' ⊓ Z)) := by
  dsimp only
  constructor
  · exact cycle_class_image L p n c hc
  · let A := L.complexStep p n
    let A' := L.complexStep (p + 1) n
    let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
    let B := imageSubobject (K.d (n - 1) n)
    let S := A ⊓ Z
    let T := A' ⊓ Z
    let i := K.iCycles n
    let q := K.homologyπ n
    have hi : Subobject.mk i = Z := cycles_subobject K n
    have hTZ : T ≤ Z := inf_le_right
    have hTz : T.arrow ≫ K.d n (n + 1) = 0 := by
      apply (kernelSubobject_factors_iff _ _).mp
      apply (Subobject.le_iff_factors_arrow _ _).mp
      simpa only [Z, pullback_bot_eq_kernel] using hTZ
    let c' := K.liftCycles T.arrow (n + 1) (by simp) hTz
    have hc' : c' ≫ i = T.arrow := K.liftCycles_i _ _ _ _
    have hT : imageSubobject c' = (Subobject.pullback i).obj T := by
      apply Subobject.map_obj_injective i
      rw [map_pullback_mono, hi, inf_eq_right.mpr hTZ,
        ← Subobject.exists_iso_map, exists_image, hc', imageSubobject_mono,
        Subobject.mk_arrow]
    have hnext : (L.homologyFiltration n).step (p + 1) =
        (Subobject.«exists» q).obj ((Subobject.pullback i).obj T) := by
      rw [← hT, exists_image]
      exact (cycle_class_image L (p + 1) n c' hc').symm
    have hbound : (Subobject.map i).obj (kernelSubobject q) = B := by
      let Q := ShortComplex.mk (K.toCycles (n - 1) n) q
        (K.toCycles_comp_homologyπ (n - 1) n)
      have he : Q.Exact := Q.exact_of_g_is_cokernel
        (K.homologyIsCokernel (n - 1) n (by simp))
      have hk : kernelSubobject q = imageSubobject (K.toCycles (n - 1) n) :=
        ((ShortComplex.exact_iff_image_eq_kernel Q).mp he).symm
      rw [hk, ← Subobject.exists_iso_map, exists_image, K.toCycles_i]
    have hpre : (Subobject.map i).obj
        ((Subobject.pullback q).obj ((L.homologyFiltration n).step (p + 1))) = B ⊔ T := by
      rw [hnext, pullback_exists_epi, ← Subobject.exists_iso_map,
        Subobject.exists_obj_sup, Subobject.exists_iso_map, hbound,
        map_pullback_mono, hi, inf_eq_right.mpr hTZ]
    have hA' : A' ≤ A := by
      let a := Subobject.ofLE (L.step (p + 1)) (L.step p)
        (L.antitone_step (Int.le_add_one le_rfl))
      have ha : a.f n ≫ (L.step p).arrow.f n = (L.step (p + 1)).arrow.f n :=
        congrArg (fun f ↦ f.f n) (Subobject.ofLE_arrow
          (L.antitone_step (Int.le_add_one (show p ≤ p from le_rfl))))
      change imageSubobject ((L.step (p + 1)).arrow.f n) ≤
        imageSubobject ((L.step p).arrow.f n)
      rw [← ha]
      exact imageSubobject_comp_le _ _
    have hTS : T ≤ S := inf_le_inf hA' le_rfl
    have hBZ : B ≤ Z := by
      rw [← hi, ← hbound]
      rw [← Subobject.exists_iso_map, Subobject.exists_obj_eq_imageSubobject]
      exact imageSubobject_comp_le _ _ |>.trans_eq (imageSubobject_mono i)
    have hSB : S ⊓ B = A ⊓ B := by
      dsimp only [S]
      rw [inf_assoc, inf_eq_right.mpr hBZ]
    have hmod : S ⊓ (B ⊔ T) = (A ⊓ B) ⊔ T := by
      rw [sup_comm B T, subobject_modular S T B hTS, hSB, sup_comm]
    change (Subobject.pullback (c ≫ q)).obj _ =
      (Subobject.pullback S.arrow).obj ((A ⊓ B) ⊔ T)
    rw [Subobject.pullback_comp]
    rw [← Subobject.pullback_map_self i
      ((Subobject.pullback q).obj ((L.homologyFiltration n).step (p + 1))), hpre,
      ← Subobject.pullback_comp, hc]
    apply Subobject.map_obj_injective S.arrow
    rw [map_pullback_mono, map_pullback_mono, Subobject.mk_arrow, hmod,
      inf_eq_right.mpr (sup_le (le_inf inf_le_left (inf_le_right.trans hBZ)) hTS)]

end CategoryTheory.DecreasingFiltration
