/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import all WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation
import all WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities
import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import Mathlib.CategoryTheory.Abelian.Exact

/-! # A stationary quotient comparison characterized on actual cycles

Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-stationary-cycle-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem filtered_cycles_image
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (q n : ℤ) :
    imageSubobject ((F.step q : CochainComplex C ℤ).iCycles n ≫
      (F.step q).arrow.f n) =
      F.complexStep q n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
  let L : CochainComplex C ℤ := F.step q
  let i := (F.step q).arrow.f n
  let S := F.complexStep q n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥
  have hz : L.iCycles n ≫ i ≫ K.d n (n + 1) = 0 := by
    dsimp only [i]
    rw [(F.step q).arrow.comm, ← Category.assoc, HomologicalComplex.iCycles_d,
      zero_comp]
  apply le_antisymm
  · apply le_inf
    · exact imageSubobject_comp_le _ _
    · apply (Subobject.imageSubobject_le_iff _ _).mpr
      apply (pullback_factors_iff _ _ _).mpr
      apply (Subobject.bot_factors_iff_zero _).mpr
      simpa only [Category.assoc] using hz
  · have hS : S ≤ Subobject.mk i := by
      simpa only [S, i, DecreasingFiltration.complexStep, imageSubobject_mono] using
        (inf_le_left : S ≤ F.complexStep q n)
    let j := Subobject.ofLEMk S i hS
    have hd : j ≫ L.d n (n + 1) = 0 := by
      apply (cancel_mono ((F.step q).arrow.f (n + 1))).mp
      rw [zero_comp, Category.assoc, ← (F.step q).arrow.comm, ← Category.assoc,
        Subobject.ofLEMk_comp]
      apply (Subobject.bot_factors_iff_zero _).mp
      apply (pullback_factors_iff _ _ _).mp
      exact Subobject.factors_right_of_inf_factors S.factors_self
    let l := L.liftCycles j (n + 1) (by simp) hd
    rw [imageSubobject_mono]
    apply Subobject.le_of_factors
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨l, ?_⟩
    change l ≫ (L.iCycles n ≫ i) = S.arrow
    dsimp only [l]
    rw [← Category.assoc, HomologicalComplex.liftCycles_i, Subobject.ofLEMk_comp]

private theorem cycles_subobject
    {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ) (n : ℤ) :
    (Subobject.pullback (K.d n (n + 1))).obj ⊥ = Subobject.mk (K.iCycles n) := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (Subobject.mk_factors_iff _ _).mpr
    have hz : ((Subobject.pullback (K.d n (n + 1))).obj ⊥).arrow ≫
        K.d n (n + 1) = 0 := by
      apply (Subobject.bot_factors_iff_zero _).mp
      exact (pullback_factors_iff _ _ _).mp (Subobject.factors_self _)
    exact ⟨K.liftCycles _ (n + 1) (by simp) hz, K.liftCycles_i _ _ _ _⟩
  · apply (Subobject.mk_le_iff_factors _ _).mpr
    apply (pullback_factors_iff _ _ _).mpr
    apply (Subobject.bot_factors_iff_zero _).mpr
    exact K.iCycles_d _ _

private theorem filtered_class_preimage
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (q n : ℤ)
    (k : ((F.complexStep q n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ :
      Subobject (K.X n)) : C) ⟶ K.cycles n)
    (hk : k ≫ K.iCycles n =
      (F.complexStep q n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥).arrow) :
    (Subobject.pullback (k ≫ K.homologyπ n)).obj ((F.homologyFiltration n).step (q + 1)) =
      (Subobject.pullback
        (F.complexStep q n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥).arrow).obj
        ((F.complexStep q n ⊓ imageSubobject (K.d (n - 1) n)) ⊔
          (F.complexStep (q + 1) n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥)) := by
  let A := F.complexStep q n
  let A' := F.complexStep (q + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let S := A ⊓ Z
  let T := (Subobject.pullback (K.iCycles n)).obj (A' ⊓ Z)
  let d := HomologicalComplex.cyclesMap (F.step (q + 1)).arrow n
  have hT : T = Subobject.mk d := by
    apply Subobject.map_obj_injective (K.iCycles n)
    dsimp only [T]
    rw [DecreasingFiltration.map_pullback_mono, Subobject.map_mk]
    have hZ : Z = Subobject.mk (K.iCycles n) := cycles_subobject K n
    rw [← hZ, inf_eq_right.mpr (inf_le_right : A' ⊓ Z ≤ Z)]
    have hc := filtered_cycles_image K F (q + 1) n
    rw [imageSubobject_mono] at hc
    exact hc.symm.trans (Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) (by
      simpa only [Iso.refl_hom, Category.id_comp, d] using
        HomologicalComplex.cyclesMap_i (F.step (q + 1)).arrow n))
  have hnext : (F.homologyFiltration n).step (q + 1) =
      (Subobject.«exists» (K.homologyπ n)).obj T := by
    rw [hT, Subobject.exists_obj_eq_imageSubobject,
      ← Subobject.underlyingIso_hom_comp_eq_mk d, Category.assoc,
      imageSubobject_iso_comp]
    rw [← HomologicalComplex.homologyπ_naturality, imageSubobject_comp_of_epi]
    rfl
  have hker : (Subobject.map (K.iCycles n)).obj (kernelSubobject (K.homologyπ n)) = B := by
    let t := K.toCycles (n - 1) n
    have ht : t ≫ K.homologyπ n = 0 := K.toCycles_comp_homologyπ _ _
    have hsc := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk t (K.homologyπ n) ht) (K.homologyIsCokernel (n - 1) n (by simp))
    rw [← ((ShortComplex.exact_iff_image_eq_kernel _).mp hsc)]
    rw [← Subobject.exists_iso_map, ← Subobject.exists_obj_top,
      Subobject.exists_obj_comp, Subobject.exists_obj_top]
    dsimp only [t]
    rw [HomologicalComplex.toCycles_i]
  have hπ : (Subobject.pullback (K.homologyπ n)).obj
      ((Subobject.«exists» (K.homologyπ n)).obj T) =
      kernelSubobject (K.homologyπ n) ⊔ T := by
    exact DecreasingFiltration.pullback_exists_isCokernel
      (kernel.ι (K.homologyπ n)) (K.homologyπ n) (kernel.condition _)
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) T
  have hm : (Subobject.map (K.iCycles n)).obj
      (kernelSubobject (K.homologyπ n) ⊔ T) = B ⊔ (A' ⊓ Z) := by
    rw [(Subobject.mapPullbackAdj (K.iCycles n)).gc.l_sup, hker]
    dsimp only [T]
    rw [DecreasingFiltration.map_pullback_mono]
    have hZ : Z = Subobject.mk (K.iCycles n) := cycles_subobject K n
    rw [← hZ, inf_eq_right.mpr (inf_le_right : A' ⊓ Z ≤ Z)]
  have hpb : (Subobject.pullback (K.homologyπ n)).obj
      ((F.homologyFiltration n).step (q + 1)) =
      (Subobject.pullback (K.iCycles n)).obj (B ⊔ (A' ⊓ Z)) := by
    rw [hnext, hπ, ← hm, Subobject.pullback_map_self]
  rw [Subobject.pullback_comp, hpb, ← Subobject.pullback_comp, hk]
  have hB : B ≤ Z := by
    apply (Subobject.imageSubobject_le_iff _ _).mpr
    apply pullback_factors
    rw [Subobject.bot_factors_iff_zero]
    exact K.d_comp_d _ _ _
  have hA : A' ≤ A := by
    let a := Subobject.ofLE (F.step (q + 1)) (F.step q)
      (F.antitone_step (Int.le_add_one le_rfl))
    have ha := congrArg (fun f ↦ f.f n) (Subobject.ofLE_arrow
      (F.antitone_step (Int.le_add_one (le_refl q))))
    dsimp only [HomologicalComplex.comp_f] at ha
    dsimp only [A, A', DecreasingFiltration.complexStep]
    rw [imageSubobject_mono, imageSubobject_mono]
    exact Subobject.mk_le_mk_of_comm (a.f n) (by simpa only [a] using ha)
  apply Subobject.map_obj_injective S.arrow
  rw [← Subobject.inf_eq_map_pullback, ← Subobject.inf_eq_map_pullback]
  change S ⊓ (B ⊔ (A' ⊓ Z)) = S ⊓ ((A ⊓ B) ⊔ (A' ⊓ Z))
  conv_lhs => rw [sup_comm]
  rw [DecreasingFiltration.subobject_modular S (A' ⊓ Z) B (inf_le_inf_right Z hA)]
  have hSB : S ⊓ B = A ⊓ B := by
    change (A ⊓ Z) ⊓ B = _
    rw [inf_assoc, inf_eq_right.mpr hB]
  rw [hSB, sup_comm, inf_eq_right.mpr
    (sup_le (inf_le_inf_left A hB) (inf_le_inf_right Z hA))]

private theorem quotient_kernel
    {C : Type u} [Category.{v} C] [Abelian C] {X T : C}
    (B Z : Subobject X) (h : B ≤ Z) (z : T ⟶ (Z : C)) :
    kernelSubobject (z ≫ cokernel.π (Subobject.ofLE B Z h)) =
      (Subobject.pullback (z ≫ Z.arrow)).obj B := by
  let b := Subobject.ofLE B Z h
  have hk : kernelSubobject (cokernel.π b) = Subobject.mk b := by
    have he := (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk b (cokernel.π b) (cokernel.condition b)) (cokernelIsCokernel b))
    simpa only [imageSubobject_mono] using ((ShortComplex.exact_iff_image_eq_kernel _).mp he).symm
  have hp : (Subobject.pullback Z.arrow).obj B = Subobject.mk b := by
    apply Subobject.map_obj_injective Z.arrow
    rw [← Subobject.inf_eq_map_pullback, inf_eq_right.mpr h, Subobject.map_mk]
    simp [b]
  rw [← BigradedExactCouple.pullback_kernelSubobject, hk, ← hp,
    ← Subobject.pullback_comp]

/-- The page projection and graded homology projection kill the same actual cycles.
Source: Stacks Project, Homology, Tag 012K, Equation 12.24.5.2;
Tag 012Q, final subquotient calculation; Tag 012W, stationary bounds calculation.
(blueprint: lem-weil-pbc-stationary-cycle-comparison).

Proof. Write n=q+p, A=F^q K^n, A'=F^(q+1) K^n, Z=ker(d^n),
and B=im(d^(n-1)). The inclusion of the cycles of F^q K identifies their
image in K^n with S=A intersect Z. The upper bound makes the graded
r-cycles the image of S under the graded projection. The lower bound makes
the graded r-boundaries the image of A intersect B under that projection.
Consequently a cycle maps to zero in the page precisely when its image in
K^n belongs to (A intersect B)+A'. Intersecting this sum with S gives
D=(A intersect B)+(A' intersect Z), since B is contained in Z and A' is
contained in A. This is the modular identity for subobjects in an abelian
category. Thus the first kernel is the inverse image of D along the
actual-cycle inclusion into K^n.

For the other kernel, compose ha with the epic homology projection and use
homology naturality. This identifies the map from actual q-step cycles to
Y with the ambient homology projection, transported by c. Since a_i and
the cycle-to-homology projection are epic, H.step i is exactly the image
of actual i-step cycles in Y. The kernel of the ambient homology projection
on S is A intersect B; the image of the next-step cycles is the image of
A' intersect Z. The inverse image of that image under the restricted
homology projection is therefore (A intersect B)+(A' intersect Z), by the
cokernel inverse-image formula. As the next-step inclusion is monic, it
is the kernel of its cokernel; pulling this kernel back along homologyπ
followed by a_q yields the second kernel. Both kernels are the inverse
image of D along the same actual-cycle inclusion, so they are equal.
These are image, pullback and cokernel calculations, valid also for zero
complexes, zero graded pieces and r=1, without lifts of arbitrary elements
through an epimorphism. -/
private theorem stationary_projection_kernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (q p r : ℤ) (hr : 1 ≤ r)
    (hupper : F.complexStep (q + r) (q + p + 1) = ⊥)
    (hlower : F.complexStep (q - r + 1) (q + p - 1) = ⊤)
    {Y : C} (c : K.homology (q + p) ≅ Y) (H : DecreasingFiltration Y)
    (a : ∀ i : ℤ, (F.step i : CochainComplex C ℤ).homology (q + p) ⟶ (H.step i : C))
    (ha : ∀ i : ℤ, a i ≫ (H.step i).arrow =
      HomologicalComplex.homologyMap (F.step i).arrow (q + p) ≫ c.hom)
    (hepi : ∀ i : ℤ, Epi (a i))
    (z : (F.step q : CochainComplex C ℤ).cycles (q + p) ⟶
      (F.complexCycles q (q + p) r : C))
    (hz : z ≫ (F.complexCycles q (q + p) r).arrow =
      (F.step q : CochainComplex C ℤ).iCycles (q + p) ≫
        (F.complexQuotientπ q (q + 1) (by omega)).f (q + p)) :
    kernelSubobject (z ≫ filteredComplexPageπ K F r (q, p)) =
      kernelSubobject ((F.step q : CochainComplex C ℤ).homologyπ (q + p) ≫ a q ≫
        cokernel.π (Subobject.ofLE (H.step (q + 1)) (H.step q)
          (H.antitone_step (Int.le_add_one (le_refl q))))) := by
  classical
  have _hr := hr
  have _hupper := hupper
  let n := q + p
  let A := F.complexStep q n
  let A' := F.complexStep (q + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let S := A ⊓ Z
  let D := (A ⊓ B) ⊔ (A' ⊓ Z)
  let i := (F.step q).arrow.f n
  let a' := Subobject.ofLE (F.step (q + 1)) (F.step q)
    (F.antitone_step (Int.le_add_one le_rfl))
  let π := (F.complexQuotientπ q (q + 1) (by omega)).f n
  let P := Subobject.pullback i
  have hS : S ≤ Subobject.mk i := by
    simpa only [S, A, i, DecreasingFiltration.complexStep, imageSubobject_mono] using
      (inf_le_left : S ≤ A)
  let j := Subobject.ofLEMk S i hS
  have ha' : a'.f n ≫ i = (F.step (q + 1)).arrow.f n := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f ↦ f.f n) (Subobject.ofLE_arrow
        (F.antitone_step (Int.le_add_one (le_refl q))))
  have hA : A' ≤ Subobject.mk i := by
    simpa only [A', i, DecreasingFiltration.complexStep, imageSubobject_mono] using
      Subobject.mk_le_mk_of_comm (a'.f n) ha'
  have hAa : A' ≤ A := by
    simpa only [A, i, DecreasingFiltration.complexStep, imageSubobject_mono] using hA
  have hA' : P.obj A' = Subobject.mk (a'.f n) := by
    apply Subobject.map_obj_injective i
    rw [DecreasingFiltration.map_pullback_mono, Subobject.map_mk,
      inf_eq_right.mpr hA]
    simpa only [A', DecreasingFiltration.complexStep, imageSubobject_mono] using
      Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) (by simpa using ha')
  have hB : B ≤ Z := by
    apply (Subobject.imageSubobject_le_iff _ _).2
    apply pullback_factors
    rw [Subobject.bot_factors_iff_zero]
    exact K.d_comp_d _ _ _
  have hD : A ⊓ B ≤ S := inf_le_inf_left A hB
  have hpre : (Subobject.pullback (j ≫ π)).obj
      ((Subobject.«exists» π).obj (P.obj ((A ⊓ B) ⊔ A'))) =
      (Subobject.pullback S.arrow).obj D := by
    rw [Subobject.pullback_comp, DecreasingFiltration.filtered_preimage F q n, ← hA']
    rw [sup_eq_right.mpr (P.monotone (le_sup_right : A' ≤ (A ⊓ B) ⊔ A'))]
    rw [← Subobject.pullback_comp, Subobject.ofLEMk_comp]
    apply Subobject.map_obj_injective S.arrow
    rw [← Subobject.inf_eq_map_pullback, ← Subobject.inf_eq_map_pullback,
      DecreasingFiltration.subobject_modular S (A ⊓ B) A' hD]
    have hSA : S ⊓ A' = A' ⊓ Z := by
      change (A ⊓ Z) ⊓ A' = _
      calc
        (A ⊓ Z) ⊓ A' = (A ⊓ A') ⊓ Z := by ac_rfl
        _ = A' ⊓ Z := by rw [inf_eq_right.mpr hAa]
    rw [hSA, inf_eq_right.mpr (sup_le hD (inf_le_inf_right Z hAa))]
  let L : CochainComplex C ℤ := F.step q
  have hs : S.Factors (L.iCycles n ≫ i) := by
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      apply (Subobject.bot_factors_iff_zero _).mpr
      dsimp only [i]
      rw [Category.assoc, (F.step q).arrow.comm, ← Category.assoc,
        HomologicalComplex.iCycles_d, zero_comp]
  let s := Subobject.factorThru S (L.iCycles n ≫ i) hs
  have hsj : s ≫ j = L.iCycles n := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, j, Subobject.ofLEMk_comp, s, Subobject.factorThru_arrow]
  have hkpage : kernelSubobject (z ≫ filteredComplexPageπ K F r (q, p)) =
      (Subobject.pullback s).obj ((Subobject.pullback S.arrow).obj D) := by
    rw [filteredComplexPageπ, quotient_kernel, hz]
    have hb : F.complexBoundaries q n r =
        (Subobject.«exists» π).obj (P.obj ((A ⊓ B) ⊔ A')) := by
      dsimp only [n] at *
      simp only [DecreasingFiltration.complexBoundaries, hlower,
        Subobject.exists_obj_top]
      rfl
    change (Subobject.pullback (L.iCycles n ≫ π)).obj (F.complexBoundaries q n r) = _
    rw [hb, ← hsj, Category.assoc, Subobject.pullback_comp, hpre]
  have hszero : S.arrow ≫ K.d n (n + 1) = 0 := by
    apply (Subobject.bot_factors_iff_zero _).mp
    apply (pullback_factors_iff _ _ _).mp
    exact Subobject.factors_right_of_inf_factors S.factors_self
  let k := K.liftCycles S.arrow (n + 1) (by simp) hszero
  have hk : k ≫ K.iCycles n = S.arrow := K.liftCycles_i _ _ _ _
  have hcoh := filtered_class_preimage K F q n k hk
  rw [Subobject.pullback_comp] at hcoh
  have hcycles : HomologicalComplex.cyclesMap (F.step q).arrow n = s ≫ k := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [HomologicalComplex.cyclesMap_i, Category.assoc, hk]
    exact (Subobject.factorThru_arrow _ _ hs).symm
  have hH (t : ℤ) : H.step t =
      (Subobject.«exists» c.hom).obj ((F.homologyFiltration n).step t) := by
    have : Epi (a t) := hepi t
    change H.step t = (Subobject.«exists» c.hom).obj
      (imageSubobject (HomologicalComplex.homologyMap (F.step t).arrow n))
    rw [← Subobject.exists_obj_top, Subobject.exists_obj_comp,
      Subobject.exists_obj_top, ← ha t, imageSubobject_comp_of_epi,
      imageSubobject_mono, Subobject.mk_arrow]
  have htransport : (Subobject.pullback c.hom).obj (H.step (q + 1)) =
      (F.homologyFiltration n).step (q + 1) := by
    rw [hH, Subobject.exists_iso_map, Subobject.pullback_map_self]
  have hkH : kernelSubobject (L.homologyπ n ≫ a q ≫
      cokernel.π (Subobject.ofLE (H.step (q + 1)) (H.step q)
        (H.antitone_step (Int.le_add_one (le_refl q))))) =
      (Subobject.pullback s).obj ((Subobject.pullback S.arrow).obj D) := by
    rw [← Category.assoc, quotient_kernel, Category.assoc, ha q,
      ← Category.assoc, HomologicalComplex.homologyπ_naturality, hcycles]
    simp only [Category.assoc]
    rw [Subobject.pullback_comp, Subobject.pullback_comp, Subobject.pullback_comp,
      htransport, hcoh]
  exact hkpage.trans hkH.symm

private theorem actual_cycles_cover
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (q p r : ℤ)
    (hupper : F.complexStep (q + r) (q + p + 1) = ⊥) :
    ∃ z : (F.step q : CochainComplex C ℤ).cycles (q + p) ⟶
        (F.complexCycles q (q + p) r : C),
      Epi z ∧ z ≫ (F.complexCycles q (q + p) r).arrow =
        (F.step q : CochainComplex C ℤ).iCycles (q + p) ≫
          (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) := by
  let L : CochainComplex C ℤ := F.step q
  let f := (F.step q).arrow.f (q + p)
  let g := (F.complexQuotientπ q (q + 1) (by omega)).f (q + p)
  let R := F.complexStep q (q + p) ⊓
    (Subobject.pullback (K.d (q + p) (q + p + 1))).obj
      (F.complexStep (q + r) (q + p + 1))
  let W := (Subobject.pullback f).obj (R ⊔ F.complexStep (q + 1) (q + p))
  have hR : R.Factors (L.iCycles (q + p) ≫ f) := by
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      have hd : L.iCycles (q + p) ≫ f ≫ K.d (q + p) (q + p + 1) = 0 := by
        dsimp only [f]
        rw [(F.step q).arrow.comm (q + p) (q + p + 1),
          ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]
      rw [Category.assoc, hd]
      exact Subobject.factors_zero
  have hW : W.Factors (L.iCycles (q + p)) :=
    (pullback_factors_iff _ _ _).mpr (Subobject.sup_factors_of_factors_left hR)
  let z := Subobject.factorThru W (L.iCycles (q + p)) hW ≫
    (Subobject.imageFactorisation g W).F.e
  have hz : z ≫ (F.complexCycles q (q + p) r).arrow = L.iCycles (q + p) ≫ g := by
    change z ≫ ((Subobject.«exists» g).obj W).arrow = _
    dsimp [z]
    rw [Category.assoc, ← Subobject.imageFactorisation_F_m,
      (Subobject.imageFactorisation g W).F.fac]
    simp
  have hij : (ComplexShape.up' (r, 1 - r)).Rel (q, p) (q + r, p + 1 - r) := by
    change (q, p) + (r, 1 - r) = (q + r, p + 1 - r)
    apply Prod.ext
    · rfl
    · dsimp
      omega
  obtain ⟨A, t, t', x, y, hx, ht, hxt, hy⟩ :=
    filteredComplex_differential_representatives_cover K F r _ _ hij
  have hn : q + r + (p + 1 - r) = q + p + 1 := by omega
  have htzero : t' ≫ (F.step (q + r)).arrow.f (q + r + (p + 1 - r)) = 0 := by
    have hb : F.complexStep (q + r) (q + r + (p + 1 - r)) = ⊥ := by
      rw [hn]; exact hupper
    have hf : (F.step (q + r)).arrow.f (q + r + (p + 1 - r)) = 0 := by
      apply Subobject.mk_eq_bot_iff_zero.mp
      simpa only [DecreasingFiltration.complexStep, imageSubobject_mono] using hb
    rw [hf, comp_zero]
  have htd : t ≫ L.d (q + p) (q + p + 1) = 0 := by
    apply (cancel_mono ((F.step q).arrow.f (q + p + 1))).1
    dsimp only [L]
    rw [zero_comp, Category.assoc, ← (F.step q).arrow.comm]
    dsimp only [Prod.fst, Prod.snd] at ht
    have hzero := ht.trans htzero
    rw [hn] at hzero
    exact hzero
  let l := L.liftCycles t (q + p + 1) (by simp) htd
  have hlz : l ≫ z = x := by
    apply (cancel_mono (F.complexCycles q (q + p) r).arrow).1
    rw [Category.assoc, hz, ← Category.assoc, HomologicalComplex.liftCycles_i]
    exact hxt.symm
  have : Epi x := hx
  have : Epi z := epi_of_epi_fac hlz
  exact ⟨z, inferInstance, hz⟩

private theorem epi_iso_of_kernel_eq
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [Epi f] [Epi g]
    (h : kernelSubobject f = kernelSubobject g) :
    ∃ e : Y ≅ Z, f ≫ e.hom = g := by
  have hfg : kernel.ι f ≫ g = 0 := by
    apply (kernelSubobject_factors_iff g _).mp
    rw [← h]
    exact kernelSubobject_factors f _ (kernel.condition f)
  have hgf : kernel.ι g ≫ f = 0 := by
    apply (kernelSubobject_factors_iff f _).mp
    rw [h]
    exact kernelSubobject_factors g _ (kernel.condition g)
  let e : Y ≅ Z :=
    { hom := Abelian.epiDesc f g hfg
      inv := Abelian.epiDesc g f hgf
      hom_inv_id := by
        apply (cancel_epi f).mp
        simp only [Abelian.comp_epiDesc_assoc,
          Abelian.comp_epiDesc, Category.comp_id]
      inv_hom_id := by
        apply (cancel_epi g).mp
        simp only [Abelian.comp_epiDesc_assoc,
          Abelian.comp_epiDesc, Category.comp_id] }
  exact ⟨e, Abelian.comp_epiDesc f g hfg⟩

/-- At stationary outer bounds, actual cycles cover the graded cycles, and their
homology classes determine the stationary comparison.
Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-stationary-cycle-comparison).

Proof. Write n=q+p. The upper bound makes the r-cycle condition d(x)=0.
Thus projecting the cycles of F^q K to gr^q K has image exactly the graded
r-cycles; adding F^(q+1) before taking the graded projection does not change
its image. Factor this projection through its image to obtain the epimorphism z.
The lower bound makes r-boundaries the graded images of total boundaries
lying in F^q K. The map from cycles of F^q K to H^n(K), transported by c,
has image H.step q, by the epic factorization a q and its inclusion equation.
Its kernel is the total boundaries lying in F^q K. Quotienting this image by
H.step (q+1) therefore kills precisely those boundaries and the cycles of
F^(q+1) K. The two cokernel presentations have the same kernel on the actual
cycles, so their universal properties give mutually inverse comparison maps.
The resulting isomorphism satisfies the displayed equation. The inclusion
of graded cycles is monic, so the representative equation uniquely fixes z;
since z and the page projection are epic, the last equation uniquely fixes
the comparison. This also covers zero complexes and zero graded pieces. -/
theorem filteredStationary_cycle_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (q p r : ℤ) (hr : 1 ≤ r)
    (hupper : F.complexStep (q + r) (q + p + 1) = ⊥)
    (hlower : F.complexStep (q - r + 1) (q + p - 1) = ⊤)
    {Y : C} (c : K.homology (q + p) ≅ Y) (H : DecreasingFiltration Y)
    (a : ∀ i : ℤ, (F.step i : CochainComplex C ℤ).homology (q + p) ⟶ (H.step i : C))
    (ha : ∀ i : ℤ, a i ≫ (H.step i).arrow =
      HomologicalComplex.homologyMap (F.step i).arrow (q + p) ≫ c.hom)
    (hepi : ∀ i : ℤ, Epi (a i)) :
    ∃ (z : (F.step q : CochainComplex C ℤ).cycles (q + p) ⟶
        (F.complexCycles q (q + p) r : C))
      (e : filteredComplexPageObject K F r (q, p) ≅ H.gradedPiece q),
      Epi z ∧
      z ≫ (F.complexCycles q (q + p) r).arrow =
        (F.step q : CochainComplex C ℤ).iCycles (q + p) ≫
          (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) ∧
      z ≫ filteredComplexPageπ K F r (q, p) ≫ e.hom =
        (F.step q : CochainComplex C ℤ).homologyπ (q + p) ≫ a q ≫
          cokernel.π (Subobject.ofLE (H.step (q + 1)) (H.step q)
            (H.antitone_step (Int.le_add_one (le_refl q)))) := by
  obtain ⟨z, hz, hzinc⟩ := actual_cycles_cover K F q p r hupper
  have : Epi z := hz
  have (i : ℤ) : Epi (a i) := hepi i
  let f := z ≫ filteredComplexPageπ K F r (q, p)
  let g := (F.step q : CochainComplex C ℤ).homologyπ (q + p) ≫ a q ≫
    cokernel.π (Subobject.ofLE (H.step (q + 1)) (H.step q)
      (H.antitone_step (Int.le_add_one (le_refl q))))
  have : Epi f := by dsimp [f, filteredComplexPageπ]; infer_instance
  have : Epi g := by dsimp [g]; infer_instance
  have hker : kernelSubobject f = kernelSubobject g :=
    stationary_projection_kernel K F q p r hr hupper hlower c H a ha hepi
      z hzinc
  obtain ⟨e, he⟩ := epi_iso_of_kernel_eq f g hker
  exact ⟨z, e, hz, hzinc, by simpa only [f, g, Category.assoc] using he⟩

end CategoryTheory
