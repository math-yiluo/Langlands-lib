/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # The normalized stationary quotient presentation

Source: Stacks Project, Tag 012Q, proof of the stationary-page formula.
(blueprint: lem-sp-filtered-normalized-quotient-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- A quotient of the image of `f` is the quotient by the inverse image of its denominator. -/
private theorem image_quotient {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) (U V : Subobject Y)
    (h : V ≤ U) (hf : imageSubobject f = U) :
    Nonempty (cokernel (Subobject.ofLE V U h) ≅
      cokernel ((Subobject.pullback f).obj V).arrow) := by
  let e := Subobject.ofMkLE (image.ι f) U (by simpa [imageSubobject] using hf.le)
  let g := factorThruImage f ≫ e
  have hg : g ≫ U.arrow = f := by simp [g, e]
  have : Epi g := epi_of_imageSubobject_comp_arrow_eq g (hg ▸ hf)
  let W := (Subobject.pullback g).obj (Subobject.mk (Subobject.ofLE V U h))
  have hp := Subobject.isPullback g (Subobject.mk (Subobject.ofLE V U h))
  have he : Epi (biprod.desc (Subobject.mk (Subobject.ofLE V U h)).arrow g) := by
    exact epi_of_epi_fac (biprod.inr_desc _ _)
  have hs := hp.isPushout_of_epi he
  have hw : W = (Subobject.pullback f).obj V := by
    rw [← hg, Subobject.pullback_comp]
    dsimp [W]
    congr 1
    apply Subobject.map_obj_injective U.arrow
    rw [← Subobject.inf_eq_map_pullback, inf_eq_right.mpr h, Subobject.map_mk]
    simp
  have hc : Nonempty (cokernel (Subobject.ofLE V U h) ≅
      cokernel (Subobject.mk (Subobject.ofLE V U h)).arrow) := by
    exact ⟨HasColimit.isoOfNatIso
      (parallelPair.ext (Subobject.underlyingIso (Subobject.ofLE V U h)).symm
        (Iso.refl _) (by simp) (by simp))⟩
  obtain ⟨c⟩ := hc
  exact ⟨c ≪≫ hs.cokernelIso.symm ≪≫ eqToIso (by change cokernel W.arrow = _; rw [hw])⟩

/-- Restricting along a monomorphism and mapping back gives intersection with its image. -/
private theorem map_pullback_mono {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (i : X ⟶ Y) [Mono i] (S : Subobject Y) :
    (Subobject.map i).obj ((Subobject.pullback i).obj S) = Subobject.mk i ⊓ S := by
  exact (Subobject.inf_eq_map_pullback' (MonoOver.mk i) S).symm

/-- The restriction of a subobject contained in a monomorphism is its canonical lift. -/
private theorem restrict_mk {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (i : X ⟶ Y) [Mono i] (S : Subobject Y) (h : S ≤ Subobject.mk i) :
    (Subobject.pullback i).obj S = Subobject.mk (Subobject.ofLEMk S i h) := by
  apply Subobject.map_obj_injective i
  rw [map_pullback_mono, Subobject.map_mk]
  simp only [Subobject.ofLEMk_comp, Subobject.mk_arrow]
  exact inf_eq_right.mpr h

/-- Restriction along a monomorphism preserves joins of subobjects in its image. -/
private theorem restrict_sup {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (i : X ⟶ Y) [Mono i] (S T : Subobject Y)
    (hS : S ≤ Subobject.mk i) (hT : T ≤ Subobject.mk i) :
    (Subobject.pullback i).obj (S ⊔ T) =
      (Subobject.pullback i).obj S ⊔ (Subobject.pullback i).obj T := by
  apply Subobject.map_obj_injective i
  rw [(Subobject.mapPullbackAdj i).gc.l_sup]
  rw [map_pullback_mono, map_pullback_mono, map_pullback_mono]
  simp only [inf_eq_right.mpr hS, inf_eq_right.mpr hT,
    inf_eq_right.mpr (sup_le hS hT)]

/-- Adding the next filtration step does not change the image in the graded quotient. -/
private theorem normalized_image {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ)
    (S : Subobject (K.X n)) (hS : S ≤ L.complexStep p n) :
    let i := (L.step p).arrow.f n
    let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
    let j := Subobject.ofLEMk S i (by simpa [complexStep, imageSubobject_mono] using hS)
    imageSubobject (j ≫ q) = (Subobject.«exists» q).obj
      ((Subobject.pullback i).obj (S ⊔ L.complexStep (p + 1) n)) := by
  dsimp only
  let i := (L.step p).arrow.f n
  let i' := (L.step (p + 1)).arrow.f n
  let a := Subobject.ofLE (L.step (p + 1)) (L.step p)
    (L.antitone_step (Int.le_add_one le_rfl))
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  have ha : a.f n ≫ i = i' := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f => f.f n) (Subobject.ofLE_arrow
        (L.antitone_step (Int.le_add_one (show p ≤ p from le_rfl))))
  have hA' : L.complexStep (p + 1) n ≤ Subobject.mk i := by
    simpa only [complexStep, imageSubobject_mono] using
      Subobject.mk_le_mk_of_comm (a.f n) ha
  have hA : (Subobject.pullback i).obj (L.complexStep (p + 1) n) =
      Subobject.mk (a.f n) := by
    apply Subobject.map_obj_injective i
    rw [map_pullback_mono, Subobject.map_mk]
    simp only [inf_eq_right.mpr hA']
    simpa only [complexStep, imageSubobject_mono] using
      Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) (by simpa using ha)
  have haq : a.f n ≫ q = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
      complexQuotientπ, complexQuotient, a, q] using
      congrArg (fun f => f.f n) (cokernel.condition a)
  rw [restrict_sup i S _ (by simpa [complexStep, imageSubobject_mono] using hS) hA',
    Subobject.exists_obj_sup, hA]
  have hz : (Subobject.«exists» q).obj (Subobject.mk (a.f n)) = ⊥ := by
    apply Subobject.exists_obj_eq_bot
    rw [← Subobject.underlyingIso_hom_comp_eq_mk (a.f n), Category.assoc, haq,
      comp_zero]
  rw [hz, sup_bot_eq, restrict_mk i S (by
    simpa only [complexStep, imageSubobject_mono] using hS)]
  rw [Subobject.exists_obj_eq_imageSubobject]
  conv_rhs =>
    rw [← Subobject.underlyingIso_hom_comp_eq_mk (Subobject.ofLEMk S i _),
      Category.assoc, imageSubobject_iso_comp]

/-- The modular identity, proved by lifting along the epimorphism onto a sum. -/
private theorem subobject_modular {C : Type u} [Category.{v} C] [Abelian C]
    {X : C} (S D T : Subobject X) (h : D ≤ S) :
    S ⊓ (D ⊔ T) = D ⊔ (S ⊓ T) := by
  let R := S ⊓ (D ⊔ T)
  let U := D ⊔ (S ⊓ T)
  apply le_antisymm
  · have : Epi (Subobject.supDesc D T) := Subobject.epi_supDesc D T
    obtain ⟨W, e, he, x, hx⟩ := surjective_up_to_refinements_of_epi
      (Subobject.supDesc D T) (Subobject.ofLE R (D ⊔ T) inf_le_right)
    have hsum : e ≫ R.arrow =
        (x ≫ biprod.fst) ≫ D.arrow + (x ≫ biprod.snd) ≫ T.arrow := by
      calc
        e ≫ R.arrow = x ≫ Subobject.supDesc D T ≫ (D ⊔ T).arrow := by
          rw [← Category.assoc, ← hx, Category.assoc, Subobject.ofLE_arrow]
        _ = _ := by simp [Subobject.supDesc, biprod.desc_eq, Preadditive.comp_add,
          Preadditive.add_comp]
    have hs : S.Factors ((x ≫ biprod.snd) ≫ T.arrow) := by
      apply (Subobject.factors_iff _ _).2
      refine ⟨e ≫ Subobject.ofLE R S inf_le_left -
        (x ≫ biprod.fst) ≫ Subobject.ofLE D S h, ?_⟩
      change (e ≫ Subobject.ofLE R S inf_le_left -
        (x ≫ biprod.fst) ≫ Subobject.ofLE D S h) ≫ S.arrow = _
      simp only [Preadditive.sub_comp, Category.assoc, Subobject.ofLE_arrow]
      rw [hsum]
      simp only [Category.assoc]
      abel
    have hst : (S ⊓ T).Factors ((x ≫ biprod.snd) ≫ T.arrow) :=
      (Subobject.inf_factors _).2 ⟨hs, Subobject.factors_comp_arrow _⟩
    have hzero : R.arrow ≫ cokernel.π U.arrow = 0 := by
      rw [← cancel_epi e, comp_zero, ← Category.assoc, hsum, Preadditive.add_comp]
      have hd : D.arrow ≫ cokernel.π U.arrow = 0 := by
        rw [← Subobject.ofLE_arrow (show D ≤ U from le_sup_left),
          Category.assoc, cokernel.condition, comp_zero]
      rw [Category.assoc, hd, comp_zero, zero_add]
      have hstzero : (S ⊓ T).arrow ≫ cokernel.π U.arrow = 0 := by
        rw [← Subobject.ofLE_arrow (show S ⊓ T ≤ U from le_sup_right),
          Category.assoc, cokernel.condition, comp_zero]
      rw [← Subobject.factorThru_arrow _ _ hst, Category.assoc, hstzero, comp_zero]
    exact Subobject.le_of_comm (Abelian.monoLift U.arrow R.arrow hzero)
      (Abelian.monoLift_comp _ _ _)
  · exact sup_le (le_inf h le_sup_left)
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))

/-- Changing the target by an isomorphism preserves the inverse image of an image. -/
private theorem pullback_exists_iso {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Y' : C} (q : X ⟶ Y) (e : Y ≅ Y') (T : Subobject X) :
    (Subobject.pullback (q ≫ e.hom)).obj ((Subobject.«exists» (q ≫ e.hom)).obj T) =
      (Subobject.pullback q).obj ((Subobject.«exists» q).obj T) := by
  rw [← Subobject.exists_obj_comp, Subobject.pullback_comp, Subobject.exists_iso_map,
    Subobject.pullback_map_self]

/-- The inverse image of an image under a cokernel is the sum with its kernel. -/
private theorem pullback_exists_isCokernel {C : Type u} [Category.{v} C] [Abelian C]
    {X' X Y : C} (j : X' ⟶ X) [Mono j] (q : X ⟶ Y) (w : j ≫ q = 0)
    (hc : IsColimit (CokernelCofork.ofπ q w)) (T : Subobject X) :
    (Subobject.pullback q).obj ((Subobject.«exists» q).obj T) = Subobject.mk j ⊔ T := by
  let S := Subobject.mk j
  let hc' := IsCokernel.ofIsoComp j S.arrow (Subobject.underlyingIso j).symm
    (Subobject.underlyingIso_arrow j) hc
  let e := hc'.coconePointUniqueUpToIso (cokernelIsCokernel S.arrow)
  have he : q ≫ e.hom = cokernel.π S.arrow :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hc' (cokernelIsCokernel S.arrow)
      WalkingParallelPair.one
  rw [← pullback_exists_iso q e T, he, Subobject.pullback_exists_cokernelπ]

/-- Evaluation preserves the filtration cokernel and its inverse-image formula. -/
private theorem filtered_preimage {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ)
    (T : Subobject ((L.step p : CochainComplex C ℤ).X n)) :
    let a := Subobject.ofLE (L.step (p + 1)) (L.step p)
      (L.antitone_step (Int.le_add_one le_rfl))
    let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
    (Subobject.pullback q).obj ((Subobject.«exists» q).obj T) =
      Subobject.mk (a.f n) ⊔ T := by
  dsimp only
  let a := Subobject.ofLE (L.step (p + 1)) (L.step p)
    (L.antitone_step (Int.le_add_one le_rfl))
  let G := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  have hc := isColimitOfHasCokernelOfPreservesColimit G a
  exact pullback_exists_isCokernel (a.f n) (G.map (cokernel.π a))
    (by simpa only [G, HomologicalComplex.eval_map, HomologicalComplex.comp_f,
      HomologicalComplex.zero_f] using congrArg (fun f => f.f n) (cokernel.condition a))
    hc T

/-- The quotient of normalized cycle and boundary subobjects has the cycle presentation.
Source: Stacks Project, Tag 012Q, final quotient calculation, Equation 12.24.5.2.
(blueprint: lem-sp-filtered-normalized-quotient-presentation).

Proof. Set A=L^pK^n, A'=L^(p+1)K^n, Z=ker(d^n), B=im(d^(n-1)).
The degree-n projection q from L^pK to gr^pK is an epimorphism whose kernel
is the degree-n image of L^(p+1)K. Evaluation preserves cokernels, so its
kernel inside A is the restriction of A'. The normalized cycle subobject
is the image of (A intersection Z)+A', restricted to A, under q; the
normalized boundary subobject is the image of (A intersection B)+A'.
Map A intersection Z onto the former, then onto its quotient by the latter.
This map is epic: adding A' does not change an image under q. Its kernel
is the restriction to A intersection Z of (A intersection B)+A'.
Since B is contained in Z by d squared equal to zero and A' is contained
in A by antitonicity, the modular identity identifies that kernel with
(A intersection B)+(A' intersection Z), restricted to A intersection Z.
The first isomorphism theorem gives the displayed cokernel isomorphism.
This calculation uses neither cohomology nor stationarity hypotheses.
-/
theorem normalizedStationaryQuotient_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  let P := Subobject.pullback ((L.step p).arrow.f n)
  let Zbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ Z) ⊔ A'))
  let Bbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ B) ⊔ A'))
  ∀ hBZ : Bbar ≤ Zbar,
    Nonempty (cokernel (Subobject.ofLE Bbar Zbar hBZ) ≅
      cokernel ((Subobject.pullback (A ⊓ Z).arrow).obj
        ((A ⊓ B) ⊔ (A' ⊓ Z))).arrow) := by
  dsimp only
  intro hBZ
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let i := (L.step p).arrow.f n
  let a := Subobject.ofLE (L.step (p + 1)) (L.step p)
    (L.antitone_step (Int.le_add_one le_rfl))
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  have hS : A ⊓ Z ≤ Subobject.mk i := by
    simpa only [A, i, complexStep, imageSubobject_mono] using
      (inf_le_left : A ⊓ Z ≤ A)
  let j := Subobject.ofLEMk (A ⊓ Z) i hS
  have ha : a.f n ≫ i = (L.step (p + 1)).arrow.f n := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f => f.f n) (Subobject.ofLE_arrow
        (L.antitone_step (Int.le_add_one (show p ≤ p from le_rfl))))
  have hA : A' ≤ Subobject.mk i := by
    simpa only [A', complexStep, imageSubobject_mono] using
      Subobject.mk_le_mk_of_comm (a.f n) ha
  have hAa : A' ≤ A := by simpa only [A, complexStep, imageSubobject_mono] using hA
  have hA' : (Subobject.pullback i).obj A' = Subobject.mk (a.f n) := by
    apply Subobject.map_obj_injective i
    rw [map_pullback_mono, Subobject.map_mk, inf_eq_right.mpr hA]
    simpa only [A', complexStep, imageSubobject_mono] using
      Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _) (by simpa using ha)
  have hB : B ≤ Z := by
    apply (Subobject.imageSubobject_le_iff _ _).2
    apply pullback_factors
    rw [Subobject.bot_factors_iff_zero]
    exact K.d_comp_d _ _ _
  have hD : A ⊓ B ≤ A ⊓ Z := inf_le_inf_left A hB
  have hImage := normalized_image L p n (A ⊓ Z) (inf_le_left : A ⊓ Z ≤ A)
  have hPreimage :
      (Subobject.pullback (j ≫ q)).obj
        ((Subobject.«exists» q).obj ((Subobject.pullback i).obj ((A ⊓ B) ⊔ A'))) =
      (Subobject.pullback (A ⊓ Z).arrow).obj ((A ⊓ B) ⊔ (A' ⊓ Z)) := by
    rw [Subobject.pullback_comp, filtered_preimage L p n, ← hA']
    rw [sup_eq_right.mpr ((Subobject.pullback i).monotone
      (le_sup_right : A' ≤ (A ⊓ B) ⊔ A'))]
    rw [← Subobject.pullback_comp, Subobject.ofLEMk_comp]
    apply Subobject.map_obj_injective (A ⊓ Z).arrow
    rw [← Subobject.inf_eq_map_pullback, ← Subobject.inf_eq_map_pullback,
      subobject_modular (A ⊓ Z) (A ⊓ B) A' hD]
    have hAZ : (A ⊓ Z) ⊓ A' = A' ⊓ Z := by
      calc
        (A ⊓ Z) ⊓ A' = (A ⊓ A') ⊓ Z := by ac_rfl
        _ = A' ⊓ Z := by rw [inf_eq_right.mpr hAa]
    rw [hAZ, inf_eq_right.mpr (sup_le hD (inf_le_inf_right Z hAa))]
  obtain ⟨e⟩ := image_quotient (j ≫ q) _ _ hBZ hImage
  exact ⟨e ≪≫ eqToIso (by rw [hPreimage])⟩

end CategoryTheory.DecreasingFiltration
