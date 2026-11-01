import Langlands.AlgebraicGeometry.Picard.PrincipalLocalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Ideal.UFD

/-! # Local equations for the closure of a prime germ -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Picard.PrimeDivisor

variable {X : Scheme.{u}}

/-- The reduced ideal data of the closure of a point. -/
noncomputable def closureIdeal (ζ : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {ζ}, isClosed_closure⟩

set_option backward.isDefEq.respectTransparency false in
/-- On an affine neighborhood of a point, the ideal of its closure is its prime ideal. -/
theorem closureIdeal_eq_primeIdealOf (ζ : X) (U : X.affineOpens) (hζU : ζ ∈ U.1) :
    (closureIdeal ζ).ideal U = (U.2.primeIdealOf ⟨ζ, hζU⟩).asIdeal := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure {ζ}) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous, PrimeSpectrum.vanishingIdeal_closure]
  have hpre : U.2.fromSpec ⁻¹' {ζ} = {U.2.primeIdealOf ⟨ζ, hζU⟩} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp
      exact U.2.fromSpec.isOpenEmbedding.injective
        (hp.trans (U.2.fromSpec_primeIdealOf ⟨ζ, hζU⟩).symm)
    · rintro rfl
      exact U.2.fromSpec_primeIdealOf ⟨ζ, hζU⟩
  rw [hpre, PrimeSpectrum.vanishingIdeal_singleton]

set_option backward.isDefEq.respectTransparency false in
/-- Away from a point and its specializations, its closure has the unit ideal. -/
theorem closureIdeal_eq_top (ζ : X) (U : X.affineOpens) (hζU : ζ ∉ U.1) :
    (closureIdeal ζ).ideal U = ⊤ := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure {ζ}) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous, PrimeSpectrum.vanishingIdeal_closure]
  have hpre : U.2.fromSpec ⁻¹' {ζ} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro p hp
    apply hζU
    rw [← Set.mem_singleton_iff.mp hp]
    exact U.2.range_fromSpec.subset (Set.mem_range_self p)
  rw [hpre, PrimeSpectrum.vanishingIdeal_empty]

set_option backward.isDefEq.respectTransparency false in
/-- Affine prime ideals preserve the coheight of the corresponding scheme point. -/
theorem primeIdealOf_height (ζ : X) (U : X.affineOpens) (hζU : ζ ∈ U.1) :
    (U.2.primeIdealOf ⟨ζ, hζU⟩).asIdeal.height = Order.coheight ζ := by
  rw [idealHeight_eq_coheight]
  rw [← coheight_eq_of_isOpenImmersion U.2.fromSpec, U.2.fromSpec_primeIdealOf]

set_option backward.isDefEq.respectTransparency false in
/-- Images of ideal data in a stalk agree for any two affine neighborhoods. -/
theorem map_ideal_germ_eq (I : X.IdealSheafData) (U V : X.affineOpens)
    (x : X) (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom := by
  obtain ⟨W, hW, hxW, hWUV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
  let W' : X.affineOpens := ⟨W, hW⟩
  have hWU : W' ≤ U := show W ≤ U.1 from le_trans hWUV inf_le_left
  have hWV : W' ≤ V := show W ≤ V.1 from le_trans hWUV inf_le_right
  have hU := congrArg (Ideal.map (X.presheaf.germ W x hxW).hom) (I.map_ideal hWU)
  have hV := congrArg (Ideal.map (X.presheaf.germ W x hxW).hom) (I.map_ideal hWV)
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res'] at hU hV
  exact hU.trans hV.symm

set_option backward.isDefEq.respectTransparency false in
/-- The closure ideal remains prime in the stalk at a specialization. -/
theorem closureIdeal_stalk_isPrime (ζ x : X) (hζx : ζ ⤳ x)
    (U : X.affineOpens) (hxU : x ∈ U.1) :
    ((closureIdeal ζ).ideal U).map (X.presheaf.germ U.1 x hxU).hom |>.IsPrime := by
  have hζU : ζ ∈ U.1 := hζx.mem_open U.1.isOpen hxU
  let p := U.2.primeIdealOf ⟨ζ, hζU⟩
  let q := U.2.primeIdealOf ⟨x, hxU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    apply U.2.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
    simpa only [p, q, U.2.fromSpec_primeIdealOf] using hζx
  have hd : Disjoint (q.asIdeal.primeCompl : Set Γ(X, U)) (p.asIdeal : Set Γ(X, U)) :=
    Set.disjoint_left.mpr (fun a ha hp ↦ ha (hpq hp))
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let := U.2.isLocalization_stalk ⟨x, hxU⟩
  rw [closureIdeal_eq_primeIdealOf ζ U hζU]
  exact IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl
    (X.presheaf.stalk x) p.asIdeal p.isPrime hd

set_option backward.isDefEq.respectTransparency false in
/-- The basic open of a closure equation is the complement of that closure in its chart. -/
theorem mem_basicOpen_equation_iff (ζ : X) (U : X.affineOpens) (a : Γ(X, U))
    (ha : (closureIdeal ζ).ideal U = Ideal.span {a}) (x : X) (hxU : x ∈ U.1) :
    x ∈ X.basicOpen a ↔ ¬ ζ ⤳ x := by
  have h : x ∈ closure ({ζ} : Set X) ↔ x ∉ X.basicOpen a := by
    change x ∈ (closureIdeal ζ).support ↔ _
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hxU,
      ha, X.zeroLocus_span, X.zeroLocus_singleton]
    rfl
  rw [specializes_iff_mem_closure]
  simpa only [not_not] using (not_congr h).symm

variable [IsIntegral X] [IsLocallyNoetherian X]

set_option backward.isDefEq.respectTransparency false in
/-- A prime germ determines a point of coheight one specializing to its base point.
Its basic-open membership is detected by divisibility of germs at the base point. -/
theorem exists_primeGermPoint (e : X) (π : X.presheaf.stalk e) (hπ : Prime π) :
    ∃ ζ : X, ζ ⤳ e ∧ Order.coheight ζ = 1 ∧
      ∀ (U : X.Opens) (heU : e ∈ U) (f : Γ(X, U)),
        ζ ∈ X.basicOpen f ↔ ¬ π ∣ X.presheaf.germ U e heU f := by
  let q : Spec (X.presheaf.stalk e) :=
    ⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ⟩
  let ζ : X := X.fromSpecStalk e q
  have hζe : ζ ⤳ e := by
    have h := (IsLocalRing.specializes_closedPoint q).map (X.fromSpecStalk e).continuous
    simpa only [Scheme.fromSpecStalk_closedPoint] using h
  refine ⟨ζ, hζe, ?_, ?_⟩
  · obtain ⟨U, hU, heU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show e ∈ (⊤ : X.Opens) from trivial)
    let : Algebra Γ(X, U) (X.presheaf.stalk e) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨e, heU⟩
    let := hU.isLocalization_stalk ⟨e, heU⟩
    have hq : q.asIdeal.height = 1 :=
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero) hπ.not_isUnit
    change Order.coheight (X.fromSpecStalk e q) = 1
    rw [← hU.fromSpecStalk_eq_fromSpecStalk heU, IsAffineOpen.fromSpecStalk,
      Scheme.Hom.comp_apply, coheight_eq_of_isOpenImmersion,
      ← idealHeight_eq_coheight]
    change (q.asIdeal.under Γ(X, U)).height = 1
    exact (IsLocalization.height_under
      (hU.primeIdealOf ⟨e, heU⟩).asIdeal.primeCompl q.asIdeal).trans hq
  · intro U heU f
    obtain ⟨W, hW, heW, hWU⟩ := exists_isAffineOpen_mem_and_subset heU
    let fW : Γ(X, W) := X.presheaf.map (homOfLE hWU).op f
    have hζW : ζ ∈ W := hζe.mem_open W.isOpen heW
    have hb : ζ ∈ X.basicOpen fW ↔ ¬ π ∣ X.presheaf.germ W e heW fW := by
      change X.fromSpecStalk e q ∈ X.basicOpen fW ↔ _
      rw [← hW.fromSpecStalk_eq_fromSpecStalk heW, IsAffineOpen.fromSpecStalk,
        Scheme.Hom.comp_apply]
      change q ∈ (Spec.map (X.presheaf.germ W e heW) ⁻¹ᵁ
        (hW.fromSpec ⁻¹ᵁ X.basicOpen fW)) ↔ _
      rw [hW.fromSpec_preimage_basicOpen]
      change (X.presheaf.germ W e heW fW ∉ Ideal.span {π}) ↔ _
      rw [Ideal.mem_span_singleton]
    have hg : X.presheaf.germ W e heW fW = X.presheaf.germ U e heU f :=
      X.presheaf.germ_res_apply (homOfLE hWU) e heW f
    rw [hg] at hb
    simpa only [fW, X.basicOpen_res, Opens.mem_inf, hζW, true_and] using hb

omit [IsLocallyNoetherian X] in
set_option backward.isDefEq.respectTransparency false in
/-- The ideal of a coheight-one point has a nonzero generator after localization
at any specialization with factorial stalk. The generator comes from the affine ideal. -/
theorem exists_stalk_numerator (ζ x : X) (hζ : Order.coheight ζ = 1) (hζx : ζ ⤳ x)
    [UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (U : X.affineOpens) (hxU : x ∈ U.1) :
    ∃ g ∈ (closureIdeal ζ).ideal U, g ≠ 0 ∧
      ((closureIdeal ζ).ideal U).map (X.presheaf.germ U.1 x hxU).hom =
        Ideal.span {X.presheaf.germ U.1 x hxU g} := by
  have hζU : ζ ∈ U.1 := hζx.mem_open U.1.isOpen hxU
  let p := U.2.primeIdealOf ⟨ζ, hζU⟩
  let q := U.2.primeIdealOf ⟨x, hxU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    apply (PrimeSpectrum.le_iff_specializes p q).mpr
    apply U.2.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
    simpa only [p, q, U.2.fromSpec_primeIdealOf] using hζx
  have hd : Disjoint (q.asIdeal.primeCompl : Set Γ(X, U)) (p.asIdeal : Set Γ(X, U)) :=
    Set.disjoint_left.mpr (fun a ha hp ↦ ha (hpq hp))
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let := U.2.isLocalization_stalk ⟨x, hxU⟩
  have : (p.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl
      (X.presheaf.stalk x) p.asIdeal p.isPrime hd
  have hh : (p.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x))).height = 1 :=
    (IsLocalization.height_map_of_disjoint q.asIdeal.primeCompl p.asIdeal hd).trans
      ((primeIdealOf_height ζ U hζU).trans hζ)
  have hprincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  obtain ⟨g, hg, hgen⟩ :=
    exists_numerator_generator q.asIdeal.primeCompl (X.presheaf.stalk x) p.asIdeal hprincipal
  have hg0 : g ≠ 0 := by
    intro hg0
    apply Ideal.ne_bot_of_height_eq_one hh
    rw [hgen, hg0, map_zero, Ideal.span_singleton_zero]
  rw [closureIdeal_eq_primeIdealOf ζ U hζU]
  exact ⟨g, hg, hg0, hgen⟩

set_option backward.isDefEq.respectTransparency false in
/-- The reduced ideal of a coheight-one point is generated by a nonzero function
on an affine neighborhood of each point when all stalks are factorial. -/
theorem exists_affine_equation (ζ : X) (hζ : Order.coheight ζ = 1)
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (x : X) :
    ∃ (V : X.affineOpens) (_ : x ∈ V.1) (a : Γ(X, V)),
      a ≠ 0 ∧ (closureIdeal ζ).ideal V = Ideal.span {a} := by
  classical
  by_cases hζx : ζ ⤳ x
  · obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    let U' : X.affineOpens := ⟨U, hU⟩
    let := hufd x
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
    obtain ⟨g, hg, hg0, hgen⟩ := exists_stalk_numerator ζ x hζ hζx U' hxU
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    let := hU.isLocalization_stalk ⟨x, hxU⟩
    obtain ⟨f, hf, hfgen⟩ := exists_principal_neighborhood
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)
      ((closureIdeal ζ).ideal U') (Ideal.fg_of_isNoetherianRing _) g hg hgen
    have hxf : x ∈ X.basicOpen f := by
      have hx' : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen f := by
        rw [← hU.fromSpec_image_basicOpen]
        exact ⟨hU.primeIdealOf ⟨x, hxU⟩, hf, rfl⟩
      simpa only [hU.fromSpec_primeIdealOf] using hx'
    let a := X.presheaf.map (homOfLE (X.basicOpen_le f)).op g
    refine ⟨X.affineBasicOpen (U := U') f, hxf, a, ?_, ?_⟩
    · intro ha
      apply hg0
      apply germ_injective_of_isIntegral X x hxU
      have hres := X.presheaf.germ_res_apply
        (homOfLE (X.basicOpen_le f)) x hxf g
      rw [show X.presheaf.map (homOfLE (X.basicOpen_le f)).op g = 0 from ha,
        map_zero] at hres
      simpa only [map_zero] using hres.symm
    · rw [← (closureIdeal ζ).map_ideal_basicOpen U' f]
      let := hU.isLocalization_basicOpen f
      exact hfgen Γ(X, X.basicOpen f) (IsLocalization.Away.algebraMap_isUnit f)
  · let W : X.Opens := ⟨(closure ({ζ} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hxW : x ∈ W := by
      exact fun hx ↦ hζx (specializes_iff_mem_closure.mpr hx)
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hxW
    have hζU : ζ ∉ U := fun hζU ↦ (hUW hζU) (subset_closure (Set.mem_singleton ζ))
    refine ⟨⟨U, hU⟩, hxU, 1, ?_, ?_⟩
    · intro hone
      have h := congrArg (X.presheaf.germ U x hxU) hone
      exact one_ne_zero (by simpa only [map_one, map_zero] using h)
    · rw [closureIdeal_eq_top ζ ⟨U, hU⟩ hζU, Ideal.span_singleton_one]

omit [IsLocallyNoetherian X] in
set_option backward.isDefEq.respectTransparency false in
/-- Local generators of the same ideal data have associated germs on overlaps. -/
theorem associated_equation_germs (I : X.IdealSheafData) (U V : X.affineOpens)
    (a : Γ(X, U)) (b : Γ(X, V))
    (ha : I.ideal U = Ideal.span {a}) (hb : I.ideal V = Ideal.span {b})
    (x : X) (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    Associated (X.presheaf.germ U.1 x hxU a) (X.presheaf.germ V.1 x hxV b) := by
  apply Ideal.span_singleton_eq_span_singleton.mp
  have h := map_ideal_germ_eq I U V x hxU hxV
  simpa only [ha, hb, Ideal.map_span, Set.image_singleton] using h

omit [IsLocallyNoetherian X] in
set_option backward.isDefEq.respectTransparency false in
/-- A nonzero local equation of a point closure has prime germ at its specializations. -/
theorem prime_equation_germ (ζ x : X) (hζx : ζ ⤳ x)
    (U : X.affineOpens) (hxU : x ∈ U.1) (a : Γ(X, U)) (ha0 : a ≠ 0)
    (ha : (closureIdeal ζ).ideal U = Ideal.span {a}) :
    Prime (X.presheaf.germ U.1 x hxU a) := by
  have hg0 : X.presheaf.germ U.1 x hxU a ≠ 0 := by
    intro h
    apply ha0
    apply germ_injective_of_isIntegral X x hxU
    simpa only [map_zero] using h
  apply (Ideal.span_singleton_prime hg0).mp
  have h := closureIdeal_stalk_isPrime ζ x hζx U hxU
  simpa only [ha, Ideal.map_span, Set.image_singleton] using h

omit [IsLocallyNoetherian X] in
set_option backward.isDefEq.respectTransparency false in
/-- An equation at the base point of a prime-germ closure has germ associated to that prime. -/
theorem associated_equation_germ_prime (ζ e : X) (hζe : ζ ⤳ e)
    (π : X.presheaf.stalk e) (hπ : Prime π)
    (hbasic : ∀ (U : X.Opens) (heU : e ∈ U) (f : Γ(X, U)),
      ζ ∈ X.basicOpen f ↔ ¬ π ∣ X.presheaf.germ U e heU f)
    (U : X.affineOpens) (heU : e ∈ U.1) (a : Γ(X, U)) (ha0 : a ≠ 0)
    (ha : (closureIdeal ζ).ideal U = Ideal.span {a}) :
    Associated (X.presheaf.germ U.1 e heU a) π := by
  have hζU : ζ ∈ U.1 := hζe.mem_open U.1.isOpen heU
  have hnot : ζ ∉ X.basicOpen a := by
    rw [mem_basicOpen_equation_iff ζ U a ha ζ hζU]
    exact not_not.mpr specializes_rfl
  have hdvd : π ∣ X.presheaf.germ U.1 e heU a :=
    Classical.not_not.mp (fun h ↦ hnot ((hbasic U.1 heU a).mpr h))
  exact (hπ.associated_of_dvd (prime_equation_germ ζ e hζe U heU a ha0 ha) hdvd).symm

end Langlands.AlgebraicGeometry.Picard.PrimeDivisor
