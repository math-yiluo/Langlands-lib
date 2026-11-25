/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The closed-fibre module of a polynomial chart

Source: Stacks Project, Tag 00RH, the displayed map of localized closed-fibre rings.
(blueprint: lem-sbc-polynomial-chart-closed-fiber-module-flat)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_fibre_lift {X T : Scheme.{u}} (f : X ⟶ T) (x : X) :
    let R := T.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let φ := (f.stalkMap x).hom
    let I := (IsLocalRing.maximalIdeal R).map φ
    ∃ v : Spec (.of (B ⧸ I)) ⟶ f.fiber (f x),
      v ≫ f.fiberι (f x) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk x := by
  let R := T.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let I := (IsLocalRing.maximalIdeal R).map φ
  let Q := B ⧸ I
  let q : B →+* Q := Ideal.Quotient.mk I
  let r : R →+* Q := q.comp φ
  have hr : IsLocalRing.maximalIdeal R ≤ RingHom.ker r := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ ha)
  let k : T.residueField (f x) →+* Q := Ideal.Quotient.lift _ r hr
  let a : Spec (.of Q) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ X.fromSpecStalk x
  let b : Spec (.of Q) ⟶ Spec (T.residueField (f x)) := Spec.map (CommRingCat.ofHom k)
  have hab : a ≫ f = b ≫ T.fromSpecResidueField (f x) := by
    dsimp only [a, b, Scheme.fromSpecResidueField]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, ← Category.assoc, ← Spec.map_comp]
    rfl
  exact ⟨pullback.lift a b hab, pullback.lift_fst _ _ _⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem stalkMap_kills_maximalIdeal_of_field_factor
    {E T : Scheme.{u}} {K : Type u} [Field K]
    (k : E ⟶ Spec (.of K)) (i : Spec (.of K) ⟶ T) (z : E)
    (a : T.presheaf.stalk ((k ≫ i) z))
    (ha : a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk ((k ≫ i) z))) :
    ((k ≫ i).stalkMap z).hom a = 0 := by
  let t := k z
  let e : (Spec (.of K)).presheaf.stalk t ≅ CommRingCat.of K :=
    eqToIso (congrArg (Spec (.of K)).presheaf.stalk
      (Subsingleton.elim t (IsLocalRing.closedPoint K))) ≪≫ stalkClosedPointIso (.of K)
  have : IsLocalHom e.hom.hom := isLocalHom_of_isIso _
  have hn := map_nonunit (i.stalkMap t).hom a ha
  have hn' := map_nonunit e.hom.hom _ hn
  have hz : e.hom.hom ((i.stalkMap t).hom a) = 0 := by
    change ¬ IsUnit (e.hom.hom ((i.stalkMap t).hom a)) at hn'
    simpa only [isUnit_iff_ne_zero, not_not] using hn'
  have hz' : (i.stalkMap t).hom a = 0 :=
    (ConcreteCategory.bijective_of_isIso e.hom).1 (hz.trans (map_zero _).symm)
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  change (k.stalkMap z).hom ((i.stalkMap t).hom a) = 0
  rw [hz', map_zero]

end AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem stalkMap_kills_maximalIdeal_of_eq_field_factor
    {E T : Scheme.{u}} {K : Type u} [Field K]
    (h : E ⟶ T) (k : E ⟶ Spec (.of K)) (i : Spec (.of K) ⟶ T)
    (heq : h = k ≫ i) (z : E)
    (a : T.presheaf.stalk (h z))
    (ha : a ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk (h z))) :
    (h.stalkMap z).hom a = 0 := by
  subst h
  exact stalkMap_kills_maximalIdeal_of_field_factor k i z a ha

@[reassoc]
private theorem fiber_congr_ι {X T : Scheme.{u}} (f : X ⟶ T) {y y' : T} (h : y = y') :
    eqToHom (congrArg f.fiber h) ≫ f.fiberι y' = f.fiberι y := by
  subst y'
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem stalkClosedPointTo_congr {X : Scheme.{u}} {Q : CommRingCat.{u}} [IsLocalRing Q]
    (h k : Spec Q ⟶ X) (heq : h = k) :
    Scheme.stalkClosedPointTo h =
      (X.presheaf.stalkCongr (.of_eq (congrArg
        (fun m : Spec Q ⟶ X ↦ m (IsLocalRing.closedPoint Q)) heq))).hom ≫
      Scheme.stalkClosedPointTo k := by
  dsimp only [Scheme.stalkClosedPointTo]
  rw [Scheme.Hom.stalkMap_congr_hom h k heq, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_stalk_kernel {X T : Scheme.{u}} (f : X ⟶ T)
    (x : X) (y : T) (hy : f x = y) (z : f.fiber y) (hx : f.fiberι y z = x) :
    let R := T.presheaf.stalk (f x)
    let φ := (f.stalkMap x).hom
    let ρ := ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫
      (f.fiberι y).stalkMap z).hom
    RingHom.ker ρ = (IsLocalRing.maximalIdeal R).map φ := by
  let R := T.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let j := f.fiberι y
  let F := (f.fiber y).presheaf.stalk z
  let ρcat : B ⟶ F := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ j.stalkMap z
  let ρ := ρcat.hom
  let I := (IsLocalRing.maximalIdeal R).map φ
  have hle : I ≤ RingHom.ker ρ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have heq : f.stalkMap x ≫ ρcat =
        (T.presheaf.stalkCongr (.of_eq (congrArg f hx.symm))).hom ≫
          (j ≫ f).stalkMap z := by
      dsimp only [ρcat]
      rw [← Category.assoc, f.stalkMap_congr_point x (j z) hx.symm,
        Category.assoc, ← Scheme.Hom.stalkMap_comp]
    let c := (T.presheaf.stalkCongr (.of_eq (congrArg f hx.symm))).hom
    have : IsLocalHom c.hom := isLocalHom_of_isIso _
    have hc := map_nonunit c.hom a ha
    have hk := stalkMap_kills_maximalIdeal_of_eq_field_factor (j ≫ f)
      (f.fiberToSpecResidueField y) (T.fromSpecResidueField y) (f.fiber_fac y) z
      (c.hom a) hc
    change ρ (φ a) = 0
    exact (congrArg (fun k : R ⟶ F ↦ k.hom a) heq).trans hk
  let Q := B ⧸ I
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (IsLocalRing.map_maximalIdeal_lt_top φ).ne
  have : IsLocalRing Q := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let q : B ⟶ CommRingCat.of Q := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨v₀, hv₀⟩ := quotient_fibre_lift f x
  let v : Spec (.of Q) ⟶ f.fiber y := v₀ ≫ eqToHom (congrArg f.fiber hy)
  have hv : v ≫ j = Spec.map q ≫ X.fromSpecStalk x := by
    dsimp only [v, j]
    rw [Category.assoc, fiber_congr_ι f hy, hv₀]
  have hz : v (IsLocalRing.closedPoint Q) = z := by
    apply j.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, Spec_closedPoint,
      Scheme.fromSpecStalk_closedPoint]
    exact hx.symm
  let γ : F ⟶ CommRingCat.of Q :=
    ((f.fiber y).presheaf.stalkCongr (.of_eq hz.symm)).hom ≫ Scheme.stalkClosedPointTo v
  have hρ : ρcat ≫ γ = q := by
    dsimp only [ρcat, γ]
    rw [Category.assoc, ← Category.assoc (j.stalkMap z),
      j.stalkMap_congr_point z (v (IsLocalRing.closedPoint Q)) hz.symm,
      Category.assoc, ← Scheme.stalkClosedPointTo_comp]
    rw [stalkClosedPointTo_congr (v ≫ j) (Spec.map q ≫ X.fromSpecStalk x) hv]
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    simp only [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk q U _
  apply le_antisymm
  · intro b hb
    have hb' : q.hom b = 0 := by
      rw [← hρ, CommRingCat.hom_comp]
      change γ.hom (ρ b) = 0
      rw [RingHom.mem_ker.mp hb, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hb'
  · exact hle

end AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_square_stalk_commutes
    {E A Z W : Scheme.{u}} (e : E ⟶ A) (i : Z ⟶ E) (j : W ⟶ A) (m : Z ⟶ W)
    (h : m ≫ j = i ≫ e) (z : Z) (x : E) (hx : i z = x) (hw : j (m z) = e x) :
    (A.presheaf.stalkCongr (.of_eq hw.symm)).hom ≫ j.stalkMap (m z) ≫ m.stalkMap z =
      e.stalkMap x ≫ (E.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ i.stalkMap z := by
  rw [← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_hom (m ≫ j) (i ≫ e) h z, Scheme.Hom.stalkMap_comp]
  rw [← Category.assoc, ← Category.assoc]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_comp]
  have hh := e.stalkMap_congr_point x (i z) hx.symm
  simpa only [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc] using
    congrArg (fun k ↦ k ≫ i.stalkMap z) hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem polynomial_fibreMap_fiberι {X T : Scheme.{u}} (f : X ⟶ T)
    (U : X.Opens) (n : ℕ) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f) (y : T) :
    PolynomialChart.fibreMap f U n e he y ≫
        (AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiberι y =
      (U.ι ≫ f).fiberι y ≫ e := by
  simp [PolynomialChart.fibreMap, Scheme.Hom.fiberι]

end AlgebraicGeometry

section
universe v w t
variable {A : Type u} {B : Type v} {Af : Type w} {Bf : Type t}
  [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]

private theorem quotient_equiv_of_ker (I : Ideal A) (ρ : A →+* Af)
    (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = I) :
    ∃ e : A ⧸ I ≃+* Af, ∀ a, e (Ideal.Quotient.mk I a) = ρ a := by
  let e := (Ideal.quotEquivOfEq hker.symm).trans (ρ.quotientKerEquivOfSurjective hρ)
  exact ⟨e, fun a ↦ by simp [e]⟩

private theorem flat_quotientMap_of_flat
    (α : A →+* B) (ρA : A →+* Af) (ρB : B →+* Bf) (ψ : Af →+* Bf)
    (I : Ideal A) (J : Ideal B) (hIJ : I ≤ J.comap α)
    (hA : Function.Surjective ρA) (hB : Function.Surjective ρB)
    (hkerA : RingHom.ker ρA = I) (hkerB : RingHom.ker ρB = J)
    (hc : ψ.comp ρA = ρB.comp α) (hψ : ψ.Flat) :
    (Ideal.quotientMap J α hIJ).Flat := by
  obtain ⟨eA, heA⟩ := quotient_equiv_of_ker I ρA hA hkerA
  obtain ⟨eB, heB⟩ := quotient_equiv_of_ker J ρB hB hkerB
  have heq : Ideal.quotientMap J α hIJ =
      eB.symm.toRingHom.comp (ψ.comp eA.toRingHom) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    apply eB.injective
    change eB (Ideal.Quotient.mk J (α a)) = eB (eB.symm (ψ (eA (Ideal.Quotient.mk I a))))
    rw [RingEquiv.apply_symm_apply, heA, heB]
    exact (congrArg (fun k : A →+* Bf ↦ k a) hc).symm
  rw [heq]
  exact ((RingHom.Flat.of_bijective eA.bijective).comp hψ).comp
    (RingHom.Flat.of_bijective eB.symm.bijective)
end

namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
private theorem maximalIdeal_map_stalkMap_congr {E T : Scheme.{u}}
    (h k : E ⟶ T) (heq : h = k) (x : E) :
    (IsLocalRing.maximalIdeal (T.presheaf.stalk (h x))).map (h.stalkMap x).hom =
      (IsLocalRing.maximalIdeal (T.presheaf.stalk (k x))).map (k.stalkMap x).hom := by
  rw [Scheme.Hom.stalkMap_congr_hom h k heq x, CommRingCat.hom_comp, ← Ideal.map_map,
    IsLocalRing.map_maximalIdeal_of_surjective _ (ConcreteCategory.bijective_of_isIso _).2]

set_option backward.isDefEq.respectTransparency false in
/-- Flatness of the canonical polynomial fibre-stalk map gives exactly the closed-fibre
module flatness required by the local ring criterion.

Proof: let y = f(U.ι x) = p(e x), where p is the affine-space projection. The stalk of the
fibre of p at the image of x is canonically S / m_R S, where R = O_T,y and
S = O_(A^n_T),e(x). The stalk of the fibre of U over y is B / m_R B, with B = O_U,x.
To identify the kernel, the fibre projection factors through Spec kappa(y), so it kills
m_R. Conversely Spec(B / m_R B) maps into the fibre by the pullback universal property;
the induced map on stalks is a left inverse to the quotient map. Fibre inclusions are
immersions, so their stalk maps are surjective and these kernel computations give
isomorphisms with the quotients.
The maps commute with the quotient maps because both are induced by the chart e.
The open-fibre inclusion identifies the latter stalk with the fibre stalk used by
PolynomialChart.stalkMap. Transport its assumed flatness across these two ring isomorphisms.
Finally the canonical (S / m_R S)-linear isomorphism
(S / m_R S) tensor_S B = B / m_R B identifies this flat module with the one displayed here.
Source: Stacks Project, Tag 00RH, displayed closed-fibre map and application of Tag 00R7.
(blueprint: lem-sbc-polynomial-chart-closed-fiber-module-flat) -/
theorem polynomial_chart_closedFiber_module_flat
    {X T : Scheme.{u}} (f : X ⟶ T) (U : X.Opens) (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    let p := (AffineSpace (ULift.{u} (Fin n)) T ↘ T)
    let R := T.presheaf.stalk (p (e x))
    let S := (AffineSpace (ULift.{u} (Fin n)) T).presheaf.stalk (e x)
    let B := U.toScheme.presheaf.stalk x
    let : Algebra R S := (p.stalkMap (e x)).hom.toAlgebra
    let : Algebra S B := (e.stalkMap x).hom.toAlgebra
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] B) := by
  let p := (AffineSpace (ULift.{u} (Fin n)) T ↘ T)
  let R := T.presheaf.stalk (p (e x))
  let S := (AffineSpace (ULift.{u} (Fin n)) T).presheaf.stalk (e x)
  let B := U.toScheme.presheaf.stalk x
  let α : R →+* S := (p.stalkMap (e x)).hom
  let β : S →+* B := (e.stalkMap x).hom
  let : Algebra R S := α.toAlgebra
  let : Algebra S B := β.toAlgebra
  let I := (IsLocalRing.maximalIdeal R).map α
  let J := I.map β
  let y := f (U.ι x)
  let m := PolynomialChart.fibreMap f U n e he y
  let z := PolynomialChart.fibrePoint f U x
  let i := (U.ι ≫ f).fiberι y
  let j := p.fiberι y
  have hx : i z = x := (U.ι ≫ f).fiberι_fiberHomeo_symm _ _
  have hsquare : m ≫ j = i ≫ e := polynomial_fibreMap_fiberι f U n e he y
  have hw : j (m z) = e x := by
    rw [← Scheme.Hom.comp_apply, hsquare, Scheme.Hom.comp_apply, hx]
  let ρS := ((AffineSpace (ULift.{u} (Fin n)) T).presheaf.stalkCongr
    (.of_eq hw.symm)).hom ≫ j.stalkMap (m z)
  let ρB := (U.toScheme.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ i.stalkMap z
  let ψ := (m.stalkMap z).hom
  have hψ : ψ.Flat := by
    dsimp [PolynomialChart.stalkMap] at hfibre
    have h₁ := (RingHom.Flat.respectsIso.cancel_right_isIso
      ((m.stalkMap z) ≫ inv ((PolynomialChart.fibreInclusion f U y).stalkMap z))
      (eqToHom (congrArg (f.fiber y).presheaf.stalk
        (PolynomialChart.fibreInclusion_asFiber f U x)))).mp hfibre
    exact (RingHom.Flat.respectsIso.cancel_right_isIso (m.stalkMap z)
      (inv ((PolynomialChart.fibreInclusion f U y).stalkMap z))).mp h₁
  have hkerS : RingHom.ker ρS.hom = I := by
    apply fibre_stalk_kernel p (e x) y _ (m z) hw
    exact congrArg (fun k : U.toScheme ⟶ T ↦ k x) he
  have hkerB : RingHom.ker ρB.hom = J := by
    rw [fibre_stalk_kernel (U.ι ≫ f) x y rfl z hx]
    dsimp only [J, I, α, β, R]
    rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    exact (maximalIdeal_map_stalkMap_congr (e ≫ p) (U.ι ≫ f) he x).symm
  have hc : ψ.comp ρS.hom = ρB.hom.comp β := by
    exact congrArg CommRingCat.Hom.hom (fibre_square_stalk_commutes e i j m
      hsquare z x hx hw)
  have hS : Function.Surjective ρS.hom :=
    (j.stalkMap_surjective (m z)).comp (ConcreteCategory.bijective_of_isIso _).2
  have hB : Function.Surjective ρB.hom :=
    (i.stalkMap_surjective z).comp (ConcreteCategory.bijective_of_isIso _).2
  have hflat := flat_quotientMap_of_flat β ρS.hom ρB.hom ψ I J
    Ideal.le_comap_map hS hB hkerS hkerB hc hψ
  let : Algebra (S ⧸ I) (B ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hmodule : Module.Flat (S ⧸ I) (B ⧸ J) := by
    apply RingHom.flat_algebraMap_iff.mp
    exact hflat
  let := hmodule
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv
end AlgebraicGeometry

