/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Algebra.FiniteTypeLiftNilpotent

/-!
# Local finite type across a finite order thickening

Source: Stacks Project, More on Morphisms, Lemma 37.3.3 (Tag 09ZW), part (2)
(blueprint: lem-weil-pbc-thickening-lft-cartesian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- A surjective leg of a ring pushout identifies its source with a quotient.
-- The pushout universal property gives a surjection from the pushout to B/IB;
-- finite type passes through that surjection and the source quotient isomorphism.
private theorem quotient_finiteType_of_isPushout
    {A B C D : CommRingCat.{u}} (a : A ⟶ C) (b : A ⟶ B) (c : C ⟶ D) (d : B ⟶ D)
    (H : IsPushout a b c d) (ha : Function.Surjective a) (hc : c.hom.FiniteType) :
    RingHom.FiniteType (Ideal.quotientMap ((RingHom.ker a.hom).map b.hom)
      b.hom Ideal.le_comap_map) := by
  classical
  let I := RingHom.ker a.hom
  let J := I.map b.hom
  let e := RingHom.quotientKerEquivOfSurjective ha
  let q : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J b.hom Ideal.le_comap_map
  let k : C ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (q.comp e.symm.toRingHom)
  let l : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have w : a ≫ k = b ≫ l := by
    ext x
    change q (e.symm (a x)) = Ideal.Quotient.mk J (b x)
    have hx : e.symm (a x) = Ideal.Quotient.mk I x := by
      apply e.injective
      simp [e, I]
    rw [hx]
    rfl
  let t := H.desc k l w
  have ht : Function.Surjective t := by
    intro x
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := J) x
    refine ⟨d y, ?_⟩
    have eq := congrArg (fun f : B ⟶ CommRingCat.of (B ⧸ J) ↦ f y) (H.inr_desc k l w)
    exact eq.trans hy
  have hk : k.hom.FiniteType := by
    rw [← H.inl_desc k l w, CommRingCat.hom_comp]
    exact hc.comp_surjective ht
  have hq : q = k.hom.comp e.toRingHom := by
    ext x
    exact congrArg q (e.symm_apply_apply x).symm
  change q.FiniteType
  rw [hq]
  exact hk.comp (RingHom.FiniteType.of_surjective _ e.surjective)

-- Apply the affine section pushout to the inverse images of U and V.
private theorem finiteType_quotient_appLE_of_closed_baseChange
    {S S' X' : Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    [IsClosedImmersion i] [LocallyOfFiniteType (pullback.fst i f')]
    (U : S'.Opens) (hU : IsAffineOpen U) (V : X'.Opens) (hV : IsAffineOpen V)
    (e : V ≤ f' ⁻¹ᵁ U) :
    RingHom.FiniteType (Ideal.quotientMap
      ((i.ker.ideal ⟨U, hU⟩).map (f'.appLE U V e).hom)
      (f'.appLE U V e).hom Ideal.le_comap_map) := by
  let p := pullback.snd i f'
  let q := pullback.fst i f'
  let T := i ⁻¹ᵁ U
  let W := p ⁻¹ᵁ V
  have H : IsPullback p q f' i := (IsPullback.of_hasPullback i f').flip
  have hp : IsClosedImmersion p := inferInstance
  have hT : IsAffineOpen T := hU.preimage i
  have hW : IsAffineOpen W := hV.preimage p
  have hwle : W ≤ q ⁻¹ᵁ T := by
    change p ⁻¹ᵁ V ≤ q ⁻¹ᵁ (i ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
    exact p.preimage_mono e
  have hWY : W = p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ T := (inf_eq_left.mpr hwle).symm
  have hpush := (isIso_pushoutSection_iff H le_rfl e hWY).mp
    (isIso_pushoutSection_of_isAffineOpen H le_rfl e hWY hU hT hV)
  rw [i.ker_apply ⟨U, hU⟩, i.app_eq_appLE]
  have ha : Function.Surjective (i.appLE U T le_rfl) := by
    simpa only [T, Scheme.Hom.appLE_eq_app] using i.app_surjective U hU
  have hc := q.finiteType_appLE hT hW hwle
  exact quotient_finiteType_of_isPushout (i.appLE U T le_rfl)
    (f'.appLE U V e) (q.appLE T W hwle) (p.appLE V W le_rfl) hpush.flip ha hc

/-- A morphism is locally of finite type exactly when its base change along a finite order
thickening is locally of finite type.
Source: Stacks Project, Tag 09ZW, part (2)
(blueprint: lem-weil-pbc-thickening-lft-cartesian).

Proof:
1. Local finite type passes from `f'` to its base change
   (def-pc-base-change, lem-weil-pbc-lft-base-change; Stacks Tag 01T4).
2. For affine opens `U' = Spec A'` and `V' = Spec B'` with `f'(V') ⊆ U'`, the
   defining ideal `I` of `S` on `U'` is nilpotent (def-sbc-first-order-thickening,
   def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers). The inverse image of
   `V'` in the pullback is the affine open `Spec (B'/IB')` over `Spec (A'/I)`
   (lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   def-pc-fibre-product). This follows from the affine fibre product and the tensor
   description of the quotient by the extended ideal.
3. If the base change is locally of finite type, each `A'/I → B'/IB'` is of finite type
   (lem-weil-pbc-lft-affine-pairs, Stacks Tag 01T2). Lift its generators to `B'`.
   Nakayama applied to the resulting polynomial-algebra map gives finite type of
   `A' → B'` (lem-weil-pbc-finite-type-lift-nilpotent, Stacks Tag 00DV).
   Applying the affine-pairs criterion again gives local finite type of `f'`.
   The nilpotent ring lemma directly handles any finite order; the source instead
   reduces inductively to the square-zero case before this affine argument. -/
theorem locallyOfFiniteType_iff_of_finiteOrderThickening
    {S S' X' : Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    (hi : IsFiniteOrderThickening i) :
    LocallyOfFiniteType (pullback.fst i f') ↔ LocallyOfFiniteType f' := by
  constructor
  · intro h
    obtain ⟨n, hi, hn⟩ := hi
    let : IsClosedImmersion i := hi
    let : LocallyOfFiniteType (pullback.fst i f') := h
    constructor
    intro U hU V hV e
    apply finiteType_of_quotient_finiteType_nilpotent
      (f'.appLE U V e).hom (i.ker.ideal ⟨U, hU⟩)
    · refine ⟨n, ?_⟩
      have h := congrArg (fun J : S'.IdealSheafData ↦ J.ideal ⟨U, hU⟩) hn
      simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
        Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using h
    · exact finiteType_quotient_appLE_of_closed_baseChange i f' U hU V hV e
  · intro h
    exact MorphismProperty.pullback_fst i f' h

end AlgebraicGeometry
