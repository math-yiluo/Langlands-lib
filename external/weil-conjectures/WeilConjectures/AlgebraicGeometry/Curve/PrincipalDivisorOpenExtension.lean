/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor

/-! # Divisor restriction across a smooth curve compactification -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

private theorem ring_ord_equiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : R) : Ring.ord S (e r) = Ring.ord R r := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  let eo := Submodule.orderIsoMapComap e.toSemilinearEquiv
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient]
  have h := Order.coheight_orderIso eo (Ideal.span {r})
  simpa [eo, Submodule.orderIsoMapComap, Submodule.orderIsoMapComapOfBijective,
    Submodule.map_span, Set.image_singleton] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ring_ordMonoid_equiv {R S : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (e : R ≃+* S) (r : R) :
    Ring.ordMonoidWithZeroHom S (e r) = Ring.ordMonoidWithZeroHom R r := by
  have hn : (e r ∈ nonZeroDivisors S) ↔ (r ∈ nonZeroDivisors R) := by
    constructor
    · intro h
      exact mem_nonZeroDivisors_iff_ne_zero.mpr
        (e.map_ne_zero_iff.mp (mem_nonZeroDivisors_iff_ne_zero.mp h))
    · intro h
      exact mem_nonZeroDivisors_iff_ne_zero.mpr
        (e.map_ne_zero_iff.mpr (mem_nonZeroDivisors_iff_ne_zero.mp h))
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    ring_ord_equiv e r]
  split_ifs with hS hR hR
  · rfl
  · exact False.elim (hR (hn.mp hS))
  · exact False.elim (hS (hn.mpr hR))
  · rfl

private theorem ring_ordFrac_equiv {R S K L : Type u}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (e : R ≃+* S) (eK : K ≃+* L)
    (hcomm : ∀ r : R, eK (algebraMap R K r) = algebraMap S L (e r)) (a : K) :
    Ring.ordFrac S (eK a) = Ring.ordFrac R a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective R a
  have hr : r ≠ 0 := by
    intro hr
    apply ha
    rw [← hrs, hr, map_zero, zero_div]
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  rw [← hrs, map_div₀, hcomm, hcomm, map_div₀, map_div₀,
    Ring.ordFrac_eq_ord S (e.map_ne_zero_iff.mpr hr),
    Ring.ordFrac_eq_ord S (e.map_ne_zero_iff.mpr hs0),
    Ring.ordFrac_eq_ord R hr, Ring.ordFrac_eq_ord R hs0,
    ring_ordMonoid_equiv, ring_ordMonoid_equiv]

namespace AlgebraicGeometry

/-- Order is invariant under compatible isomorphisms of local rings and function fields.
Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine, first paragraph,
restriction and boundary divisors.

Proof: if the common coheight is not one, both orders are zero by definition. Otherwise
both stalks are Noetherian domains of Krull dimension one. The local ring equivalence
identifies the principal quotients by r and by e(r), including their submodule lattices;
therefore their module lengths agree. Thus the ring order maps agree on all nonzero stalk
elements. Every function-field element is a quotient of two such elements, and the assumed
commuting square takes this quotient to the corresponding quotient in the other field.
The multiplicative fraction order maps agree by multiplicativity and the quotient formula.
For zero both orders are zero; for nonzero elements taking the additive exponent proves
the asserted equality. This includes constant units and points of other codimension. -/
private theorem ord_eq_of_stalk_equiv
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (x : X) (y : Y) (e : X.presheaf.stalk x ≃+* Y.presheaf.stalk y)
    (eK : X.functionField ≃+* Y.functionField)
    (hcomm : ∀ r : X.presheaf.stalk x,
      eK (algebraMap (X.presheaf.stalk x) X.functionField r) =
        algebraMap (Y.presheaf.stalk y) Y.functionField (e r))
    (hheight : Order.coheight x = Order.coheight y) (a : X.functionField) :
    Y.ord (eK a) y = X.ord a x := by
  by_cases hx : Order.coheight x = 1
  · have hy : Order.coheight y = 1 := hheight.symm.trans hx
    let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
    have hfrac := ring_ordFrac_equiv e eK hcomm a
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy,
      Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
    change Multiplicative.toAdd ((Ring.ordFrac (Y.presheaf.stalk y) (eK a)).unzeroD 1) =
      Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk x) a).unzeroD 1)
    rw [hfrac]
  · have hy : Order.coheight y ≠ 1 := by simpa [← hheight] using hx
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]


/-- A principal divisor on the open curve has a principal extension with identical orders.
Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine, first paragraph,
restriction and boundary divisors
(blueprint: lem-sc-principal-divisor-open-extension).

Proof: a nonempty open subset of an integral scheme contains its generic point. Hence the
open immersion of the connected smooth curve into its integral compactification identifies
both generic stalks, and thus both function fields. Transport the given unit through the
inverse of this field isomorphism to a unit b on Z. At Q and its image P the open immersion
identifies local rings and the maps into the common function field. The discrete valuation
rings therefore have identical normalized valuations: a uniformizer maps to a uniformizer,
and units map to units. Applying this to the given rational function yields the displayed
coefficient equality. No choice of a divisor or trivial Picard class is used, and no boundary
order is prescribed. For a constant unit all retained orders vanish; an empty boundary
simply makes the equality hold at every ambient closed point. -/
theorem Scheme.Hom.exists_principal_divisor_open_extension
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [IsIntegral C] [IsNoetherian C] [IsIntegral c.Z] [IsNoetherian c.Z]
    (a : Additive C.functionFieldˣ) :
    ∃ b : Additive c.Z.functionFieldˣ,
      ∀ (P : closedPoints c.Z) (Q : closedPoints C), c.i.base Q.val = P.val →
        c.Z.div b P = C.div a Q := by
  classical
  have _hsm := hsm
  have hη := genericPoint_eq_of_isOpenImmersion c.i
  let e : c.Z.functionField ≃+* C.functionField :=
    ((c.Z.presheaf.stalkCongr (.of_eq hη.symm)) ≪≫
      asIso (c.i.stalkMap (genericPoint C))).commRingCatIsoToRingEquiv
  let b : Additive c.Z.functionFieldˣ :=
    Additive.ofMul (Units.map e.symm.toMonoidHom a.toMul)
  refine ⟨b, ?_⟩
  intro P Q hPQ
  let eq : c.Z.presheaf.stalk (c.i Q.val) ≃+* C.presheaf.stalk Q.val :=
    (asIso (c.i.stalkMap Q.val)).commRingCatIsoToRingEquiv
  have hcomm : ∀ r : c.Z.presheaf.stalk (c.i Q.val),
      e (algebraMap (c.Z.presheaf.stalk (c.i Q.val)) c.Z.functionField r) =
        algebraMap (C.presheaf.stalk Q.val) C.functionField (eq r) := by
    intro r
    change c.i.stalkMap (genericPoint C)
        ((c.Z.presheaf.stalkCongr (.of_eq hη.symm)).hom
          (c.Z.presheaf.stalkSpecializes (genericPoint_specializes (c.i Q.val)) r)) =
      C.presheaf.stalkSpecializes (genericPoint_specializes Q.val) (c.i.stalkMap Q.val r)
    simp only [TopCat.Presheaf.stalkCongr_hom]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact c.i.stalkSpecializes_stalkMap_apply (genericPoint C) Q.val
      (genericPoint_specializes Q.val) r
  have hheight : Order.coheight (c.i Q.val) = Order.coheight Q.val :=
    c.i.isOpenEmbedding.coheight_eq c.i.base
  have hord := ord_eq_of_stalk_equiv (c.i Q.val) Q.val eq e hcomm hheight
    (e.symm (a.toMul : C.functionField))
  simp only [e.apply_symm_apply] at hord
  rw [Scheme.div_apply, Scheme.div_apply, ← hPQ]
  exact hord.symm

end AlgebraicGeometry
