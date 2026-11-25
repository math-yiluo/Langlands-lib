/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility
import WeilConjectures.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionDiv
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Affine Picard torsion under extension of algebraically closed fields

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, affine case.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


-- Representative form of the divisible quotient torsion argument.
private theorem quotient_torsion_comparison
    {G H A B : Type*} [CommGroup G] [CommGroup H] [CommGroup A] [CommGroup B]
    (r : G →* A) (s : H →* B) (j : G →* H) (b : A →* B)
    (hr : Function.Surjective r) (hs : Function.Surjective s)
    (hc : ∀ x, s (j x) = b (r x)) (hi : Function.Injective j)
    (hk : ∀ y, s y = 1 → ∃ x, r x = 1 ∧ j x = y)
    (n : ℕ) (hd : Function.Surjective (fun x : G => x ^ n))
    (ht : ∀ y : H, y ^ n = 1 → ∃ x : G, x ^ n = 1 ∧ j x = y) :
    Function.Bijective (fun x : {x : A // x ^ n = 1} =>
      (⟨b x.val, by rw [← map_pow, x.property, map_one]⟩ : {y : B // y ^ n = 1})) := by
  constructor
  · intro x y hxy
    obtain ⟨a, ha⟩ := hr x.val
    obtain ⟨a', ha'⟩ := hr y.val
    have h : s (j (a / a')) = 1 := by
      rw [hc, map_div, ha, ha', map_div]
      exact div_eq_one.mpr (congrArg Subtype.val hxy)
    obtain ⟨l, hl, hjl⟩ := hk _ h
    have he : a / a' = l := hi hjl.symm
    apply Subtype.ext
    apply div_eq_one.mp
    rw [← ha, ← ha', ← map_div, he, hl]
  · intro y
    obtain ⟨a, ha⟩ := hs y.val
    have hna : s (a ^ n) = 1 := by rw [map_pow, ha, y.property]
    obtain ⟨l, hl, hjl⟩ := hk _ hna
    obtain ⟨z, hz⟩ := hd l
    change z ^ n = l at hz
    have hdiff : (a / j z) ^ n = 1 := by
      rw [div_pow, ← map_pow, hz, hjl, div_self']
    obtain ⟨t, ht, hjt⟩ := ht _ hdiff
    have hzt : j (z * t) = a := by
      rw [map_mul, hjt]
      simp
    have hpow : r (z * t) ^ n = 1 := by
      rw [← map_pow, mul_pow, ht, mul_one, hz, hl]
    refine ⟨⟨r (z * t), hpow⟩, Subtype.ext ?_⟩
    change b (r (z * t)) = y.val
    rw [← hc, hzt, ha]

/-- Pullback on the `n`-torsion of the Picard group of a smooth connected affine curve
is bijective under extension of algebraically closed fields.

Source:
literature/blueprint/master/blueprint/sec-curve-estimates/sbc-thm-algebraically-closed-invariance/
_section.md, affine case (blueprint: lem-sc-affine-picard-torsion-base-change).

Proof: Choose a smooth proper connected compactification by lemma-proper-smooth-model--1.
Its boundary cannot be empty: otherwise the open immersion is an isomorphism, making the
original curve proper and affine; lem-sc-proper-affine-finite contradicts its dimension one.
Choose a closed boundary point using the closedness of every boundary point. Apply
lem-sc-pic-affine-base-change-compatibility to get presentations G/Λ and G'/Λ' of the two
Picard groups, compatible with restriction and pullback, and an isomorphism Λ ≃* Λ'.
The compactification's degree-zero Picard group is n-divisible by
lem-sc-pic-proper-ntorsion-div. The comparison j on its degree-zero subgroup is injective,
and lifts n-torsion elements, by lem-sc-piczero-torsion-base-change.
For injectivity on the quotients, lift two classes to a and a'. Equality of their images
means j(a/a') belongs to Λ'. Lift it to l in Λ; injectivity gives a/a'=l, so the original
classes agree. For surjectivity, lift a torsion class to y in G'. Then y^n belongs to Λ'.
Lift it to l in Λ, choose z in G with z^n=l, and lift the n-torsion element y/j(z) to t in G.
Now j(z*t)=y and (z*t)^n=l, so its quotient class is torsion and maps to the prescribed
class. This representative argument is proved in the private quotient_torsion_comparison
lemma and does not require the full torsion short exact sequence. Finally, pullback along
hπ.isoPullback is bijective on torsion, with inverse pullback along its inverse. Functoriality
and hπ.isoPullback_hom_fst identify the composite with the specified Pic.map π.
For n=1 both torsion types are singletons; n=0 is excluded by the given hypotheses. -/
theorem affine_picard_torsion_base_change
    (k k' : Type u) [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (P : Scheme.{u}) (π : P ⟶ C) (g : P ⟶ Spec (.of k'))
    (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
    Function.Bijective (fun x : {x : C.Pic // x ^ n = 1} =>
      (⟨Scheme.Pic.map π x.1, by
        change (Scheme.Pic.mapHom π x.1) ^ n = 1
        rw [← map_pow, x.2, map_one]⟩ : {x : P.Pic // x ^ n = 1})) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  obtain ⟨c, hc, hs, hfin, hcl⟩ := IsConnectedCurve.exists_smooth_properCompactification f
  let := hc
  let := hs
  have : ConnectedSpace c.Z := IsConnectedCurve.connectedSpace (f := c.g)
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IsIntegral c.Z := IsRegular.isIntegral c.Z
  have hsm : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := c.g))
  let := hsm
  have hsm' : SmoothOfRelativeDimension 1 (c.baseChange b).g := by
    change SmoothOfRelativeDimension 1 (pullback.snd c.g b)
    infer_instance
  let := hsm'
  have hboundary : (Set.range c.i.base)ᶜ.Nonempty := by
    by_contra hempty
    have hrange : Set.range c.i.base = Set.univ := by
      simpa only [Set.nonempty_compl, not_not] using hempty
    have hi : c.i.opensRange = ⊤ := TopologicalSpace.Opens.ext hrange
    have : IsIso c.i := isIso_of_isOpenImmersion_of_opensRange_eq_top c.i hi
    have : IsProper f := by rw [c.comm]; infer_instance
    have hdim := (isFinite_of_isProper_of_isAffine f).2
    rw [IsConnectedCurve.krullDim_eq_one (f := f)] at hdim
    exact (by norm_num : ¬ (1 : WithBot ℕ∞) ≤ 0) hdim
  obtain ⟨p, hp⟩ := hboundary
  let P₀ : closedPoints c.Z := ⟨p, hcl p hp⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _,
    G, hG, Λ, e, G', hG', Λ', e', j, hj, _, hrest⟩ :=
    pic_affine_base_change_compatibility (k' := k') f c P₀ hp
  obtain ⟨_, _, hrest'⟩ := hrest 1
  obtain ⟨_, hej, hrest''⟩ := hrest' 1
  have hjmap (L : c.Z.Pic) := (hrest'' L).1
  have hcompat := (hrest'' 1).2
  let j₀ : G →* G' :=
    { toFun L := ⟨j L.val, hj L⟩
      map_one' := Subtype.ext (j.map_one)
      map_mul' L M := Subtype.ext (j.map_mul L.val M.val) }
  obtain ⟨hinj, htors⟩ := picZero_torsion_base_change c.g G hG G' hG' j₀
    (fun L => hjmap L.val) n hn
  let r : G →* C.Pic := e.toMonoidHom.comp (QuotientGroup.mk' Λ)
  let s : G' →* (pullback f b).Pic := e'.toMonoidHom.comp (QuotientGroup.mk' Λ')
  have hr : Function.Surjective r := e.surjective.comp QuotientGroup.mk_surjective
  have hs' : Function.Surjective s := e'.surjective.comp QuotientGroup.mk_surjective
  have hcomm : ∀ L, s (j₀ L) = Scheme.Pic.mapHom (pullback.fst f b) (r L) :=
    hcompat
  have hker : ∀ y, s y = 1 → ∃ x, r x = 1 ∧ j₀ x = y := by
    intro y hy
    have hyΛ : y ∈ Λ' := by
      change e' (QuotientGroup.mk y) = 1 at hy
      rw [← e'.map_one, e'.injective.eq_iff, QuotientGroup.eq_one_iff] at hy
      exact hy
    obtain ⟨ej, he⟩ := hej
    let x : Λ := ej.symm ⟨y, hyΛ⟩
    refine ⟨x.val, ?_, ?_⟩
    · change e (QuotientGroup.mk x.val) = 1
      rw [(QuotientGroup.eq_one_iff _).mpr x.property, e.map_one]
    · apply Subtype.ext
      exact (he x).symm.trans (congrArg (fun z : Λ' => z.val.val)
        (ej.apply_symm_apply ⟨y, hyΛ⟩))
  have hdiv : Function.Surjective (fun x : G => x ^ n) := by
    intro L
    obtain ⟨M, hM, hpow⟩ := c.g.pic_proper_ntorsion_div n hn L.val (by
      rw [← hG]; exact L.property)
    refine ⟨⟨M, by change M ∈ (G : Set c.Z.Pic); rw [hG]; exact hM⟩, ?_⟩
    exact Subtype.ext hpow
  have hcanonical := quotient_torsion_comparison r s j₀
    (Scheme.Pic.mapHom (pullback.fst f b)) hr hs' hcomm hinj hker n hdiv htors
  let E := hπ.isoPullback
  let t := Scheme.Pic.mapHom E.hom
  have ht : Function.Bijective (fun x : {x : (pullback f b).Pic // x ^ n = 1} =>
      (⟨t x.val, by rw [← map_pow, x.property, map_one]⟩ : {x : P.Pic // x ^ n = 1})) := by
    have htinv (L : (pullback f b).Pic) : Scheme.Pic.map E.inv (t L) = L := by
      change Scheme.Pic.map E.inv (Scheme.Pic.map E.hom L) = L
      rw [← Scheme.Pic.map_comp, E.inv_hom_id, Scheme.Pic.map_id]
    have htinverse (L : P.Pic) : t (Scheme.Pic.map E.inv L) = L := by
      change Scheme.Pic.map E.hom (Scheme.Pic.map E.inv L) = L
      rw [← Scheme.Pic.map_comp, E.hom_inv_id, Scheme.Pic.map_id]
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact (htinv x.val).symm.trans
        ((congrArg (Scheme.Pic.map E.inv) (congrArg Subtype.val hxy)).trans (htinv y.val))
    · intro y
      refine ⟨⟨Scheme.Pic.map E.inv y.val, ?_⟩, Subtype.ext (htinverse y.val)⟩
      change (Scheme.Pic.mapHom E.inv y.val) ^ n = 1
      rw [← map_pow, y.property, map_one]
  have hresult := ht.comp hcanonical
  convert hresult using 1
  funext x
  apply Subtype.ext
  change Scheme.Pic.map π x.val = Scheme.Pic.map E.hom
    (Scheme.Pic.map (pullback.fst f b) x.val)
  rw [← Scheme.Pic.map_comp, hπ.isoPullback_hom_fst]

end AlgebraicGeometry
