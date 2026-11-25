/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularDivisorSpec
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion

/-!
# Intersections of principal closed subschemes of an affine scheme

For elements `a, b` of a ring `S` such that `(b, a)` is a weakly regular sequence, the
intersection `V(a) ∩ V(b) ⟶ Spec S` of the closed subschemes `V(a)` and `V(b)` is a regular
immersion of codimension two.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S : Type u} [CommRing S]

/-- If `[b, a]` is a weakly regular sequence of `S`, then `Spec (S/(a, b)) ⟶ Spec S` is a regular
immersion of codimension two. -/
theorem isRegularImmersion_specMap_quotient_span_pair {a b : S}
    (h : RingTheory.Sequence.IsWeaklyRegular S [b, a]) :
    IsRegularImmersion 2
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a, b})))) := by
  have hofList : Ideal.ofList [b, a] = Ideal.span {a, b} := by
    rw [Ideal.ofList, Set.pair_comm]
    congr 1
    ext r
    simp
  refine isRegularImmersion_specMap two_ne_zero _ Ideal.Quotient.mk_surjective [b, a] rfl h
    (by rw [Ideal.mk_ker, hofList]) 1 (map_one _) fun k hk ↦ ?_
  rw [Ideal.mk_ker] at hk
  rwa [one_mul, hofList]

/-- If `[b, a]` is a weakly regular sequence of `S`, the scheme-theoretic intersection of
`V(a)` and `V(b)` is a regular immersion of codimension two into `Spec S`. -/
theorem isRegularImmersion_pullback_fst_specMap_quotient {a b : S}
    (h : RingTheory.Sequence.IsWeaklyRegular S [b, a]) :
    IsRegularImmersion 2
      (pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {b})))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) := by
  have hspan : Ideal.span {a, b} = Ideal.span {a} ⊔ Ideal.span {b} := by
    rw [← Ideal.span_union, Set.singleton_union]
  have hI : Ideal.span {a} ≤ Ideal.span {a, b} := hspan ▸ le_sup_left
  have hJ : Ideal.span {b} ≤ Ideal.span {a, b} := hspan ▸ le_sup_right
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_factor hI hJ hspan.le)
  have := isRegularImmersion_specMap_quotient_span_pair h
  rw [← hp.isoPullback_inv_fst, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]
  infer_instance

end AlgebraicGeometry
