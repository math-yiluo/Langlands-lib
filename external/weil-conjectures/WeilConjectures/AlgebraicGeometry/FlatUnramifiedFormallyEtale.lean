/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallySmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.FlatOpenDiagonalConormalZero
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningConormalZero
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningExists

/-!
# Flat unramified morphisms are formally étale

Source: Stacks Project, More on Morphisms, Lemma 04FF and Definitions 02HG, 02H0
(blueprint: lem-weil-pbc-flat-unramified-formally-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An unramified flat morphism has a unique lift across every affine first-order
thickening; in particular it is formally smooth and formally étale.
Source: Stacks Project, More on Morphisms, Lemma 04FF and Definitions 02HG, 02H0
(blueprint: lem-weil-pbc-flat-unramified-formally-etale).
Proof (Stacks 04FF, with 04FE (3) implies (1)), following the node's seven steps:
1. By lem-weil-pbc-unramified-formally-unramified, `f` is formally unramified,
   giving uniqueness. Choose its universal first order thickening `X ⊆ X'`
   (lem-weil-pbc-universal-first-order-thickening-exists), with square-zero ideal
   `I` and conormal sheaf `C = I` pulled back to `X`.
2. Let `p, q : X ×[S] X ⟶ X` be the projections and let `D` be the open image
   of the diagonal. Then `q` is formally unramified by
   lem-weil-pbc-formally-unramified-base-change, and `p` is flat by
   lem-weil-pbc-flat-morphism-base-change. Both projections compose with the
   diagonal to the identity.
3. By lem-weil-pbc-universal-thickening-flat-base-change, `p* C ≅ C_q`.
4. On `D`, `q` is an isomorphism. By
   lem-weil-pbc-universal-thickening-open-restriction, `C_q` restricted to `D`
   is the conormal sheaf of this isomorphism, hence zero: its universal first
   order thickening is the identity with zero ideal, by the universal property
   and uniqueness of universal first order thickenings.
5. Pull the isomorphism of step 3 back along the diagonal. Functoriality of
   module pullback and lem-weil-pbc-open-immersion-module-pullback-restriction,
   together with step 4 and `p` composed with the diagonal being the identity,
   give `C ≅ 0`.
6. The defining ideal `I` of `X ⊆ X'` has square zero, so its pullback to `X`
   is `I/I² = I` under the homeomorphism of underlying spaces. Thus `C = 0`
   forces `I = 0`, and the immersion `X ⟶ X'` is an isomorphism. For the given
   square, the universal property of `X'` gives a map `T' ⟶ X'`; composing
   with the inverse immersion gives the desired lift to `X`, with both
   triangles commuting. Step 1 gives its uniqueness.
7. Unique lifting is Definition 02HG; forgetting uniqueness gives
   `FormallySmooth f` by Definition 02H0 (def-sbc-formally-smooth).
-/
theorem flat_unramified_formally_etale {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (h_unramified : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) :
    (∀ {T T' : Scheme.{u}} (i : T ⟶ T') [IsAffine T] [IsAffine T'] [T'.Over S],
      IsFirstOrderThickening i →
        ∀ (a : T ⟶ X), a ≫ f = i ≫ (T' ↘ S) →
          ∃! a' : T' ⟶ X, i ≫ a' = a ∧ a' ≫ f = T' ↘ S) ∧
      FormallySmooth f := by
  have : IsOpenImmersion (pullback.diagonal f) := h_unramified.2
  have : FormallyUnramified f := inferInstance
  obtain ⟨X', j, s, H⟩ := (FormallyUnramified.exists_universalFirstOrderThickening f).1
  have hC := flat_openDiagonal_conormal_isZero f j s H
  have : IsIso j := firstOrderThickening_isIso_of_conormal_isZero j H.1 hC
  have hlift : ∀ {T T' : Scheme.{u}} (i : T ⟶ T') (b : T' ⟶ S)
      (hi : IsFirstOrderThickening i) (a : T ⟶ X), a ≫ f = i ≫ b →
        ∃! a' : T' ⟶ X, i ≫ a' = a ∧ a' ≫ f = b := by
    intro T T' i b hi a ha
    obtain ⟨c, hc, _⟩ := H.2.2 i b a hi ha.symm
    have hc' : i ≫ (c ≫ inv j) = a ∧ (c ≫ inv j) ≫ f = b := by
      constructor
      · rw [← Category.assoc, hc.2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      · have hs : inv j ≫ f = s := by
          rw [← H.2.1, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
        rw [Category.assoc, hs, hc.1]
    refine ⟨c ≫ inv j, hc', ?_⟩
    intro d hd
    let _ : IsClosedImmersion i := hi.1
    apply FormallyUnramified.hom_ext i ⟨2, hi.2⟩ f
      (g₁ := d) (g₂ := c ≫ inv j)
    · exact hd.1.trans hc'.1.symm
    · exact hd.2.trans hc'.2.symm
  constructor
  · intro T T' i _ _ _ hi a ha
    exact hlift i (T' ↘ S) hi a ha
  · intro T T' i _ _ _ hi a ha
    exact (hlift i (T' ↘ S) hi a ha).exists

end AlgebraicGeometry
