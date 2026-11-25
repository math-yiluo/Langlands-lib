/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions

import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedComparisons
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # Finite Tate descent

Source: Stacks Project, Tags 03PK and 099R
(blueprint: lem-amb-finite-tate-site-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

private theorem comparison_iso_lift_unique
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C} {Z : D}
    (a : F.obj Y ≅ Z) (b : F.obj X ≅ Z) :
    ∃! h : X ≅ Y, F.mapIso h ≪≫ a = b := by
  let e := (Functor.FullyFaithful.ofFullyFaithful F).isoEquiv (X := X) (Y := Y)
  refine ⟨e.symm (b ≪≫ a.symm), ?_, ?_⟩
  · change e (e.symm (b ≪≫ a.symm)) ≪≫ a = b
    simp
  · intro h hh
    apply e.injective
    change F.mapIso h = _
    rw [Equiv.apply_symm_apply]
    calc
      F.mapIso h = (F.mapIso h ≪≫ a) ≪≫ a.symm := by simp
      _ = b ≪≫ a.symm := by rw [hh]

/-- The finite pro-etale Tate twists descend canonically, with the specified root
normalization, all nonnegative tensor powers, pullback squares, exponent transitions,
and uniqueness of the descent with its comparison. Both positive exponents are indexed
by their predecessor: the finite quotient is at `n+1`, and the annihilator is `l^(r+1)`.
There is no condition relating `n+1` to the ramification index.
Source: Stacks Project, Tags 03PK, 099R, 0GLZ, 099T and 03EL;
finite reduction in `lem-pur-twist-sheaf-locally-free`, clauses (2)--(3)
(blueprint: lem-amb-finite-tate-site-descent).

Proof plan:
1. Write L for the recorded root limit and C for completed Z_l. Its specified finite
   reduction is L tensor_C Z/l^(r+1), identified with the finite roots by the root projection.
   The constant-completion equivalence identifies the coefficient quotient with Z/l^(r+1).
2. Reassociate the two discrete coefficient tensors defining purTwistFiniteOne, obtaining
   L tensor_Z_l A. Since l^(r+1)A=0, quotienting L by that power before tensoring gives the
   same sheaf. The mutually inverse pure-tensor maps use no flatness of A over Z/l^(r+1).
3. The comparison-pullback section formula and etale finite-root pullback identify the
   inverse image of the etale root sheaf with the pro-etale root sheaf. Both restrictions
   and power transitions act on the same units; the constant coefficient maps agree.
4. Inverse image preserves the balanced tensor coequalizer and the canonical scalar maps.
   Compose this tensor comparison with the inverse finite reduction of step 2. It sends
   every etale root tensor to the specified pro-etale root-limit tensor on local lifts.
   This is IsFiniteTateSiteComparison, including arbitrary pro-etale tests over etale U.
5. For larger r', the identity p_r = power(r',r) p_r' proves the transition square on
   generators. The etale finite-twist theorem makes this transition invertible. Its power
   formula composes, and a common larger exponent compares any two annihilators canonically.
6. For scheme pullback, the compatible pulled-back finite root projections induce the
   map to the root limit by its universal property. Do not commute inverse image with
   that infinite limit. Tensor with A and apply finite reduction; the resulting comparison
   is invertible. Its generator formula and the etale root pullback give the displayed
   comparison square. These same formulas determine identity and composition comparisons.
7. At tensor exponent zero use the constant coefficient map. At positive exponents tensor
   the first comparison repeatedly, using the sheafification-unit tensor generators.
   They give precisely the recorded powers on both sides, with the normalizations below.
   Thus all transition and pullback squares tensor factor by factor. In the derived
   categories use K-flat total tensors of proposition-open-direct-image-preserves-finite; exact
   comparison acts termwise and its canonical derived tensor comparison carries these same
   degree-zero isomorphisms, so the construction has the stipulated derived tensor convention.
8. The comparison unit is invertible for module sheaves, so inverse image is fully
   faithful. Lift alpha inverse composed with beta, and its inverse, uniquely. Faithfulness
   gives their inverse identities and the unique comparison-preserving isomorphism.
   The zero tensor power and the empty scheme are included throughout.
-/
theorem finite_tate_site_descent :
    ∃ b : ∀ (T : Scheme.{u}), IsUnit (l : Γ(T, ⊤)) →
      ∀ (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k,
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      IsFiniteTateSiteComparison l E n T r hA k (b T hT r hA k)) ∧
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
          (finiteTateProSheaf l E n T k) ≅ finiteTateProSheaf l E n T' k),
      IsFiniteTateEtalePullback l E n T v r hA k c ∧
      IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).mapIso
          (b T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').mapIso c ≪≫ b T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃! t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapIso t ≪≫ b T hT r hA k =
            b T hT r' hA' k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
      (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
      (alpha : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj G ≅
          finiteTateProSheaf l E n T k),
      ∃! h : finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k ≅ G,
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).mapIso h ≪≫ alpha =
            b T hT r hA k) := by
  classical
  obtain ⟨b, hb⟩ := finite_tate_normalized_comparisons l E n
  obtain ⟨hp, ht⟩ := finite_tate_normalized_coherence l E n b hb
  refine ⟨b, hb, hp, ?_, ?_⟩
  · intro T hT r r' hrr hA hA' k
    obtain ⟨t, htn, hts⟩ := ht T hT r r' hrr hA hA' k
    obtain ⟨q, hq, hqu⟩ := comparison_iso_lift_unique
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
      (b T hT r hA k) (b T hT r' hA' k)
    refine ⟨t, ⟨htn, hts⟩, ?_⟩
    intro t' ht'
    exact (hqu t' ht'.2).trans (hqu t hts).symm
  · intro T hT r hA k G alpha
    exact comparison_iso_lift_unique
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
      alpha (b T hT r hA k)

end AlgebraicGeometry.Scheme
