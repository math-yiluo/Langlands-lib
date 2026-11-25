/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedCoproducts

/-!
# Proper direct image of unbounded complexes: statement

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-construction/sec-proper-direct-image-of-unbounded-complexes/
sk-lem-proper-unbounded-window/_section.md, assertions (1)--(3)
(blueprint: lemma-proper-direct-image-unbounded-complexes).

The theorem states the three assertions for both coefficient choices in the current
condensed model.  The two existing predicates expand the degreewise ind-constructible
condition, the two amplitude bounds, the canonical finite truncation window, and the
canonical arbitrary-direct-sum comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper direct image of unbounded ind-constructible complexes, with its finite
cohomological window and arbitrary direct sums, for both `E` and `ℚ̄_ℓ` coefficients.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-brown-construction/sec-proper-direct-image-of-unbounded-complexes/
sk-lem-proper-unbounded-window/_section.md, assertions (1)--(3); proof in
sk-lem-proper-unbounded-window.proof.md (blueprint: lemma-proper-direct-image-unbounded-complexes).

Proof plan, the eight steps of the DAG node:
1. Ambient setting: Dic and IndCons as in corollary-ambient-ind-derived and
proposition-ind-constructible-sheaves.
   The module categories are Grothendieck (prose-03-02), so
   prose-03-02 gives K-injective resolutions, and
   lem-pc-right-derived-functor-triangulated makes Rp_* (sk-def-sfb-module-derived-pushpull)
   exact and shift-compatible.
2. Bounded-below K: the spectral sequence of lemma-uniform-bound-proper-direct-image--1,
   E_2^{u,v} = R^u p_* H^v(K) => H^{u+v}(Rp_*K), has columns 0 <= u <= 2d+1 with
   ind-constructible terms by lemma-uniform-bound-proper-direct-image. Closure of IndCons under
   kernels, cokernels and extensions (proposition-ind-constructible-sheaves (2)) and the finite
   filtration give IndCons membership and both amplitude bounds.
3. Arbitrary K: proposition-left-completeness gives K = Rlim_n A_n, A_n = tau_ge(-n) K. Rp_* is a
   right adjoint, so it preserves products, and lem-pc-homotopy-limit-map gives
   Rp_*K = Rlim_n Rp_*A_n with the images of the canonical projections.
4. The fibre of A_(n+1) -> A_n is H^(-n-1)(K)[n+1], whose image lies in degrees
   [-n-1, 2d-n]. For fixed q the towers H^q and H^(q-1) of Rp_*A_n are eventually constant,
   so lim^1 = 0 (proposition-milnor-sequence) and H^q(Rp_*K) = H^q(Rp_*A_n) for large n. Step 2 then
   gives (1).
5. The triangles tau_le q K -> K -> tau_ge (q+1) K and tau_le (q-2d-2) K -> tau_le q K -> W_q K,
   W_q = tau_ge(q-2d-1) tau_le q (lem-sf-derived-truncation-triangle), with the bounds of (1)
   and lem-sf-derived-homology-long-exact, make both canonical arrows on H^q Rp_* invertible.
   Inverse of the first followed by the second is (6.5) in IndCons. This proves (2).
6. Sums: exact small sums in the Grothendieck categories; lem-kun-grothendieck-derived-coproducts,
   src-weil-derived-homology-preserves-coproducts and lem-sfb-derived-truncation-coproducts
   make cohomology and truncations commute with sums; sums of triangles are distinguished.
7. Families in a common finite interval [r,s]: induct on s-r. The single-degree case is the
   arbitrary-sum clause of lemma-uniform-bound-proper-direct-image with
   lem-weil-pbc-unbounded-derived-iso-cohomology; the induction uses the top-cohomology
   triangles and lem-sf-triangle-morphism-iso.
8. Arbitrary families: for each q the natural window isomorphisms of step 5 and step 6 identify
   H^q of the comparison with the comparison for W_q K_alpha in [q-2d-1,q], invertible by
   step 7. By lem-weil-pbc-unbounded-derived-iso-cohomology the comparison is invertible.
   This proves (3). -/
theorem properUnboundedWindow_statement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀]
    (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (_hk : Finite k ∨ IsAlgClosed k)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperUnboundedWindowAssertions (Profinite.continuousMapRingObj.{u} E) p d ∧
      ProperUnboundedCoproductAssertions (Profinite.continuousMapRingObj.{u} E) p ∧
      ProperUnboundedWindowAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d ∧
      ProperUnboundedCoproductAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p := by
  sorry

end AlgebraicGeometry.ProEtale
