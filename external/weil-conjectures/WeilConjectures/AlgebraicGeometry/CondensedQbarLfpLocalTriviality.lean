/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition

/-!
# Local triviality for bounded-image condensed algebraic-closure coefficients

Source: ConstructibleSheaf/ProEtaleModule/Def.lean, IsLocallyFinitelyPresented and its
module docstring; RefactorInstruction.tex, Section 4; Bhatt--Scholze, Definition 6.8.3
(auxiliary; not a blueprint node).

The coefficient ring is the bounded-finite-subextension-image condensed ring, pulled
back from the profinite point. Presentations and restrictions are ordinary module
sheaf constructions; there is no completeness hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Local finite presentation implies pro-etale local finite freeness for the
bounded-image condensed algebraic closure of the l-adic field.

Source: ConstructibleSheaf/ProEtaleModule/Def.lean, IsLocallyFinitelyPresented;
RefactorInstruction.tex, Section 4, prop:Qbar-X and prop:continuous-X;
Bhatt--Scholze, Definition 6.8.3
(auxiliary; not a blueprint node).

Proof plan:
1. Refine the presentation cover by affine weakly contractible objects
(lemma-constructible-sheaves--8). Exact inverse image and
forgetfulness preserve ordinary cokernel presentations
(lemma-constructible-sheaves--8,
situation-conventions). Use coefficient composition comparisons
(lemma-constructible-sheaves--8). Basis evaluation
(lemma-constructible-sheaves--8) makes each finite matrix a matrix of
bounded-image functions; directedness (lemma-constructible-sheaves--8) puts
all entries in one finite field. The coefficient-realization clause of
lemma-constructible-sheaves--8, applied over the original noetherian base,
identifies these sections with continuous functions on each covering object.
2. Evaluate at geometric points (lemma-constructible-sheaves--8).
Covers stay covers under base change (lemma-constructible-sheaves--8,
lemma-constructible-sheaves--8,
lemma-constructible-sheaves--8). Sections of covers over algebraically closed
fields give finite-dimensional fibres. Extension invariance makes their dimension
intrinsic, and evaluation of the presentation gives n minus the pointwise matrix rank.
Rank does not change on extending the finite coefficient field to the closure.
3. Lift generalizations along the flat covering maps by flat going down
(lemma-constructible-sheaves--8, lemma-constructible-sheaves--8). Continuous functions into the
Hausdorff finite field are constant on specializations, so fibre rank is too.
4. Finitely many irreducible components and their generic points
(lemma-constructible-sheaves--8, lemma-constructible-sheaves--8) show that rank
levels downstairs are clopen: each and its complement are finite unions of components.
No noetherianity of the covering objects is used.
5. On the inverse image of each rank level, cover by the open nonvanishing loci of
maximal-rank minors; for rank zero use the entire object. These are pro-etale covers
(definition-small-pro-etale-site--1). Exact restriction preserves the presentations.
6. Invert the chosen minor using adjugate divided by determinant. The inverse entries
are continuous functions in the same finite field, hence actual coefficient sections
by lemma-constructible-sheaves--8. Block row and column operations reduce
the matrix to an identity block and its Schur complement. Constant pointwise rank
forces the latter to be the zero function, hence the zero section. The cokernel is
therefore finite free. At rank zero all entries vanish and the cokernel is the target.
7. Compose the refinement, rank-level and minor-locus covers. Omit empty pieces; the
empty scheme permits the empty cover. Empty rows, columns and rank-zero blocks need
no inverse. All steps concern ordinary cokernels, with no derived completeness. -/
theorem condensedQbar_lfp_locally_free (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) P) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒲.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (𝒲.f i)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (𝒲.X i)) r) := by
  classical
  rcases hP with ⟨𝒰, h𝒰⟩
  have h0 (i : 𝒰.I₀) := exists_condensedQbar_finiteFree_refinement ℓ X (𝒰.X i)
    (𝒰.f i) (𝒰.forgetQc.map_prop i) P (h𝒰 i)
  exact exists_condensedQbar_refinement_of_local ℓ X P 𝒰 h0

end AlgebraicGeometry.ProEtale
