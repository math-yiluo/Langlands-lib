/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyAffineComparison
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyQcqsGluing
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Finite-stage detection of a zero limit cohomology class

Source: Stacks Project, Tags 09YQ, 09YP, 0EYL and 0A50.
(blueprint: lem-weil-pbc-etale-limit-cohomology-eventual-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Finite-stage detection of a zero limit cohomology class.

Source: Stacks Project, Theorem 09YQ (theorem-colimit), via 0EYL and 09YP;
the qcqs gluing argument uses 0A50 and the parent node steps 2-8.
(blueprint: lem-weil-pbc-etale-limit-cohomology-eventual-vanishing).

Proof:
Pass to the cofinal tail above a chosen stage. Initiality for scheme limits and
finality for filtered colimits preserve the limit cone, the sheaf colimit, and the
canonical comparison. When that stage is affine, every scheme on the tail is affine.
Use the affine etale site colimit presentation (0EYL), including its strictification,
and the affine etale restriction equivalence (04HR). Base-change direct images agree
on affine objects; uniqueness of their left adjoints identifies inverse images,
compatibly with the adjunction units and composition. Transport F, phi, G and L
through these equivalences. Apply cohomology_colimit_of_sites (09YP) at the final
affine object. Its object-cohomology is global cohomology. The unit-compatible
comparisons identify its transition maps with hH and its legs with hB, so they
establish affine continuity for the specified comparison, in every degree.

For a quasi-compact open of a stage, restrict on the cofinal tail to its inverse
images. Limits commute with these restrictions (01YX); transitions remain affine,
and the restricted schemes are qcqs. Inverse image preserves the sheaf colimit,
so these are systems of exactly the same kind. For a cover by two quasi-compact
opens, Mayer-Vietoris (0A50), its pullback compatibility, and its naturality in
coefficients give a map from the filtered colimit of the stage long exact sequences
to the sequence on the limit. Filtered group colimits are exact. If comparisons on
the opens and their intersection are isomorphisms in all degrees, the five lemma
makes the comparison on their union an isomorphism; degree zero uses the initial
zero terms of the same exact sequences.

Induct first on a finite affine cover of a separated stage. The base with no opens
is empty and has zero cohomology; the single-open case is affine. Split a larger
cover into one affine U and the union V of the remaining affines. V and U intersect V
have covers with fewer affines, since intersections of affine opens of a separated
scheme are affine. Induction and the preceding gluing argument apply. Then induct
on a finite affine cover of an arbitrary qcqs stage. V has fewer affines, U is affine,
and U intersect V is a quasi-compact separated open in U, covered by the first
induction. Gluing again gives the canonical comparison for the whole stage.
Compactness supplies the initial finite affine cover. All these operations respect
the specified cohomology legs by pullback functoriality; the isomorphisms eG, eH and
eB merely transport objects and do not change any image or kernel assertion.

Take x in H.obj i whose specified image in B.pt is zero. The injective
canonical comparison just constructed implies that the image of x in the filtered
group colimit is zero. In a filtered colimit, equality of two stage elements is
witnessed at a common later stage. Apply this to x and zero at i. There exist j
and f : i to j such that (H.map f).hom x = (H.map f).hom 0 = 0. This proves
finite-stage detection of zero only; it does not provide representatives of arbitrary
classes of B.pt.

Edge cases: x = 0 is killed by the identity at i. Zero sheaves and empty schemes
satisfy this case. Degree zero is the equality-of-sections case. A one-object index
reduces to injectivity of the canonical comparison.
-/
theorem etale_limit_cohomology_eventual_vanishing
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p)) :
    ∀ (i : I) (x : H.obj i), (B.ι.app i).hom x = 0 →
      ∃ (j : I) (f : i ⟶ j), (H.map f).hom x = 0 := by
  obtain ⟨hBcolim⟩ := etale_limit_cohomology_qcqs_gluing
    @etale_limit_cohomology_affine_comparison
    D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  intro i x hx
  obtain ⟨j, f, _, hf⟩ := Concrete.isColimit_exists_of_rep_eq H hBcolim
    x (0 : H.obj i) (by simpa only [map_zero] using hx)
  exact ⟨j, f, by simpa only [map_zero] using hf⟩

end AlgebraicGeometry.Etale
