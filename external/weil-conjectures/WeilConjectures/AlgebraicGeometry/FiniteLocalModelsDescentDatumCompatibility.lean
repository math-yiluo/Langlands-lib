/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityTransport
/-!
# Compatible transport on an etale local representative

Source: Stacks Project, Tag 03RV and Descent Tag 02W5.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum-compatibility)
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- A representation on the localized small site induces compatible scheme descent data.

Source: Stacks Project, Tag 03RV, construction of the overlap datum from representations;
Descent Tag 02W5, Yoneda comparison of representations.
(blueprint: lem-weil-pbc-finite-local-models-descent-datum-compatibility)

Proof: Let q be the structure map of Q and g the structure map of U. Over U times_T U, the
two pullbacks of Q both represent the restriction of E: pull back e along the two
projections, which are etale. Yoneda full faithfulness on the small etale site of the overlap
gives the comparison isomorphism. Its pullbacks to U times_T U times_T U satisfy the cocycle,
because under their representation isomorphisms they are the identity on the restriction
of E. Yoneda faithfulness proves equality; the diagonal comparison is the identity for
the same reason. These isomorphisms define transport for points from arbitrary schemes by
pullback along the pair of maps to U. This transport is natural in the source scheme by
functoriality of pullbacks, and the diagonal and triple-product identities give transport_self
and transport_transport. Although E is defined only on the small site, every comparison is
constructed there: the overlap projections, and the pullbacks of Q, are etale. For arbitrary
source schemes the comparison scheme morphism is simply base changed; E is not evaluated
there. On an etale W, the comparison was defined to identify the same section of E under
the two restrictions of e. Applying it to the point given by e at (W,a,s) therefore gives
exactly the point given by e at (W,b,s), proving the displayed equation. This includes empty
schemes by the empty-cover sheaf axiom. Surjectivity of U is not needed for this construction;
finiteness of Q is preserved but not used in constructing transport. -/
theorem finiteLocalModels_descentDatum_compatibility
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale)
    (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    ∃ d : Over.DescentDatum U.hom (Over.mk Q.obj.hom),
      ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (d.transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left := by
  obtain ⟨t⟩ := finiteLocalModels_descentDatum_compatibility_datum T E U Q e
  obtain ⟨hself, hcomp⟩ := finiteLocalModels_descentDatum_compatibility_transport T E U Q e t
  let d : Over.DescentDatum U.hom (Over.mk Q.obj.hom) :=
    { transport := t.transport
      transport_homMk_comp := t.naturality
      transport_self := fun a x ↦ hself _ a x
      transport_transport := fun a b c hab hbc x ↦ hcomp _ a b c hab hbc x }
  exact ⟨d, t.compatibility⟩
end AlgebraicGeometry.Scheme
