/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineEventualZero
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Affine-stage cohomology continuity

Source: Stacks Project, Tags 09YQ, 0EYL, 09YP and 04HR.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Affine-stage continuity for the specified cohomology comparison.

Source: Stacks Project, Tags 09YQ (theorem-colimit), 0EYL
(lemma-colimit-affine-sites), 09YP (lemma-colimit), and 04HR.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-comparison).

Proof:
1. Affine transition limits are affine. Present their affine etale sites as a
   filtered colimit using exists_affineEtaleSite_colimit, including its strictification.
2. Restriction along fullAffineEtaleInclusion is a sheaf equivalence. On an affine
   etale object A, both direct images evaluate a sheaf at the base change of A.
   This identifies the right adjoints under restriction. The induced isomorphism of
   left adjoints is the unique one compatible with the adjunction units. The two
   isomorphisms for a composite have the same unit, so uniqueness gives the
   composition compatibility. Transport phi by these isomorphisms; its two coherence
   equations therefore remain valid. Transport G and L using the same equivalences;
   an equivalence preserves the colimit and its legs.
3. Fix any index i and pass to the cofinal tail above i. The affine scheme D_i,
   with its identity map, is a final object of its affine etale site. Its base changes
   are the final objects D_j and X. Apply cohomology_colimit_of_sites to this object
   of the strictified site. Object cohomology at the final object is global
   cohomology. The sheaf equivalences identify these cohomology groups with the
   original groups, naturally in the coefficients.
4. The pullback comparisons agree: each is induced by the adjunction unit on
   injective resolutions, and step 2 identifies the units. Naturality in the
   coefficient sheaf identifies the transition maps with hH and the legs with hB.
   Thus the transported colimit cocone is exactly B, including eH and eB.
5. The tail inclusion is final, so its colimit is the colimit on I. Transport the
   colimit structure back to B. This yields Nonempty (IsColimit B).

Edge cases: nonemptiness gives the index chosen in the proof. Empty affine schemes
have zero cohomology. Degree zero uses sections. A one-object system identifies its
scheme limit and sheaf colimit with the single stage and its sheaf.
-/
theorem etale_limit_cohomology_affine_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
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
    Nonempty (IsColimit B) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hlift := etale_limit_cohomology_class_descent D c hc F φ hidentity hcomposition
    G eG hG L hL p H eH hH B eB hB
  have hzero := etale_limit_affine_eventual_zero D c hc F φ hidentity hcomposition
    G eG hG L hL p
  have hleg (i : I) (x : H.obj i) :
      eB.hom (B.ι.app i x) =
        Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p
          (cohomologyMap (c.π.app (op i)) (F i) p ((eH i).hom x)) := by
    exact congrArg (fun f ↦ f x) (hB i)
  have htrans (i j : I) (f : i ⟶ j) (x : H.obj i) :
      (eH j).hom (H.map f x) =
        Sheaf.H.map (φ f) p (cohomologyMap (D.map f.op) (F i) p ((eH i).hom x)) := by
    rw [hH]
    simp
  have hbij : Function.Bijective (colimit.desc H B) := by
    constructor
    · apply (injective_iff_map_eq_zero (colimit.desc H B).hom).2
      intro z hz
      obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep H z
      have hx : B.ι.app i x = 0 := by
        change (colimit.ι H i ≫ colimit.desc H B) x = 0 at hz
        rwa [colimit.ι_desc] at hz
      have hx' : Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p
          (cohomologyMap (c.π.app (op i)) (F i) p ((eH i).hom x)) = 0 := by
        rw [← hleg, hx]
        exact map_zero eB.hom.hom
      obtain ⟨j, f, hf⟩ := hzero i ((eH i).hom x) hx'
      have hfx : H.map f x = 0 := by
        have heq : (eH j).hom (H.map f x) = 0 := (htrans i j f x).trans hf
        have := congrArg (fun y ↦ (eH j).inv y) heq
        simpa using this
      calc
        colimit.ι H i x = colimit.ι H j (H.map f x) :=
          (colimit.w_apply H f x).symm
        _ = 0 := by rw [hfx]; exact map_zero (colimit.ι H j).hom
    · intro y
      obtain ⟨i, x, hx⟩ := hlift y
      refine ⟨colimit.ι H i x, ?_⟩
      change (colimit.ι H i ≫ colimit.desc H B) x = y
      rw [colimit.ι_desc]
      exact hx
  have : IsIso (colimit.desc H B) :=
    (ConcreteCategory.isIso_iff_bijective (colimit.desc H B)).2 hbij
  exact ⟨(colimit.isColimit H).ofIsoColimit
    (Cocone.ext (asIso (colimit.desc H B)) (by intro i; simp))⟩

end AlgebraicGeometry.Etale
