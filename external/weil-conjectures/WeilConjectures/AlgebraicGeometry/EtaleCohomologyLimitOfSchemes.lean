/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyEventualVanishing
import WeilConjectures.AlgebraicGeometry.CompatiblePullbackSheafSystem
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected

/-! # Etale cohomology of limits of schemes

Source: Stacks Project, Etale Cohomology, Theorem 59.51.3 (Tag 09YQ), and
Limits, Lemma 32.2.1 (Tag 01YW)
(blueprint: lem-weil-pbc-etale-cohomology-limit-of-schemes).

The object isomorphisms present diagrams on the varying sites as ordinary functors.
The equations on their arrows and on the cocone legs specify the canonical comparison.
Its being a colimit cocone says that the induced comparison from the colimit is an
isomorphism. We use `Sheaf.H` and `cohomologyMap`, the recorded abelian-sheaf cohomology
and pullback encoding; its comparison with K-injective cohomology is a comparison theorem.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale


/-- Cohomology continuity for a system of abelian sheaves on a directed inverse system
of qcqs schemes with affine transition maps. Source: Stacks Project, Tag 09YQ
(blueprint: lem-weil-pbc-etale-cohomology-limit-of-schemes).

Proof:
1. Inverse-image composition (lem-weil-pbc-inverse-image-composition) and its coherence
   turn the pulled-back sheaves into the diagram `G`. Cohomology pullback functoriality
   (proposition-cohomology-p-1-over-henselian--1) gives the diagram `H` and cocone `B`.
2. Restrict to any cofinal tail of the directed set using
   lem-weil-pbc-colimit-initial-full-subcategory and lem-weil-pbc-limit-affine-transition.
3. For affine stages use lem-weil-pbc-affine-etale-site-topos and
   lem-weil-pbc-affine-etale-site-colimit to pass to the colimit of affine etale sites.
   Direct images agree on affine objects, so uniqueness of left adjoints identifies
   inverse images, compatibly with units and composition.
4. Apply lem-weil-pbc-cohomology-colimit-of-sites at the final affine object and transport
   the cohomology comparison back across the equivalence. Cofinality gives the full diagram.
5. Restrict to quasi-compact opens at a stage. Limits commute with these restrictions,
   and inverse image preserves colimits; hence the restricted data have the same form.
6. Mayer-Vietoris and its pullback compatibility (lem-weil-pbc-etale-mayer-vietoris and
   lem-weil-pbc-etale-mayer-vietoris-pullback), exact filtered colimits of abelian groups
   (lem-weil-pbc-filtered-colimit-abelian-groups-exact), and lem-weil-pbc-five-lemma
   show that the result glues across two such opens.
7. Induct on a finite affine cover in the separated case; intersections of affine opens
   are affine by lem-weil-pbc-separated-affine-open-intersection.
8. Induct on a finite affine cover in general. The intersection with one affine is a
   quasi-compact separated open, handled by step 7. Step 6 finishes the induction.
   The comparison throughout has exactly the legs prescribed by `hB`.
-/
theorem nonempty_isColimit_etale_cohomology_of_isLimit
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
    Nonempty (IsColimit B) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hlift := etale_limit_cohomology_class_descent
    D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB
  have hzero := etale_limit_cohomology_eventual_vanishing
    D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB
  have hiso : IsIso (colimit.desc H B) := by
    apply (ConcreteCategory.isIso_iff_bijective (colimit.desc H B)).2
    constructor
    · apply (injective_iff_map_eq_zero (colimit.desc H B).hom).2
      intro z hz
      obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep H z
      have hx : (B.ι.app i).hom x = 0 := by
        change (colimit.ι H i ≫ colimit.desc H B).hom x = 0 at hz
        rwa [colimit.ι_desc] at hz
      obtain ⟨j, f, hf⟩ := hzero i x hx
      calc
        (colimit.ι H i).hom x = (colimit.ι H j).hom ((H.map f).hom x) :=
          (colimit.w_apply H f x).symm
        _ = 0 := by rw [hf, map_zero]
    · intro y
      obtain ⟨i, x, hx⟩ := hlift y
      refine ⟨(colimit.ι H i).hom x, ?_⟩
      change (colimit.ι H i ≫ colimit.desc H B).hom x = y
      rw [colimit.ι_desc]
      exact hx
  have : IsIso ((colimit.isColimit H).desc B) := hiso
  exact ⟨(colimit.isColimit H).ofPointIso⟩


private theorem continuity_constant_pullback
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (d : Cone D) (hd : IsLimit d)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, D.obj (op i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = D.map f.op ≫ v i)
    (vLimit : d.pt ⟶ T) (wLimit : ∀ i : I, vLimit = d.π.app (op i) ≫ v i)
    (p : ℕ) (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (D.map f.op)
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (D.map f.op) (v i)
            (v j) (wv i j f)).inv.app G) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} vLimit).obj G) p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (d.π.app (op i))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op i)) (v i)
            vLimit (wLimit i)).inv.app G) p)) :
    Nonempty (IsColimit B) := by
  set_option backward.isDefEq.respectTransparency true in
    let : IsConnected I := IsFiltered.isConnected I
    let F := fun i : I ↦ (upperStar AddCommGrpCat.{u + 1} (v i)).obj G
    let φ := fun {i j : I} (f : i ⟶ j) ↦
      (upperStarComp AddCommGrpCat.{u + 1} (D.map f.op) (v i)
        (v j) (wv i j f)).inv.app G
    let K := (upperStar AddCommGrpCat.{u + 1} vLimit).obj G
    let S : I ⥤ Sheaf d.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      (Functor.const I).obj K
    let eS := fun i : I ↦
      (upperStarComp AddCommGrpCat.{u + 1} (d.π.app (op i)) (v i)
        vLimit (wLimit i)).app G
    obtain ⟨hidentity, hcomposition, hS⟩ :=
      compatiblePullbackSheafSystem D d T G v wv vLimit wLimit
    apply nonempty_isColimit_etale_cohomology_of_isLimit D d hd F φ
      hidentity hcomposition S eS hS (constCocone I K) (isColimitConstCocone I K)
      p H eH hH B eB ?_
    intro i
    change B.ι.app i ≫ eB.hom = (eH i).hom ≫
      AddCommGrpCat.ofHom (cohomologyMap (d.π.app (op i)) (F i) p) ≫
      AddCommGrpCat.ofHom (Sheaf.H.map ((eS i).inv ≫ 𝟙 K) p)
    rw [Category.comp_id]
    exact hB i


/-- The affine ring case: for a directed system of rings with colimit `C`, the compatible
pullbacks of one abelian sheaf to `Spec C_i` satisfy continuity at `Spec C`.
Source: Stacks Project, Tags 01YW and 09YQ
(blueprint: lem-weil-pbc-etale-cohomology-limit-of-schemes).

Proof (step 9 of the node): lem-weil-pbc-spec-colimit-limit gives the limit and affine
transitions. Set F_i = v_i inverse image of G; inverse-image composition gives their
transition isomorphisms and the cocycle law. On the limit all these sheaves identify with
v inverse image of G, with identity transition maps. The directed index is connected,
so definition-torsion-sheaves--3 identifies their colimit with that
sheaf. Apply the preceding eight-step argument. Its canonical maps become the pullbacks
followed by the composition isomorphisms appearing in `hH` and `hB` below. -/
theorem nonempty_isColimit_etale_cohomology_spec_ring_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, Spec (R.obj i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = Spec.map (R.map f) ≫ v i)
    (vLimit : Spec c.pt ⟶ T) (wLimit : ∀ i : I, vLimit = Spec.map (c.ι.app i) ≫ v i)
    (p : ℕ) (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (R.map f))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (R.map f)) (v i)
            (v j) (wv i j f)).inv.app G) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} vLimit).obj G) p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (c.ι.app i))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (c.ι.app i)) (v i)
            vLimit (wLimit i)).inv.app G) p)) :
    Nonempty (IsColimit B) := by
  let D : Iᵒᵖ ⥤ Scheme.{u} := R.op ⋙ Scheme.Spec
  let d : Cone D := Scheme.Spec.mapCone c.op
  have hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  let (i : Iᵒᵖ) : CompactSpace (D.obj i) := by
    dsimp [D]
    infer_instance
  let (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    dsimp [D]
    infer_instance
  let (i j : Iᵒᵖ) (f : i ⟶ j) : IsAffineHom (D.map f) := by
    dsimp [D]
    infer_instance
  exact continuity_constant_pullback D d hd T G v wv vLimit wLimit p H eH hH B eB hB

end AlgebraicGeometry.Etale
