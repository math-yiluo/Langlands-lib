/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyAffineStage
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyBinaryGluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Cohomology continuity glues from affine stages to qcqs stages

Source: Stacks Project, Tags 09YQ and 0A50; parent proof steps 5-8.
(blueprint: lem-weil-pbc-etale-limit-cohomology-qcqs-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

private theorem stageContinuity_of_iso {S T : Scheme.{u}} (e : S ≅ T)
    (h : EtaleCohomologyStageContinuity T) : EtaleCohomologyStageContinuity S := by
  constructor
  intro I _ _ _ D c hc _ _ _ F φ hid hcomp G eG hG L hL p H eH hH B eB hB i hi
  exact h.holds D c hc F φ hid hcomp G eG hG L hL p H eH hH B eB hB i
    (hi.map (fun ei ↦ ei ≪≫ e))

set_option linter.unusedVariables false in
/-- The qcqs gluing reduction for cohomology continuity.

The hypothesis is affine-stage continuity for every system and every degree in
this universe. It is applied to restrictions of the supplied system, and never
assumes continuity for the nonaffine system being proved.

Source: Stacks Project, Tag 09YQ (theorem-colimit); the finite-cover reduction is
steps 5-8 of lem-weil-pbc-etale-limit-cohomology-eventual-vanishing, using
Tags 0A50 (lemma-mayer-vietoris), 01YX and 01KP.
(blueprint: lem-weil-pbc-etale-limit-cohomology-qcqs-gluing).

Proof:
1. Work above an arbitrary stage i0. Its cofinal tail has the same scheme limit,
   sheaf colimit, and group colimit. For a quasi-compact open W of D_i0, form its
   inverse images on the tail and on X. Affine morphisms preserve quasi-compactness
   under inverse image; the opens are quasi-separated and the restricted maps
   affine. The limit of the restricted schemes is the indicated open of X.
   Restrict the sheaves by inverse image along the open immersions. The composition
   isomorphisms give the restricted transition maps and their coherence. Since
   inverse image preserves colimits, the restriction of L is their colimit. The
   pullback composition and naturality formulas give the prescribed restricted
   cohomology legs. Thus the affine-continuity hypothesis applies when W is affine.
2. Suppose a stage is the union of two quasi-compact opens U and V and continuity
   holds in all degrees on U, V and their intersection. Pull back this cover to
   every later stage and to X. Mayer-Vietoris, naturality in the coefficient sheaf,
   and pullback compatibility give a morphism from the filtered colimit of the
   stage long exact sequences to the limit long exact sequence. The stage colimit
   sequence is exact because filtered group colimits are exact. In positive degree
   use the five-term segment
   H^(p-1)(U)+H^(p-1)(V) -> H^(p-1)(U intersection V) -> H^p(X)
     -> H^p(U)+H^p(V) -> H^p(U intersection V).
   Its four outer comparisons are isomorphisms, so the five lemma makes the middle
   comparison an isomorphism. For degree zero use the initial zero terms. Hence
   continuity holds on the union, with exactly the legs hB.
3. Induct on the size of a finite affine cover of a separated chosen stage, for all
   systems and all degrees simultaneously. A cover of size zero means the stage,
   every later stage, and the limit are empty, so all groups are zero. Size one is
   the affine hypothesis, since every later scheme is affine over that affine stage.
   For a larger cover take one affine U and the union V of the remaining affines.
   V is separated with a shorter cover. Its intersection with U is covered by the
   intersections with the remaining affines, each affine by separatedness. Apply
   the induction hypothesis to these two shorter covers, the affine hypothesis to
   U, and step 2 to their union.
4. Induct on a finite affine cover of an arbitrary qcqs chosen stage. The zero and
   one cases are as above. For a larger cover write U union V as in step 3. V is
   qcqs and has a shorter cover, so the induction hypothesis applies. U is affine.
   U intersection V is quasi-compact by quasi-separatedness and separated as an
   open of U; it has a finite affine cover, so step 3 applies. Step 2 proves
   continuity on the union. Compactness provides the initial finite affine cover.
5. The resulting canonical comparison is an isomorphism. Transport the colimit
   cocone along it and eB to obtain a colimit structure on B. Cofinality returns
   from the tail to I. All the identifications use the legs in hB, so this is the
   supplied cocone rather than merely an abstract isomorphic group.

Edge cases: degree zero uses a left-exact row starting at zero, not a negative
cohomology group. Empty schemes and zero sheaves give zero groups. No separatedness
is assumed in step 4; it is only used for opens of the affine U in that step.
-/
theorem etale_limit_cohomology_qcqs_gluing
    (haffine : ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (D : Jᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Jᵒᵖ, CompactSpace (D.obj i)] [∀ i : Jᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Jᵒᵖ, IsAffine (D.obj i)]
    (F : ∀ i : J, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : J} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : J, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : J) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : J ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : J, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : J) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : J ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : J, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : J) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : J, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p)),
      Nonempty (IsColimit B))
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
  have ha : ∀ (X : Scheme.{u}) (U : X.Opens), IsAffineOpen U →
      EtaleCohomologyStageContinuity U.toScheme := by
    intro X U hU
    let : IsAffine U.toScheme := hU
    exact @etale_limit_cohomology_affine_stage @haffine U.toScheme hU
  have hsep : ∀ (X : Scheme.{u}) [X.IsSeparated] (U : X.Opens),
      IsCompact (U : Set X) → EtaleCohomologyStageContinuity U.toScheme := by
    intro X _ U hU
    have hpair : ∀ (V : X.Opens), IsCompact (V : Set X) →
        EtaleCohomologyStageContinuity V.toScheme ∧
        ∀ W : X.affineOpens, EtaleCohomologyStageContinuity (V ⊓ W.1).toScheme := by
      intro V hV
      refine compact_open_induction_on V hV ?_ ?_
      · constructor
        · exact ha X ⊥ (isAffineOpen_bot X)
        · intro W
          simpa using ha X ⊥ (isAffineOpen_bot X)
      · intro V hV W ih
        have hW := ha X W.1 W.2
        constructor
        · exact etale_limit_cohomology_binary_gluing X V W.1 hV W.2.isCompact
            ih.1 hW (ih.2 W)
        · intro Z
          have hVZ : IsCompact ((V ⊓ Z.1) : Set X) :=
            hV.inter_of_isOpen Z.2.isCompact V.2 Z.1.2
          have hWZ := W.2.inf Z.2
          have hI : EtaleCohomologyStageContinuity ((V ⊓ Z.1) ⊓ (W.1 ⊓ Z.1)).toScheme := by
            have h := ih.2 ⟨W.1 ⊓ Z.1, hWZ⟩
            simpa [inf_assoc, inf_left_comm, inf_comm] using h
          simpa [inf_sup_right] using
            etale_limit_cohomology_binary_gluing X (V ⊓ Z.1) (W.1 ⊓ Z.1)
              hVZ hWZ.isCompact (ih.2 Z) (ha X _ hWZ) hI
    exact @And.left _ _ (hpair U hU)
  have hqcqs : ∀ (X : Scheme.{u}) [QuasiSeparatedSpace X] (U : X.Opens),
      IsCompact (U : Set X) → EtaleCohomologyStageContinuity U.toScheme := by
    intro X _ U hU
    refine compact_open_induction_on U hU ?_ ?_
    · exact ha X ⊥ (isAffineOpen_bot X)
    · intro V hV W ih
      let : IsAffine W.1.toScheme := W.2
      have hI : IsCompact ((V ⊓ W.1) : Set X) :=
        hV.inter_of_isOpen W.2.isCompact V.2 W.1.2
      let f : (V ⊓ W.1).toScheme ⟶ W.1.toScheme := X.homOfLE inf_le_right
      let : (V ⊓ W.1).toScheme.IsSeparated := by
        constructor
        rw [← terminal.comp_from f]
        infer_instance
      let : CompactSpace (V ⊓ W.1).toScheme := isCompact_iff_compactSpace.mp hI
      have hcont := hsep (V ⊓ W.1).toScheme ⊤ (by simpa using isCompact_univ)
      have hcont' : EtaleCohomologyStageContinuity (V ⊓ W.1).toScheme :=
        stageContinuity_of_iso (V ⊓ W.1).toScheme.topIso.symm hcont
      exact etale_limit_cohomology_binary_gluing X V W.1 hV W.2.isCompact
        ih (ha X W.1 W.2) hcont'
  let i : I := Classical.choice inferInstance
  have ht := hqcqs (D.obj (op i)) ⊤ (by simpa using isCompact_univ)
  have hstage : EtaleCohomologyStageContinuity (D.obj (op i)) :=
    stageContinuity_of_iso (D.obj (op i)).topIso.symm ht
  exact hstage.holds D c hc F φ hidentity hcomposition G eG hG L hL p H eH hH B eB hB i
    ⟨Iso.refl _⟩

end AlgebraicGeometry.Etale
