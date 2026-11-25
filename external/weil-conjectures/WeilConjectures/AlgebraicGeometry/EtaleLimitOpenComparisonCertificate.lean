/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
public import WeilConjectures.AlgebraicGeometry.StageCohomologyComparison
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Geometric certificate for the canonical open comparison

Source: Stacks Project, Tag 09YQ, restriction of coherent systems.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem tailOpenCohomologyMap_eq
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {X : Scheme.{u}} {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    {j k : Set.Ici i₀} (f : j ⟶ k) :
    tailOpenCohomologyMap D g₀ W F φ f =
      AddCommGrpCat.ofHom (cohomologyMap ((tailOpenDiagram D g₀ W).map f.op)
        (tailOpenSheaf D g₀ W F j) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (tailOpenCoefficient D g₀ W F φ f) 0) := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 150000 in
-- Dependent scheme-indexed sheaf categories require the full restricted-system check.
/-- The canonical cocone on inverse-image opens has a stage-comparison certificate.

Source: Stacks Project, Tag 09YQ, coherent-system construction; the open-limit
construction in Mathlib.AlgebraicGeometry.AffineTransitionLimit.
(blueprint: lem-weil-pbc-etale-limit-open-comparison-certificate).

Proof: Restrict the inverse diagram to the directed tail above i₀ and to the
inverse images of W. The opens cone is limiting by `isLimitOpensCone`, after
identifying the tail opposite with Over(op i₀). Its transitions are affine
restrictions of the given affine maps. At the least tail index its object is
isomorphic to W.toScheme: the identity transition, the given e, and W ≤ O
identify its open with W. Compactness of W makes this least stage compact;
affine preimages of quasi-compact opens are quasi-compact. Every other stage
is an open in a quasi-separated scheme, hence quasi-separated. Pull the given
coefficient system back to these stages with `openSquareCoefficient`. The
canonical inverse-image coherences give the identity, composition and G-map
equations. The tail inclusion is final (directedness gives an upper bound for
any index and i₀), so L reindexed to the tail is still a colimit. Inverse image
along the limit open is a left adjoint and preserves this colimit. Composition
identifications make it the colimit of the pulled-back restricted coefficients.
The specified hK and hι are precisely the arrow and cocone formulas for this
system, after transporting the object identifications eK. Apply the `system`
constructor of StageCohomologyComparison at the least index, and transport
through the canonical open-limit/coefficient isomorphisms with its `iso` and
`comp` constructors. This certifies the supplied colimit.desc, without asserting
that it is an isomorphism. Empty W, zero coefficients, and singleton diagrams
satisfy the same construction; no injectivity or continuity is assumed. -/
theorem etale_limit_open_comparison_certificate
    (X : Scheme.{u}) (O W : X.Opens) (hW : IsCompact (W : Set X)) (hWO : W ≤ O)
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
    (L : Cocone G) (hL : IsColimit L)
    (i₀ : I) (e : D.obj (op i₀) ≅ O.toScheme)
    (allowed : Scheme.{u} → Prop) (hallowed : allowed W.toScheme)
    (K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eK : ∀ j : Set.Ici i₀, K.obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D (e.hom ≫ O.ι) W j).ι).obj (F j.val)) 0))
    (hK : ∀ (j k : Set.Ici i₀) (f : j ⟶ k), K.map f =
      (eK j).hom ≫ tailOpenCohomologyMap D (e.hom ≫ O.ι) W F φ f ≫ (eK k).inv)
    (ι : K ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ (e.hom ≫ O.ι)) ⁻¹ᵁ W).ι).obj L.pt) 0)))
    (hι : ∀ j, ι.app j =
      (eK j).hom ≫ tailOpenCohomologyLeg D c (e.hom ≫ O.ι) W F G eG L j) :
    StageCohomologyComparison allowed (colimit.desc K (Cocone.mk _ ι)) := by
  classical
  let J := Set.Ici i₀
  let o : J := ⟨i₀, le_rfl⟩
  let : Nonempty J := ⟨o⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let g₀ := e.hom ≫ O.ι
  let U := g₀ ⁻¹ᵁ W
  let E := tailOpenDiagram D g₀ W
  let cE := tailOpenCone D c g₀ W
  let Q := tailOpenIndexFunctor i₀
  let : Q.Initial := Functor.initial_of_exists_of_isCofiltered Q
    (fun i ↦ ⟨op ⟨i.left.unop, leOfHom i.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, by
      apply Over.OverMorphism.ext
      apply Subsingleton.elim⟩)
  have hE : IsLimit cE := (Functor.Initial.isLimitWhiskerEquiv Q _).symm
    (isLimitOpensCone D c hc (op i₀) U)
  let q : U.toScheme ≅ W.toScheme :=
    e.hom.preimageIso (O.ι ⁻¹ᵁ W) ≪≫ Scheme.Opens.isoOfLE hWO
  have hU : IsCompact (U : Set (D.obj (op i₀))) := by
    let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    have hCU : CompactSpace U.toScheme :=
      (TopCat.homeoOfIso (asIso q.hom.base)).symm.compactSpace
    exact isCompact_iff_compactSpace.mpr hCU
  let hcompact (j : Jᵒᵖ) : CompactSpace (E.obj j) := isCompact_iff_compactSpace.mp
    ((D.map (homOfLE j.unop.property).op).isCompact_preimage hU)
  let hqs (j : Jᵒᵖ) : QuasiSeparatedSpace (E.obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _
      (D.map (homOfLE j.unop.property).op ⁻¹ᵁ U).2).mp (.of_quasiSeparatedSpace _)
  let haffine (j k : Jᵒᵖ) (f : j ⟶ k) : IsAffineHom (E.map f) :=
    inferInstanceAs (IsAffineHom ((opensDiagram D (op i₀) U).map (Q.map f)))
  have h₀ : D.map (homOfLE (show i₀ ≤ i₀ from le_rfl)).op ⁻¹ᵁ U = U := by
    have ht : (homOfLE (show i₀ ≤ i₀ from le_rfl)).op = 𝟙 (op i₀) :=
      Subsingleton.elim _ _
    rw [ht, D.map_id]
    rfl
  let e₀ : E.obj (op o) ≅ W.toScheme := (D.obj (op i₀)).isoOfEq h₀ ≪≫ q
  let T := tailOpenInclusion i₀
  let : T.Final := by
    apply Functor.final_of_exists_of_isFiltered T
    · intro i
      obtain ⟨k, hik, h₀k⟩ := exists_ge_ge i i₀
      exact ⟨⟨k, h₀k⟩, ⟨homOfLE hik⟩⟩
    · intro i j f g
      exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩
  let R := upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
  let G' := (T ⋙ G) ⋙ R
  let L' : Cocone G' := R.mapCocone (L.whisker T)
  have hL' : IsColimit L' := isColimitOfPreserves R
    ((Functor.Final.isColimitWhiskerEquiv T L).symm hL)
  have hcoh :=
    tailOpenRestrictedSystem_coherence D c F φ hidentity hcomposition G eG hG i₀ (e.hom ≫ O.ι) W
  obtain ⟨hidentity', hcomposition', hG', hleg⟩ := hcoh
  let B : Cocone K := Cocone.mk (AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
    ((c.π.app (op i₀) ≫ (e.hom ≫ O.ι)) ⁻¹ᵁ W).ι).obj L.pt) 0)) ι
  let eB := Iso.refl B.pt
  have hH : ∀ (j k : (Set.Ici i₀)) (f : j ⟶ k), K.map f =
      (eK j).hom ≫ AddCommGrpCat.ofHom (cohomologyMap ((tailOpenDiagram D (e.hom ≫ O.ι) W).map
        f.op) ((tailOpenSheaf D (e.hom ≫ O.ι) W F) j) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((@tailOpenCoefficient _ _ D _ _ (e.hom ≫ O.ι) W F φ)
          f) 0) ≫ (eK k).inv := by
    intro j k f
    rw [hK j k f, tailOpenCohomologyMap_eq]
    simp only [Category.assoc]
  have hB : ∀ j : (Set.Ici i₀), B.ι.app j ≫ eB.hom =
      (eK j).hom ≫ AddCommGrpCat.ofHom (cohomologyMap ((tailOpenCone D c (e.hom ≫ O.ι) W).π.app
        (op j)) ((tailOpenSheaf D (e.hom ≫ O.ι) W F) j) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (((tailOpenLimitIso D c (e.hom ≫ O.ι) W F G eG) j).inv
          ≫ ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ (e.hom ≫ O.ι)) ⁻¹ᵁ
            W).ι).mapCocone (L.whisker (tailOpenInclusion i₀))).ι.app j) 0) := by
    intro j
    change ι.app j ≫ 𝟙 _ = _
    rw [Category.comp_id, hι j, hleg L j]
    simp only [Functor.mapCocone_ι_app, Cocone.whisker,
      Functor.whiskerLeft_app, tailOpenInclusion]
  let := hcompact
  let := hqs
  let := haffine
  exact StageCohomologyComparison.system (I := Set.Ici i₀) (tailOpenDiagram D (e.hom ≫ O.ι) W)
      (tailOpenCone D c (e.hom ≫ O.ι) W) hE (tailOpenSheaf D (e.hom ≫ O.ι) W F)
        (@tailOpenCoefficient _ _ D _ _ (e.hom ≫ O.ι) W F φ)
    hidentity' hcomposition' ((tailOpenInclusion i₀ ⋙ G) ⋙ (upperStar AddCommGrpCat.{u + 1}
      ((c.π.app (op i₀) ≫ (e.hom ≫ O.ι)) ⁻¹ᵁ W).ι)) (tailOpenLimitIso D c (e.hom ≫ O.ι) W F G
        eG) hG' ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ (e.hom ≫ O.ι)) ⁻¹ᵁ
          W).ι).mapCocone (L.whisker (tailOpenInclusion i₀))) hL' 0 K eK hH B eB hB
    W.toScheme hallowed o e₀

end AlgebraicGeometry.Etale
