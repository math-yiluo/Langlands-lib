/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.StageCohomologyComparison
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenComparisonCertificate

/-! # Comparison for one open in a cofinal tail

Source: Stacks Project, Tag 09YQ, restriction of the coherent-system construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to one quasi-compact open constructs its canonical comparison on the tail.

Source: Stacks Project, Tag 09YQ, coherent systems on inverse limits, and Tag 01F7,
functoriality of cohomology.
(blueprint: lem-weil-pbc-etale-limit-single-open-comparison).

Proof: Use the directed tail above i₀. Pull W back along the stage projection to
D(i₀), e, and O.ι. Restrict D and its cone to these opens. The open limit theorem
identifies the cone point with the indicated open of c.pt. Affine transition maps
and affine limit projections imply compactness of the restricted stages; open
subspaces of quasi-separated schemes are quasi-separated. At the least tail index,
the restricted stage is canonically isomorphic to W.toScheme, since W ≤ O.
Pull F and its transition maps back to these opens. Inverse-image composition and
its coherence give the identity and composition laws; the same comparisons identify
the pulled-back colimit diagram with the restriction of G. Restriction preserves
colimits because it is a left adjoint, and the tail inclusion is final. Apply the
canonical cohomology-diagram construction in degree zero, transporting the limit
cohomology group through the canonical open and coefficient identifications.
The system constructor gives the comparison certificate with stage W.toScheme;
composition with these identifications uses the iso and comp constructors.
Pullback functoriality and coefficient naturality give the transformation from H
whose components are exactly the specified restrictions. The canonical cocone
formula, hB, and composition naturality give the stage-leg equation.
No injectivity or binary-product comparison is asserted. For W empty the restricted
schemes and groups are empty and zero; for W = O this is just tail reindexing. -/
theorem etale_limit_single_open_comparison
    (X : Scheme.{u}) (O W : X.Opens)
    (hW : IsCompact (W : Set X)) (hWO : W ≤ O)
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
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) 0))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) 0) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt 0))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0))
    (i₀ : I) (e : D.obj (op i₀) ≅ O.toScheme)
    (allowed : Scheme.{u} → Prop) (hallowed : allowed W.toScheme) :
    let t : Set.Ici i₀ ⥤ I := (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from
      fun _ _ h ↦ h).functor
    let WL := (c.π.app (op i₀) ≫ e.hom ≫ O.ι) ⁻¹ᵁ W
    let BW := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WL.ι).obj L.pt) 0)
    let rW : B.pt ⟶ BW := eB.hom ≫ AddCommGrpCat.ofHom (cohomologyMap WL.ι L.pt 0)
    ∃ (K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
      (eK : ∀ j : Set.Ici i₀, K.obj j ≅ AddCommGrpCat.of
        (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((D.map (homOfLE j.property).op ≫ e.hom ≫ O.ι) ⁻¹ᵁ W).ι).obj (F j.val)) 0))
      (r : t ⋙ H ⟶ K) (v : colimit K ⟶ BW),
      (∀ j, r.app j ≫ (eK j).hom = (eH j.val).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap ((D.map (homOfLE j.property).op ≫ e.hom ≫ O.ι) ⁻¹ᵁ W).ι
          (F j.val) 0)) ∧
      StageCohomologyComparison allowed v ∧
      (∀ j, r.app j ≫ colimit.ι K j ≫ v = B.ι.app j.val ≫ rW) := by
  let g₀ := e.hom ≫ O.ι
  obtain ⟨K, eK, hK, ι, hι⟩ := etale_limit_open_cohomology_cocone
    D c F φ hidentity hcomposition G eG hG L i₀ g₀ W
  let t : Set.Ici i₀ ⥤ I := (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from
    fun _ _ h ↦ h).functor
  let r : t ⋙ H ⟶ K :=
    { app := fun j ↦ (eH j.val).hom ≫
        AddCommGrpCat.ofHom (cohomologyMap (tailStageOpen D g₀ W j).ι (F j.val) 0) ≫
        (eK j).inv
      naturality := by
        intro j k f
        have hs := openSquareCoefficient_cohomology
          (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
          (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
          (tailStageOpenMap D g₀ W f)
          (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
          (F j.val) (F k.val) (φ (homOfLE (show j.val ≤ k.val from f.le))) 0
        change H.map (homOfLE (show j.val ≤ k.val from f.le)) ≫ _ = _
        rw [hH, hK]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        simpa only [tailOpenCohomologyMap, Category.assoc] using
          congrArg (fun m ↦ (eH j.val).hom ≫ m ≫ (eK k).inv) hs.symm }
  refine ⟨K, eK, r, colimit.desc K (Cocone.mk _ ι), ?_, ?_, ?_⟩
  · intro j
    simp only [r, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  · exact etale_limit_open_comparison_certificate X O W hW hWO D c hc F φ
      hidentity hcomposition G eG hG L hL i₀ e allowed hallowed K eK hK ι hι
  · intro j
    have hs := openSquareCoefficient_cohomology (c.π.app (op j.val))
      (tailStageOpen D g₀ W j).ι ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
      (tailLimitOpenMap D c g₀ W j)
      (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι])
      (F j.val) L.pt ((eG j.val).inv ≫ L.ι.app j.val) 0
    dsimp only [r, NatTrans.app]
    rw [Category.assoc, colimit.ι_desc, hι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have ht := congrArg (fun m ↦ (eH j.val).hom ≫ m) hs
    have hb := congrArg (fun m ↦ m ≫ AddCommGrpCat.ofHom
      (cohomologyMap ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι L.pt 0)) (hB j.val)
    calc
      _ = (eH j.val).hom ≫
          AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op j.val)) (F j.val) 0) ≫
          AddCommGrpCat.ofHom (Sheaf.H.map ((eG j.val).inv ≫ L.ι.app j.val) 0) ≫
          AddCommGrpCat.ofHom
            (cohomologyMap ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι L.pt 0) := by
        simpa only [tailOpenCohomologyLeg, Category.assoc] using ht
      _ = _ := by simpa only [Category.assoc] using hb.symm


end AlgebraicGeometry.Etale
