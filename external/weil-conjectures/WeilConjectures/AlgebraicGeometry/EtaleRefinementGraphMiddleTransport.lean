/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Intersection transport along a proper refinement graph

Source: Stacks Project, Tags 0F7C--0F7D, and step 2 of
`lem-pur-etale-graph-refinement-normalization`.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem triangle_transport
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasBaseChange]
    {X W O Z T : Scheme.{u}} (t : X ⟶ W) (a : W ⟶ O) (b : O ⟶ T)
    (s : X ⟶ O) (j : X ⟶ Z) (z : Z ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j]
    (ht : IsPullback t (𝟙 X) a s) (hs : IsPullback s j b z) (M : F.obj X) :
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) ht
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) hs
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
      (by simpa only [Category.id_comp] using ht.paste_vert hs :
        IsPullback t j (a ≫ b) z)
    (F.sh b).map ((F.exchange t (𝟙 X) a s ht.w).app M ≫
        (F.pf s).map ((F.shId X).hom.app M)) ≫
        (F.exchange s j b z hs.w).app M =
      (F.shComp' a b (a ≫ b) rfl).inv.app ((F.pf t).obj M) ≫
        (F.exchange t j (a ≫ b) z
          ((ht.paste_vert hs).w.trans
            (congrArg (fun q ↦ q ≫ z) (Category.id_comp j)))).app M := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) ht
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) hs
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    (by simpa only [Category.id_comp] using ht.paste_vert hs :
        IsPullback t j (a ≫ b) z)
  have h := congr_app (F.exchange_paste_vert t s z (𝟙 X) a j b j (a ≫ b)
    ht.w hs.w (Category.id_comp j) rfl ((ht.paste_vert hs).w.trans
      (congrArg (fun q ↦ q ≫ z) (Category.id_comp j)))) M
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id] at h
  have hi := congr_app (F.shComp'_id_left j) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, NatTrans.id_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id] at hi
  have hinv : (F.shComp' (𝟙 X) j j (Category.id_comp j)).inv.app M =
      (F.sh j).map ((F.shId X).hom.app M) := by
    apply (cancel_epi ((F.shComp' (𝟙 X) j j (Category.id_comp j)).hom.app M)).1
    rw [Iso.hom_inv_id_app, hi]
  rw [hinv] at h
  have hn := (F.exchange s j b z hs.w).naturality ((F.shId X).hom.app M)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc] at h
  rw [← hn] at h
  have hc := congrArg
    (fun q ↦ (F.shComp' a b (a ≫ b) rfl).inv.app ((F.pf t).obj M) ≫ q) h
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp,
    Functor.comp_obj, Functor.id_obj] using hc.symm

private theorem concrete_triangle_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X W O Z T : Scheme.{u}} (t : X ⟶ W) (a : W ⟶ O) (b : O ⟶ T)
    (s : X ⟶ O) (j : X ⟶ Z) (z : Z ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j]
    [IsProper s] [IsProper z] (ht : t ≫ a = s) (hs : IsPullback s j b z)
    (M : DerivedCategoryModule A X) :
    D((b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t a s ht).hom.app M) ≫
        (openImmersionLowerShriekLowerStarExchangeIso A hs).hom.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) a b).inv.app (R((t)_*[ModuleCat.{u + 1} A]).obj M) ≫
        (openImmersionLowerShriekLowerStarExchangeIso A
          (by
            simpa only [Category.id_comp] using
              (IsPullback.of_vert_isIso_mono (snd := 𝟙 X)
                (CommSq.mk (by simpa using ht))).paste_vert hs)).hom.app M := by
  let := unbounded_has_base_change A
  let htri : IsPullback t (𝟙 X) a s :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using ht⟩
  have h := triangle_transport (unboundedFormalism A) t a b s j z htri hs M
  have hid : (unboundedFormalism A).shId X =
      mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X := by
    rw [unbounded_sh_id, mapDerivedCategoryOpenImmersionLowerShriekId,
      openImmersionLowerShriekId, identity_leftAdjoint_compare]
  rw [unbounded_open_exchange A htri, unbounded_open_exchange A hs,
    unbounded_open_exchange A (by
      simpa only [Category.id_comp] using htri.paste_vert hs), unbounded_sh_comp, hid] at h
  simpa only [unboundedFormalism,
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
    mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_trans,
    Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.comp_id, openImmersionLowerShriekLowerStarExchangeIso, asIso_hom,
    Functor.comp_obj, Functor.id_obj] using h

private theorem exchange_open_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X W Z T : Scheme.{u}} (t : X ⟶ W) (j : X ⟶ Z) (z : Z ⟶ T)
    {b b' : W ⟶ T} [IsOpenImmersion b] [IsOpenImmersion b']
    [IsOpenImmersion j] [IsProper z] (h : b = b')
    (sq : IsPullback t j b z) (sq' : IsPullback t j b' z)
    (M : DerivedCategoryModule A X) :
    (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) h).hom.app (R((t)_*[ModuleCat.{u + 1} A]).obj M) ≫
        (openImmersionLowerShriekLowerStarExchangeIso A sq').hom.app M =
      (openImmersionLowerShriekLowerStarExchangeIso A sq).hom.app M := by
  subst b'
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- The intersection comparison is unchanged after transport along the proper graph.

Source: Stacks Tags 0F7C--0F7D, vertical and horizontal pasting;
`lem-pur-etale-graph-refinement-normalization`, steps 2--3.
(auxiliary; not a blueprint node).

Proof: put T = r.Z ×_Y s.Z, O₁ = T ×_{s.Z} X and O₂ = T ×_{r.Z} X.
The proper graph z = (1,rs.hom) pulls both O₁ and O₂ back to r.i:X -> r.Z,
by square₁ and square₂. Pulling back their intersection W gives the same X,
since r.i is mono. Let uν:W -> Oν be the open projections and sW the common
proper graph. For each ν paste the identity-top graph square for sW,uν,sν
vertically with the Cartesian square for sν,r.i,bν,z. The outer square is
the same for both ν, since u₁b₁ = u₂b₂ and both upstairs lifts are 1_X.
Vertical proper/open pasting expresses its exchange as the triangle exchange
followed by transportν and the open compositor. Identity normalization removes
the upstairs identity extension. Equate the two expressions for the outer
exchange and cancel the invertible first triangle. The remaining open
compositor--triangle word is precisely locallyClosedGraphMiddle. Whisker by
the common exterior R(p)_*, insert its two associators, and compose with the
same proper compositor Rz_* Rp_* -> R(r.g)_*. This is the displayed equation.
There are no graph side maps or refinement comparison in this assertion.
Empty opens and identity refinements use the same pasting and identity laws. -/
theorem etaleRefinementGraphMiddleTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
    (rs : r.Refinement s) (hs : IsPullback r.i (𝟙 X) rs.hom s.i) :
    EtaleRefinementGraph.middle s r A ≪≫ EtaleRefinementGraph.transport₂ s r rs A =
      EtaleRefinementGraph.transport₁ s r rs A hs := by
  let B := ModuleCat.{u + 1} A
  let t := locallyClosedGraphS₁₂ (𝟙 X) r.i r.g s.i s.g
    (EtaleRefinementGraph.equation s r)
  let a₁ := pullback.fst (EtaleRefinementGraph.b₁ s r) (EtaleRefinementGraph.b₂ s r)
  let a₂ := pullback.snd (EtaleRefinementGraph.b₁ s r) (EtaleRefinementGraph.b₂ s r)
  have ht₁ : t ≫ a₁ = EtaleRefinementGraph.s₁ s r := by
    exact pullback.lift_fst _ _ _
  have ht₂ : t ≫ a₂ = EtaleRefinementGraph.s₂ s r := by
    exact pullback.lift_snd _ _ _
  let sq₁ := EtaleRefinementGraph.square₁ s r rs hs
  let sq₂ := EtaleRefinementGraph.square₂ s r rs
  let out₁ : IsPullback t r.i (a₁ ≫ EtaleRefinementGraph.b₁ s r)
      (EtaleRefinementGraph.z s r rs) := by
    simpa only [Category.id_comp] using
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 X)
        (CommSq.mk (by simpa using ht₁))).paste_vert sq₁
  let out₂ : IsPullback t r.i (a₂ ≫ EtaleRefinementGraph.b₂ s r)
      (EtaleRefinementGraph.z s r rs) := by
    simpa only [Category.id_comp] using
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 X)
        (CommSq.mk (by simpa using ht₂))).paste_vert sq₂
  have hraw :
      (locallyClosedGraphMiddle (𝟙 X) r.i r.g s.i s.g
          (EtaleRefinementGraph.equation s r) A).hom ≫
          (openImmersionLowerShriekLowerStarExchangeIso A sq₂).hom =
        (openImmersionLowerShriekLowerStarExchangeIso A sq₁).hom := by
    apply NatTrans.ext
    funext M
    have h₁ := concrete_triangle_transport A t a₁ (EtaleRefinementGraph.b₁ s r)
      (EtaleRefinementGraph.s₁ s r) r.i (EtaleRefinementGraph.z s r rs) ht₁ sq₁ M
    have h₂ := concrete_triangle_transport A t a₂ (EtaleRefinementGraph.b₂ s r)
      (EtaleRefinementGraph.s₂ s r) r.i (EtaleRefinementGraph.z s r rs) ht₂ sq₂ M
    have hc := exchange_open_congr A t r.i (EtaleRefinementGraph.z s r rs)
      (pullback.condition (f := EtaleRefinementGraph.b₁ s r)
        (g := EtaleRefinementGraph.b₂ s r)) out₁ out₂ M
    simp only [NatTrans.comp_app, locallyClosedGraphMiddle,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc]
    rw [h₂]
    dsimp only [a₂, t, EtaleRefinementGraph.b₂] at *
    simp only [Iso.hom_inv_id_app_assoc]
    rw [hc, ← h₁]
    dsimp only [a₁, EtaleRefinementGraph.b₁, EtaleRefinementGraph.s₁]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply Iso.ext
  ext M
  simp only [EtaleRefinementGraph.middle, EtaleRefinementGraph.transport₁,
    EtaleRefinementGraph.transport₂, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc]
  simpa only [NatTrans.comp_app] using congrArg
    (fun q ↦ (R((EtaleRefinementGraph.p s r)_*[B])).map q ≫
      (rightDerivedLowerStarCompOfEq B (EtaleRefinementGraph.z s r rs)
        (EtaleRefinementGraph.p s r) r.g (EtaleRefinementGraph.z_p s r rs)).hom.app
          (D((r.i)_!open[B]).obj M)) (congr_app hraw M)

end AlgebraicGeometry.Etale
