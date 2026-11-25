/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # The two projection boundaries of a proper refinement graph

Source: Stacks Project, Tags 0F7C--0F7E, and steps 3--4 of
`lem-pur-etale-graph-refinement-normalization`.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem projection_boundary
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasBaseChange]
    {X U O R T S Y : Scheme.{u}}
    (x : X ⟶ O) (q : O ⟶ U) (h : X ⟶ U)
    (k : X ⟶ R) (b : O ⟶ T) (j : U ⟶ S)
    (z : R ⟶ T) (p : T ⟶ S) (v : R ⟶ S)
    (g : S ⟶ Y) (d : T ⟶ Y) (rg : R ⟶ Y)
    [IsOpenImmersion k] [IsOpenImmersion b] [IsOpenImmersion j]
    (sx : IsPullback x k b z) (sq : IsPullback q b j p)
    (so : IsPullback h k j v) (hxq : x ≫ q = h) (hzp : z ≫ p = v)
    (hpg : p ≫ g = d) (hzd : z ≫ d = rg) (hvg : v ≫ g = rg)
    (M : F.obj X) :
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sx
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) so
    (F.pf g).map ((F.sh j).map ((F.pfComp' x q h hxq).hom.app M) ≫
        (F.exchange q b j p sq.w).app ((F.pf x).obj M)) ≫
      (F.pfComp' p g d hpg).inv.app ((F.sh b).obj ((F.pf x).obj M)) ≫
      (F.pf d).map ((F.exchange x k b z sx.w).app M) ≫
      (F.pfComp' z d rg hzd).inv.app ((F.sh k).obj M) =
    (F.pf g).map ((F.exchange h k j v so.w).app M) ≫
      (F.pfComp' v g rg hvg).inv.app ((F.sh k).obj M) := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sx
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) so
  have hp := congr_app (F.exchange_paste_horiz x q k b j z p h v
    sx.w sq.w hxq hzp so.w) M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj] at hp
  have hn := (F.pfComp' p g d hpg).inv.naturality
    ((F.exchange x k b z sx.w).app M)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [F.pfComp'_assoc_inv_app z p g v d rg hzp hpg hvg hzd]
  rw [← (F.pf g).map_comp_assoc, ← (F.pf g).map_comp_assoc]
  simp only [Category.assoc] at hp ⊢
  rw [← hp]

private theorem refinement_projection_boundary
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasBaseChange]
    {X Y T O : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
    (rs : r.Refinement s) (hs : IsPullback r.i (𝟙 X) rs.hom s.i)
    (x : X ⟶ O) (q : O ⟶ X) (b : O ⟶ T)
    (z : r.Z ⟶ T) (p : T ⟶ s.Z) (d : T ⟶ Y)
    [IsOpenImmersion b] (sx : IsPullback x r.i b z)
    (sq : IsPullback q b s.i p) (hxq : x ≫ q = 𝟙 X)
    (hzp : z ≫ p = rs.hom) (hpg : p ≫ s.g = d) (hzd : z ≫ d = r.g)
    (M : F.obj X) :
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sx
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
    (F.pf s.g).map ((F.sh s.i).map ((F.pfId X).inv.app M ≫
        (F.pfComp' x q (𝟙 X) hxq).hom.app M) ≫
        (F.exchange q b s.i p sq.w).app ((F.pf x).obj M)) ≫
      (F.pfComp' p s.g d hpg).inv.app ((F.sh b).obj ((F.pf x).obj M)) ≫
      (F.pf d).map ((F.exchange x r.i b z sx.w).app M) ≫
      (F.pfComp' z d r.g hzd).inv.app ((F.sh r.i).obj M) =
    (F.refinementComparison rs hs).app M := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sx
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) hs.flip
  have h := projection_boundary F x q (𝟙 X) r.i b s.i z p rs.hom
    s.g d r.g sx sq hs.flip hxq hzp hpg hzd rs.hom_g M
  have hh := congrArg
    (fun t ↦ (F.pf s.g).map ((F.sh s.i).map ((F.pfId X).inv.app M)) ≫ t) h
  rw [CompactSupportFormalism.refinementComparison_app]
  simpa only [Functor.map_comp, Category.assoc] using hh

private theorem concrete_pf_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (unboundedFormalism A).pfComp' f g h w =
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g h w).symm := by
  subst h
  exact unbounded_pf_comp A f g

private theorem concrete_refinement_projection_boundary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y T O : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
    (rs : r.Refinement s) (hs : IsPullback r.i (𝟙 X) rs.hom s.i)
    (x : X ⟶ O) (q : O ⟶ X) (b : O ⟶ T)
    (z : r.Z ⟶ T) (p : T ⟶ s.Z) (d : T ⟶ Y)
    [IsOpenImmersion b] [IsProper z] [IsProper p]
    (sx : IsPullback x r.i b z) (sq : IsPullback q b s.i p)
    (hxq : x ≫ q = 𝟙 X) (hzp : z ≫ p = rs.hom)
    (hpg : p ≫ s.g = d) (hzd : z ≫ d = r.g)
    (M : DerivedCategoryModule A X) :
    R((s.g)_*[ModuleCat.{u + 1} A]).map
        (D((s.i)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarIdIso A X).inv.app M ≫
            (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
              x q (𝟙 X) hxq).inv.app M) ≫
          (openImmersionLowerShriekLowerStarExchangeIso A sq).hom.app
            (R((x)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        p s.g d hpg).hom.app
          (D((b)_!open[ModuleCat.{u + 1} A]).obj
            (R((x)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((d)_*[ModuleCat.{u + 1} A]).map
        ((openImmersionLowerShriekLowerStarExchangeIso A sx).hom.app M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        z d r.g hzd).hom.app (D((r.i)_!open[ModuleCat.{u + 1} A]).obj M) =
    (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) rs hs).app M := by
  let := unbounded_has_base_change A
  have h := refinement_projection_boundary (unboundedFormalism A) s r rs hs
    x q b z p d sx sq hxq hzp hpg hzd M
  rw [unbounded_refinement_comparison A rs hs] at h
  simp only [concrete_pf_comp, Iso.symm_hom, Iso.symm_inv,
    unbounded_open_exchange A sx, unbounded_open_exchange A sq,
    unbounded_pf_id] at h
  simpa only [unboundedFormalism, rightDerivedLowerStarIdIso,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom] using h

/-- The first transported side is the specified refinement map; the second removes R(1)_*.

Source: Stacks Tags 0F7C--0F7E, projection pasting; the normalized refinement map in
`LowerShriekIndependenceUnbounded.lean` and its open-unit normalization in
`OpenImmersionLowerShriekProjectionBaseChange.lean`.
(auxiliary; not a blueprint node).

Proof: paste the square of square₁ horizontally with the proper/open square for
pr₂:T -> s.Z and s.i. The composite upper proper arrow is s₁q₁ = 1_X,
and the composite lower proper arrow is z pr₂ = rs.hom. Horizontal exchange
pasting therefore identifies the transported first side with the exchange for
the supplied refinement square. The exterior proper compositors agree by
associativity of the normalized K-injective compositor, or equivalently by
conjugating the associative exact inverse-image compositor. Removing R(1_X)_*
uses its canonical identity isomorphism. Expand the resulting exchange as its
adjunction unit, inverse open base change and identity counit. The unit mate
equation identifies the open factor with refinementLowerShriekBaseChangeDerivedIso;
the composite-adjunction normalization identifies the proper compositor with
refinementLowerStarComp. These are the three factors of the stated refinement map.
For the second side paste square₂ with the square for pr₁:T -> r.Z and r.i.
Now the composite upper and lower proper arrows are both identities, since
s₂q₂ = 1_X and z pr₁ = 1_{r.Z}. Horizontal exchange pasting and its identity
normalization reduce this side to rightDerivedLowerStarIdIso on X, whiskered
by Dr.i_! Rr.g_*. Its left unitor is exactly etaleGraphOpenNormalization.
No intersection comparison is used in either side computation. The proof
requires no quasi-compactness and applies to identity or empty opens. -/
theorem etaleRefinementGraphSideTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
    (rs : r.Refinement s) (hs : IsPullback r.i (𝟙 X) rs.hom s.i) :
    (locallyClosedGraphSide₁ (𝟙 X) r.i r.g s.i s.g
        (EtaleRefinementGraph.equation s r) A ≪≫
        EtaleRefinementGraph.transport₁ s r rs A hs =
      asIso (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) rs hs)) ∧
    (locallyClosedGraphSide₂ (𝟙 X) r.i r.g s.i s.g
        (EtaleRefinementGraph.equation s r) A ≪≫
        EtaleRefinementGraph.transport₂ s r rs A = etaleGraphOpenNormalization A r) := by
  constructor
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    have h := concrete_refinement_projection_boundary A s r rs hs
      (EtaleRefinementGraph.s₁ s r) (pullback.snd (pullback.snd r.g s.g) s.i)
      (EtaleRefinementGraph.b₁ s r) (EtaleRefinementGraph.z s r rs)
      (pullback.snd r.g s.g) (EtaleRefinementGraph.p s r)
      (EtaleRefinementGraph.square₁ s r rs hs)
      (IsPullback.of_hasPullback (pullback.snd r.g s.g) s.i).flip
      (by simp [EtaleRefinementGraph.s₁, locallyClosedGraphS₁])
      (by simp [EtaleRefinementGraph.z]) pullback.condition.symm
      (EtaleRefinementGraph.z_p s r rs) M
    simpa only [locallyClosedGraphSide₁, EtaleRefinementGraph.transport₁,
      Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id,
      Functor.map_comp, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
      EtaleRefinementGraph.s₁, EtaleRefinementGraph.b₁, EtaleRefinementGraph.p,
      Category.assoc, asIso_hom] using h
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    let rr : r.Refinement r :=
      ⟨𝟙 r.Z, Category.comp_id r.i, Category.id_comp r.g⟩
    let hs' : IsPullback r.i (𝟙 X) rr.hom r.i := IsPullback.id_vert r.i
    have h := concrete_refinement_projection_boundary A r r rr hs'
      (EtaleRefinementGraph.s₂ s r) (pullback.snd (pullback.fst r.g s.g) r.i)
      (EtaleRefinementGraph.b₂ s r) (EtaleRefinementGraph.z s r rs)
      (pullback.fst r.g s.g) (EtaleRefinementGraph.p s r)
      (EtaleRefinementGraph.square₂ s r rs)
      (IsPullback.of_hasPullback (pullback.fst r.g s.g) r.i).flip
      (by simp [EtaleRefinementGraph.s₂, locallyClosedGraphS₂])
      (by simp [EtaleRefinementGraph.z, rr]) rfl
      (EtaleRefinementGraph.z_p s r rs) M
    have hr : rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) rr hs' = 𝟙 _ := by
      let := unbounded_has_base_change A
      rw [← unbounded_refinement_comparison A rr hs']
      exact CompactSupportFormalism.refinementComparison_eq_id
        (unboundedFormalism A) rr hs' rfl
    rw [hr, NatTrans.id_app] at h
    apply (cancel_epi ((etaleGraphOpenNormalization A r).inv.app M)).1
    rw [Iso.inv_hom_id_app]
    simpa only [locallyClosedGraphSide₂, EtaleRefinementGraph.transport₂,
      etaleGraphOpenNormalization, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.leftUnitor_hom_app,
      EtaleGraphPresentation.ofCompactification,
      EtaleRefinementGraph.s₂, EtaleRefinementGraph.b₂, EtaleRefinementGraph.p,
      Functor.comp_map, Functor.comp_obj, Functor.id_obj,
      Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp] using h

end AlgebraicGeometry.Etale
