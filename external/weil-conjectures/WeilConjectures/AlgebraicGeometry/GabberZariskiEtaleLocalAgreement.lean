/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.EtalePullbackUnitPointedWitness

/-! # Local reflection of equality for the Zariski–étale unit
Source: Stacks Project, Tag 09ZF, first proof paragraph.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

-- Descent along the single surjective étale map onto the open image.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem etale_agreement_on_open_image
    {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (W : X.Opens) (U : X.Etale) (g : U ⟶ Scheme.Etale.mk W.ι)
    (s t : F.obj.obj (op (Scheme.Etale.mk W.ι)))
    (heq : F.obj.map g.op s = F.obj.map g.op t) :
    ∃ (W0 : X.Opens) (_ : Set.range U.hom ⊆ (W0 : Set X)) (h : W0 ⟶ W),
      F.obj.map ((MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun V ↦ (inferInstance : Etale V.ι)) (fun _ ↦ trivial)
        (fun _ ↦ trivial)).map h).op s =
      F.obj.map ((MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun V ↦ (inferInstance : Etale V.ι)) (fun _ ↦ trivial)
        (fun _ ↦ trivial)).map h).op t := by
  let : Etale U.hom := U.prop
  let W0 : X.Opens := ⟨Set.range U.hom, U.hom.isOpenMap.isOpen_range⟩
  have hW : W0 ≤ W := by
    rintro x ⟨y, rfl⟩
    have e := congrArg (fun k : U.left ⟶ X ↦ k y) (MorphismProperty.Over.w g)
    exact e ▸ (g.left y).property
  let h : W0 ⟶ W := homOfLE hW
  let q : U.left ⟶ W0.toScheme :=
    IsOpenImmersion.lift W0.ι U.hom (by rw [Scheme.Opens.range_ι]; exact fun _ hx ↦ hx)
  have hq : q ≫ W0.ι = U.hom := IsOpenImmersion.lift_fac _ _ _
  let q' : U ⟶ Scheme.Etale.mk W0.ι :=
    MorphismProperty.Over.homMk q hq
  have hsurj : Function.Surjective q := by
    intro x
    obtain ⟨y, hy⟩ := x.property
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun k : U.left ⟶ X ↦ k y) hq).trans hy
  let j := (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
    X.restrictFunctor (fun V ↦ (inferInstance : Etale V.ι)) (fun _ ↦ trivial)
    (fun _ ↦ trivial)).map h
  have hfac : q' ≫ j = g := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono W.ι).mp
    change (q ≫ X.homOfLE hW) ≫ W.ι = g.left ≫ W.ι
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact hq.trans (MorphismProperty.Over.w g).symm
  have hcover : Sieve.generate (Presieve.singleton q') ∈ X.smallEtaleTopology _ := by
    have hc := (Scheme.ofArrows_mem_smallEtaleTopology_iff
      (fun _ : Unit ↦ q')).mpr (by simpa only [Set.iUnion_const] using
        (show Set.range q'.left = Set.univ from Set.range_eq_univ.mpr hsurj))
    convert hc using 1
    congr 1
    funext T k
    apply propext
    constructor
    · rintro ⟨⟩
      exact Presieve.ofArrows.mk ()
    · rintro ⟨a⟩
      exact Presieve.singleton_self _
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp F.property).isSheafFor
    (Presieve.singleton q') hcover |>.isSeparatedFor
  refine ⟨W0, fun _ hx ↦ hx, h, ?_⟩
  apply (Presieve.isSeparatedFor_singleton.mp hsep)
  change F.obj.map q'.op (F.obj.map j.op s) = F.obj.map q'.op (F.obj.map j.op t)
  have hs := congrArg (fun k ↦ k s) (F.obj.map_comp j.op q'.op)
  have ht := congrArg (fun k ↦ k t) (F.obj.map_comp j.op q'.op)
  have hfop : j.op ≫ q'.op = g.op := congrArg Quiver.Hom.op hfac
  calc
    _ = F.obj.map (j.op ≫ q'.op) s := hs.symm
    _ = F.obj.map g.op s := congrArg (fun k ↦ F.obj.map k s) hfop
    _ = F.obj.map g.op t := heq
    _ = F.obj.map (j.op ≫ q'.op) t := (congrArg (fun k ↦ F.obj.map k t) hfop).symm
    _ = _ := ht

/-- Equality of pulled-back sections on a neighbourhood of z reflects to equality
on an open neighbourhood of i(z) in X.
Source: Stacks Project, Tag 09ZF (lemma-gabber-h0), first proof paragraph.
(blueprint: lem-weil-pbc-gabber-zariski-etale-local-agreement).

Proof: express the étale unit as the identity-indexed coprojection into the
presheaf left Kan extension followed by sheafification. Equality in the
sheafification is locally equality in that presheaf. Choose a point over z
in the resulting étale cover. Base change preserves finite limits, so the
index category is filtered; equality of the two classes is witnessed on an
étale X-scheme U with a point above i(z). Its image W0 is open, contains i(z),
and lies in W. Factor U through W0. This is a surjective étale morphism, hence
an étale covering. The two sections agree after restriction to U; separatedness
of F on that cover makes them agree on W0. Naturality and injectivity of the
presheaf isomorphism eX give the asserted equality in Fzar. The maps a and ha
identify the open preimage with the fibre product and its projection.
The assumed z in V rules out empty neighbourhoods; for empty Z the statement
has no instances. No finiteness hypothesis or closedness beyond that supplied
by the parent is used. -/
theorem gabber_zariski_etale_local_agreement
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (Fzar : TopCat.Sheaf (Type (max (u + 1) v)) X.carrier)
    (eX : Fzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙ F.obj)
    (iFzar : TopCat.Sheaf (Type (max (u + 1) v)) Z.carrier)
    (eZ : iFzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        Z.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj F).obj)
    (a : ∀ W : X.Opens, Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk W.ι))
    (ha : ∀ W : X.Opens,
      (a W).hom.left ≫ pullback.fst W.ι i = i ∣_ W)
    (W : X.Opens) (z : Z.carrier) (hzW : i.base z ∈ W)
    (V : Z.Opens) (hzV : z ∈ V) (f : V ⟶ i ⁻¹ᵁ W)
    (s t : Fzar.obj.obj (op W))
    (heq : iFzar.obj.map f.op
      (eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s)))) =
      iFzar.obj.map f.op
      (eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) t))))) :
    ∃ (W0 : X.Opens) (_ : i.base z ∈ W0) (g : W0 ⟶ W),
      Fzar.obj.map g.op s = Fzar.obj.map g.op t := by
  have _ := ha W
  have _ := hzW
  let jZ := MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
    Z.restrictFunctor (fun U ↦ (inferInstance : Etale U.ι)) (fun _ ↦ trivial)
    (fun _ ↦ trivial)
  let iF := (Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
    (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj F
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
    (X.smallGrothendieckTopology @Etale)
    (Z.smallGrothendieckTopology @Etale)).unit.app F).hom
  let ss := η.app (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s)
  let tt := η.app (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) t)
  have heq' : iF.obj.map ((jZ.map f) ≫ (a W).hom).op ss =
      iF.obj.map ((jZ.map f) ≫ (a W).hom).op tt := by
    have e := congrArg (fun x ↦ eZ.hom.app (op V) x) heq
    simp only [← NatTrans.naturality_apply, Iso.inv_hom_id_app_apply] at e
    change iF.obj.map (jZ.map f).op (iF.obj.map (a W).hom.op ss) =
      iF.obj.map (jZ.map f).op (iF.obj.map (a W).hom.op tt) at e
    exact (congrArg (fun k ↦ k ss)
      (iF.obj.map_comp (a W).hom.op (jZ.map f).op)).trans
      (e.trans (congrArg (fun k ↦ k tt)
        (iF.obj.map_comp (a W).hom.op (jZ.map f).op)).symm)
  obtain ⟨U, g, u, hu, hst⟩ := etale_pullback_unit_pointed_witness i F
    (Scheme.Etale.mk W.ι) (Scheme.Etale.mk V.ι) ((jZ.map f) ≫ (a W).hom)
    ⟨z, hzV⟩ (eX.hom.app (op W) s) (eX.hom.app (op W) t) heq'
  obtain ⟨W0, hW0, h, hh⟩ := etale_agreement_on_open_image F W U g
    (eX.hom.app (op W) s) (eX.hom.app (op W) t) hst
  refine ⟨W0, hW0 ⟨u, hu⟩, h, ?_⟩
  apply ((isIso_iff_bijective _).mp (inferInstance : IsIso (eX.hom.app (op W0)))).1
  exact (eX.hom.naturality_apply h.op s).trans
    (hh.trans (eX.hom.naturality_apply h.op t).symm)

end AlgebraicGeometry
