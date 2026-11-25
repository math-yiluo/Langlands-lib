/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Topology.Sheaves.Stalks
import WeilConjectures.AlgebraicGeometry.GabberZariskiEtaleLocalAgreement
import WeilConjectures.AlgebraicGeometry.InverseImageStalkPairRepresentatives

/-! # Stalk injectivity of Gabber's comparison
Source: Stacks Project, Tag 09ZF, first proof paragraph.
(blueprint: lem-weil-pbc-gabber-zariski-etale-comparison-stalk-injective)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A comparison satisfying the unit equation is injective on stalks.
Source: Stacks Project, Tag 09ZF (lemma-gabber-h0), first proof paragraph.
(blueprint: lem-weil-pbc-gabber-zariski-etale-comparison-stalk-injective).
Proof: the stalk of the topological inverse image at z identifies with the stalk
of Fzar at i(z). Represent two germs on a common open W around i(z). The unit
equation identifies their images with germs of the étale pullbacks of those
sections. Equality of these germs gives equality on a smaller open of Z around z.
The étale inverse image is the sheafification of the presheaf left Kan extension.
Its unit is the identity-indexed colimit coprojection followed by sheafification.
Local equality for sheafification provides an étale cover on which the two
presheaf classes agree. Choose a point above z in this cover. The indexing
category is filtered, since the étale base-change functor preserves finite
limits. Equality in this filtered colimit is witnessed by an étale X-scheme U
on which the original sections agree, with a point lying over i(z). The image
W0 of U in X is open, lies in W, and contains i(z). Factor U through W0; the
result is a surjective étale map, hence a cover. Separatedness of F for this
cover shows that the original sections agree on W0. Their original germs are
therefore equal, and the stalk inverse-image identification proves the claim.
The empty Z case is vacuous; no quasi-compactness or finite cover is needed.
-/
theorem gabber_zariski_etale_comparison_stalk_injective
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
    (beta :
      (Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map i.base) (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Z.carrier)).obj Fzar ⟶ iFzar)
    (hbeta :(∀ (W : X.Opens) (s : Fzar.obj.obj (op W)),
        beta.hom.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map i.base) (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier)
            (Opens.grothendieckTopology Z.carrier)).unit.app Fzar).hom.app (op W) s) =
        eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s))))) :
    ∀ z : Z.carrier, Function.Injective
      (colim.map (Functor.whiskerLeft (OpenNhds.inclusion z).op beta.hom)) := by
  intro z s t hst
  let H := (Functor.sheafPullbackConstruction.sheafPullback
    (Opens.map i.base) (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier)
    (Opens.grothendieckTopology Z.carrier)).obj Fzar
  let eta := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map i.base) (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier)
    (Opens.grothendieckTopology Z.carrier)).unit.app Fzar
  let D := (OpenNhds.inclusion z).op ⋙ H.obj
  let E := (OpenNhds.inclusion z).op ⋙ iFzar.obj
  obtain ⟨W, hzW, a0, b0, rfl, rfl⟩ :=
    TopCat.inverse_image_stalk_pair_representatives.{u, max (u + 1) v} i.base Fzar z s t
  let n : (OpenNhds z)ᵒᵖ := op ⟨i ⁻¹ᵁ W, hzW⟩
  have himages : colimit.ι E n (beta.hom.app (op (i ⁻¹ᵁ W))
        (eta.hom.app (op W) a0)) =
      colimit.ι E n (beta.hom.app (op (i ⁻¹ᵁ W))
        (eta.hom.app (op W) b0)) := by
    have h := colimit.ι_map (Functor.whiskerLeft (OpenNhds.inclusion z).op beta.hom) n
    have hs := congrArg (fun f ↦ f (eta.hom.app (op W) a0))
      (congrArg ConcreteCategory.hom h)
    have ht := congrArg (fun f ↦ f (eta.hom.app (op W) b0))
      (congrArg ConcreteCategory.hom h)
    exact hs.symm.trans (hst.trans ht)
  obtain ⟨V, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit E) (i := n)
      (beta.hom.app (op (i ⁻¹ᵁ W)) (eta.hom.app (op W) a0))
      (beta.hom.app (op (i ⁻¹ᵁ W)) (eta.hom.app (op W) b0))).mp himages
  change iFzar.obj.map ((OpenNhds.inclusion z).map f.unop).op (beta.hom.app (op (i ⁻¹ᵁ W))
      (eta.hom.app (op W) a0)) =
    iFzar.obj.map ((OpenNhds.inclusion z).map f.unop).op (beta.hom.app (op (i ⁻¹ᵁ W))
      (eta.hom.app (op W) b0)) at hf
  dsimp only [eta] at hf
  rw [hbeta W a0, hbeta W b0] at hf
  obtain ⟨W0, hzW0, g, hg⟩ := gabber_zariski_etale_local_agreement
    i F Fzar eX iFzar eZ a ha W z hzW V.unop.val V.unop.property
    ((OpenNhds.inclusion z).map f.unop) a0 b0 hf
  let n0 : (OpenNhds z)ᵒᵖ := op ⟨i ⁻¹ᵁ W0, hzW0⟩
  let g0 : n ⟶ n0 := (homOfLE (show i ⁻¹ᵁ W0 ≤ i ⁻¹ᵁ W from
    fun x hx ↦ (leOfHom g) hx)).op
  have hunit : H.obj.map ((Opens.map i.base).map g).op (eta.hom.app (op W) a0) =
      H.obj.map ((Opens.map i.base).map g).op (eta.hom.app (op W) b0) := by
    have hs := eta.hom.naturality_apply g.op a0
    have ht := eta.hom.naturality_apply g.op b0
    exact hs.symm.trans ((congrArg (eta.hom.app (op W0)) hg).trans ht)
  have hs := congrArg (fun f ↦ f (eta.hom.app (op W) a0))
    (congrArg ConcreteCategory.hom (colimit.w D g0))
  have ht := congrArg (fun f ↦ f (eta.hom.app (op W) b0))
    (congrArg ConcreteCategory.hom (colimit.w D g0))
  exact hs.symm.trans ((congrArg (colimit.ι D n0) hunit).trans ht)

end AlgebraicGeometry
