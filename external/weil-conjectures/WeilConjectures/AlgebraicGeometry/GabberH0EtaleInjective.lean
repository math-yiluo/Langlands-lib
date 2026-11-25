/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescent
import WeilConjectures.AlgebraicGeometry.GabberZariskiEtaleRestrictionInjective
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites

/-! # Injectivity of étale restriction from Zariski restriction

Source: Stacks Project, Tag 09ZF, first two proof paragraphs
(blueprint: lem-weil-pbc-gabber-h0-etale-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private noncomputable abbrev zarEtale (X : Scheme.{u}) :=
  MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
    X.restrictFunctor (fun U ↦ (inferInstance : Etale U.ι)) (fun _ ↦ trivial)
    (fun _ ↦ trivial)
private theorem zarEtale_continuous (X : Scheme.{u}) :
    (zarEtale X).IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology := by
  obtain ⟨k, hk, _, _, _, hcont, _⟩ := zariski_to_etale_is_morphism.{u, 0} X
  let : k.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology := hcont
  have hj : zarEtale X ⋙ Scheme.Etale.forget X = X.restrictFunctor := rfl
  let e : k ≅ zarEtale X :=
    ((Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget X)).whiskeringRight
      X.Opens).preimageIso (eqToIso (hk.trans hj.symm))
  exact Functor.isContinuous_of_iso e _ _


/-- Zariski bijectivity implies injectivity of the étale unit on global sections.
Source: Stacks Project, Tag 09ZF, first two proof paragraphs
(blueprint: lem-weil-pbc-gabber-h0-etale-injective).

Proof:
1. Restrict F and its inverse image to open subschemes, obtaining Zariski sheaves.
   The inclusion is continuous by
   `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`. Base changes of open
   subschemes give the canonical isomorphisms used in the comparison theorem.
2. Apply `lem-weil-pbc-gabber-zariski-etale-restriction-injective`. Its unit equation
   factors the étale unit at the top open as the Zariski unit followed by its
   injective comparison. The Zariski unit is injective by hZar.
3. The top-open inclusion and the identity object are both terminal in X.Etale.
   Transport the factorization along their unique isomorphism, and likewise on Z.
   Naturality of the units identifies the transported map with the stated unit.
   Isomorphisms induce bijections on sections, so this unit is injective.
No quasi-compactness, quasi-separatedness, or finite base-change hypothesis is needed. -/
theorem gabber_h0_etale_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Bijective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentUnit i F (Scheme.Etale.mk (𝟙 X))) := by
  let : (zarEtale X).IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology := zarEtale_continuous X
  let : (zarEtale Z).IsContinuous (Opens.grothendieckTopology Z.carrier)
      Z.smallEtaleTopology := zarEtale_continuous Z
  let Fzar : TopCat.Sheaf (Type (u + 1)) X.carrier :=
    ((zarEtale X).sheafPushforwardContinuous (Type (u + 1))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F
  let iFzar : TopCat.Sheaf (Type (u + 1)) Z.carrier :=
    ((zarEtale Z).sheafPushforwardContinuous (Type (u + 1))
      (Opens.grothendieckTopology Z.carrier) Z.smallEtaleTopology).obj
      ((Scheme.etaleSetPullback i).obj F)
  let a : ∀ W : X.Opens, Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk W.ι) :=
    fun W ↦ MorphismProperty.Over.isoMk (isPullback_morphismRestrict i W).isoPullback
      (isPullback_morphismRestrict i W).isoPullback_hom_snd
  have ha : ∀ W : X.Opens,
      (a W).hom.left ≫ pullback.fst W.ι i = i ∣_ W := by
    intro W
    exact (isPullback_morphismRestrict i W).isoPullback_hom_fst
  obtain ⟨beta, hbeta, hunit⟩ := gabber_zariski_etale_restriction_injective.{u, 0}
    i F Fzar (Iso.refl _) iFzar (Iso.refl _) a ha
  have hu := (hunit beta).mpr rfl
  intro s t h
  let e : (zarEtale X).obj ⊤ ≅ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.isoMk X.topIso (by
      change (⊤ : X.Opens).ι ≫ 𝟙 X = (⊤ : X.Opens).ι
      exact Category.comp_id _)
  have hs := hu ⊤ (F.obj.map e.hom.op s)
  have ht := hu ⊤ (F.obj.map e.hom.op t)
  have hn := etaleSetInverseImageCompositionUnits.1 X Z i F
    (Scheme.Etale.mk (𝟙 X)) ((zarEtale X).obj ⊤) e.hom
  have hEt := (hn s).trans ((congrArg
    (((Scheme.etaleSetPullback i).obj F).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ i).map e.hom).op) h).trans (hn t).symm)
  have hZ := hbeta (i ⁻¹ᵁ (⊤ : X.Opens))
    (hs.trans ((congrArg (((Scheme.etaleSetPullback i).obj F).obj.map
      (a ⊤).hom.op) hEt).trans ht.symm))
  have htop := (hZar Fzar).1 hZ
  have hh := congrArg (F.obj.map e.inv.op) htop
  simpa [← Functor.map_comp_apply, ← op_comp] using hh

end AlgebraicGeometry
