/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.EtaleClosedSectionLocalFamily
import WeilConjectures.AlgebraicGeometry.EtaleFiniteFamilySectionGluing
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Topology.ClosedPushforwardConstantStalks

/-! # A surjective étale cover representing a Gabber section

Source: Stacks Project, Tag 09ZF, fourth proof paragraph, through surjectivity
of the union of the local representing étale schemes.
(blueprint: lem-weil-pbc-gabber-h0-etale-cover-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem gabber_open_detection
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Injective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (W : X.Opens) (hW : Set.range i ⊆ W) : W = ⊤ := by
  classical
  let C : Set X := (W : Set X)ᶜ
  let P := TopCat.closedPushforwardConstantPresheaf X.toTopCat C (ULift.{u} Bool)
  have hP : P.IsSheaf :=
    (TopCat.closed_pushforward_constant_stalks X.toTopCat C
      W.isOpen.isClosed_compl (ULift.{u} Bool)).1
  let G : TopCat.Sheaf (Type (u + 1)) X.toTopCat :=
    ⟨P ⋙ uliftFunctor.{u + 1}, by
      change Presheaf.IsSheaf (Opens.grothendieckTopology X) P at hP
      rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
      exact (Presieve.isSheaf_comp_uliftFunctor_iff _).mpr hP⟩
  let a : G.obj.obj (op (⊤ : X.Opens)) :=
    ⟨LocallyConstant.const _ ⟨false⟩⟩
  let b : G.obj.obj (op (⊤ : X.Opens)) :=
    ⟨LocallyConstant.const _ ⟨true⟩⟩
  have hab : G.obj.map (homOfLE (le_top : W ≤ ⊤)).op a =
      G.obj.map (homOfLE (le_top : W ≤ ⊤)).op b := by
    apply ULift.ext
    apply LocallyConstant.ext
    intro x
    exact False.elim (x.2.2 x.2.1)
  let : ∀ Q : X.Opensᵒᵖ ⥤ Type (u + 1),
      (Opens.map i.base).op.HasPointwiseLeftKanExtension Q :=
    fun Q U ↦ @Types.hasColimit.{u, u + 1, u}
      (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
      inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ Q)
  let η := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map i.base) (Type (u + 1))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom
  have he : (Opens.map i.base).obj W = (Opens.map i.base).obj ⊤ := by
    ext z
    change i z ∈ W ↔ i z ∈ (⊤ : X.Opens)
    exact ⟨fun _ ↦ trivial, fun _ ↦ hW ⟨z, rfl⟩⟩
  have hn := ConcreteCategory.congr_hom (η.naturality
    (homOfLE (le_top : W ≤ ⊤)).op) a
  have hm := ConcreteCategory.congr_hom (η.naturality
    (homOfLE (le_top : W ≤ ⊤)).op) b
  have hi : IsIso ((Opens.map i.base).map (homOfLE (le_top : W ≤ ⊤))) :=
    ⟨⟨eqToHom he.symm, by apply Subsingleton.elim, by apply Subsingleton.elim⟩⟩
  have heq : η.app (op (⊤ : X.Opens)) a = η.app (op (⊤ : X.Opens)) b := by
    apply (ConcreteCategory.bijective_of_isIso
      (((Functor.sheafPullbackConstruction.sheafPullback (Opens.map i.base)
        (Type (u + 1)) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Z)).obj G).obj.map
        (((Opens.map i.base).map (homOfLE (le_top : W ≤ ⊤))).op))).injective
    exact hn.symm.trans ((congrArg (η.app (op W)) hab).trans hm)
  have h := hZar G heq
  apply top_unique
  intro x hx
  by_contra hxW
  have hh := congrArg (fun s : G.obj.obj (op (⊤ : X.Opens)) ↦
    (show LocallyConstant {y : X // y ∈ (⊤ : X.Opens) ∧ y ∈ C}
      (ULift.{u} Bool) from s.down) ⟨x, Opens.mem_top x, hxW⟩) h
  cases hh

/-- A global inverse-image section has a representative on a surjective étale cover.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph, before finite refinement.
(blueprint: lem-weil-pbc-gabber-h0-etale-cover-section).

Proof:
1. Every nonempty closed subset of X meets i(Z). Otherwise the two constant
   sections of the closed pushforward of the constant two-element sheaf have
   equal restrictions, because its inverse-image stalks on Z are singletons.
   Section determination by germs contradicts injectivity of hZar.
2. Apply local sheafification and colimit representatives to t, after identifying
   the base change of the identity object with the identity object of Z. This
   gives an étale cover V_j of Z, étale X-schemes U_j, sections s_j, and maps
   V_j to U_j times_X Z on which the restrictions of t and i^*s_j agree.
3. Each map V_j to U_j times_X Z is étale, hence has open image. Since the latter
   embeds as a closed subscheme of U_j, extend that image to an ambient open and
   restrict U_j and s_j. The map V_j is now surjective, so separatedness for this
   one-member étale cover gives equality on all of U_j times_X Z.
4. The open union of the images of U_j contains i(Z); its closed complement is
   empty by step 1. By compactness choose finitely many of these images covering X.
   Take their finite disjoint union U. It is étale and surjective over X. The
   sections s_j glue on this disjoint union (overlaps are empty), giving s.
   Naturality of the inverse-image unit and the sheaf axiom on its base change
   give the displayed equation. Finite disjoint unions keep U in universe u.
For empty X use the empty étale cover, whose sections exist uniquely by the
empty-cover sheaf axiom. No nonemptiness of X or Z is assumed. -/
theorem gabber_h0_etale_cover_section
    {X Z : Scheme.{u}} [CompactSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Injective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X))))) :
    ∃ (U : Scheme.{u}) (q : U ⟶ X) (_ : Etale q) (_ : Surjective q)
      (s : F.obj.obj (op (Scheme.Etale.mk q))),
      etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk q (Category.comp_id q) :
              Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
  classical
  obtain ⟨J, U, s, hnear, heq⟩ := etale_closed_section_local_family i F t
  let W : X.Opens := ⟨⋃ j, Set.range (U j).hom,
    isOpen_iUnion (fun j ↦ (U j).hom.isOpenMap.isOpen_range)⟩
  have hW : W = ⊤ := gabber_open_detection i hZar W hnear
  have hcover : (Set.univ : Set X) ⊆ ⋃ j, Set.range (U j).hom := by
    change (Set.univ : Set X) ⊆ W
    rw [hW]
    exact Set.Subset.rfl
  obtain ⟨K, hK⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (fun j : J ↦ Set.range ((U j).hom : (U j).left → X))
    (fun j ↦ (U j).hom.isOpenMap.isOpen_range) hcover
  have hfinite : (Set.univ : Set X) ⊆ ⋃ j : K, Set.range (U j.val).hom := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hK hx)
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
  exact etale_finite_family_section_gluing i F t
    (fun j : K ↦ U j.val) (fun j : K ↦ s j.val) hfinite (fun j ↦ heq j.val)

end AlgebraicGeometry
