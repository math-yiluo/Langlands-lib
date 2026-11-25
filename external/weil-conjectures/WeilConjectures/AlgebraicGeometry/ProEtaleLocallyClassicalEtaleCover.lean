/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Locally classical pro-etale sheaves and etale-local sections

Source: Bhatt--Scholze, Definition 5.1.3, Lemmas 5.1.1--5.1.4 and Proposition 6.8.4(6)
(auxiliary; not a blueprint node).

The three predicates spell out the notions introduced in this node. Restriction to
`U` is precomposition with the existing localization functor, which composes structure
maps with `U.hom`. Covering families use the actual small-site topologies.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction of set-valued sheaves to the small pro-etale site of a cover member.
It is precomposition with the canonical structure-map composition functor.
Source: Bhatt--Scholze, Lemma 5.1.4, restriction to a covering member
(auxiliary; not a blueprint node). -/
def proEtaleSetRestriction (X : Scheme.{u}) (U : X.ProEt) :
    Sheaf (ProEt.topology X) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology U.left) (Type (u + 1)) :=
  @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
    (Type (u + 1)) _ (ProEt.topology U.left) (ProEt.topology X)
    (ProEt.isContinuous_overMap U.prop)

/-- Classical means isomorphic to the canonical inverse image of an etale sheaf of sets.
Source: Bhatt--Scholze, Definition 5.1.3
(auxiliary; not a blueprint node). -/
def IsProEtaleClassical (X : Scheme.{u}) (F : Sheaf (ProEt.topology X) (Type (u + 1))) :
    Prop :=
  ∃ G : Sheaf X.smallEtaleTopology (Type (u + 1)),
    Nonempty (F ≅ (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
      (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj G)

/-- Local classicality uses a pro-etale cover and the sectionwise restriction to each
member's small pro-etale site, with no compatibility imposed on the etale presentations.
Source: Bhatt--Scholze, Lemma 5.1.4
(auxiliary; not a blueprint node). -/
def IsProEtaleLocallyClassical (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1))) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → X.ProEt), (ProEt.topology X).CoversTop U ∧
    ∀ i : I, IsProEtaleClassical (U i).left
      ((proEtaleSetRestriction X (U i)).obj F)

/-- Local constancy allows varying, possibly empty, sets on the members of a pro-etale
cover. The constant sheaves are sheafifications of constant presheaves.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(auxiliary; not a blueprint node). -/
def IsProEtaleLocallyConstant (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1))) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → X.ProEt), (ProEt.topology X).CoversTop U ∧
    ∀ i : I, ∃ S : Type (u + 1), Nonempty
      (((proEtaleSetRestriction X (U i)).obj F) ≅
          (constantSheaf (ProEt.topology (U i).left) (Type (u + 1))).obj S)

private noncomputable def etaleIdentityTerminal (X : Scheme.{u}) :
    IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f ↦ MorphismProperty.Over.Hom.ext (by
      change f.left = U.hom
      have hw : f.left ≫ 𝟙 X = U.hom := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans hw))

private noncomputable def proEtaleIdentityTerminal (X : Scheme.{u}) :
    IsTerminal ((toProEt X).obj (Scheme.Etale.mk (𝟙 X))) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f ↦ MorphismProperty.Over.Hom.ext (by
      change f.left = U.hom
      have hw : f.left ≫ 𝟙 X = U.hom := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans hw))

private noncomputable def comparisonConstantIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (Type (u + 1)) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
        (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X) ≅
      constantSheaf (ProEt.topology X) (Type (u + 1)) :=
  (((constantSheafAdj X.smallEtaleTopology (Type (u + 1))
      (etaleIdentityTerminal X)).comp
        (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _))).leftAdjointUniq
    (constantSheafAdj (ProEt.topology X) (Type (u + 1)) (proEtaleIdentityTerminal X))

private theorem locallyConstant_locallyClassical (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (h : IsProEtaleLocallyConstant X F) : IsProEtaleLocallyClassical X F := by
  obtain ⟨I, U, hU, hF⟩ := h
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  obtain ⟨S, ⟨e⟩⟩ := hF i
  exact ⟨(constantSheaf (U i).left.smallEtaleTopology (Type (u + 1))).obj S,
    ⟨e ≪≫ ((comparisonConstantIso (U i).left).app S).symm⟩⟩

private theorem epi_of_cover_sections
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {F H : Sheaf J (Type (u + 1))} (q : F ⟶ H) (hH : IsTerminal H)
    {I : Type (u + 1)} {U : I → C} (hU : J.CoversTop U)
    (hF : ∀ i, Nonempty (F.obj.obj (op (U i)))) : Epi q := by
  have : Presheaf.IsLocallySurjective J q.hom :=
    Presheaf.isLocallySurjective_of_coversTop hU q.hom (by
      intro V i a t
      have : Unique (H.obj.obj (op V)) := Types.isTerminalEquivUnique _
        (hH.isTerminalObj ((sheafToPresheaf J _) ⋙
          (CategoryTheory.evaluation Cᵒᵖ (Type (u + 1))).obj (op V)))
      obtain ⟨s⟩ := hF i
      exact ⟨F.obj.map a.op s, Subsingleton.elim _ _⟩)
  have : Sheaf.IsLocallySurjective q := this
  infer_instance

private theorem etale_cover_sections_of_classical (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (hF : IsProEtaleClassical X F)
    (hsec : ∃ (I : Type (u + 1)) (U : I → X.ProEt),
      (ProEt.topology X).CoversTop U ∧ ∀ i, Nonempty (F.obj.obj (op (U i)))) :
    ∃ (I : Type (u + 1)) (Y : I → X.Etale),
      X.smallEtaleTopology.CoversTop Y ∧
        ∀ i, Nonempty (F.obj.obj (op ((toProEt X).obj (Y i)))) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  obtain ⟨I, U, hU, hs⟩ := hsec
  let L := Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)
  have hu := proEtaleComparisonUnitSets_isIso X
  have : L.Faithful :=
    (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).faithful_L_of_mono_unit_app
  let T := Sheaf.terminal X.smallEtaleTopology (Types.isTerminalPUnit :
    IsTerminal PUnit.{u + 2})
  let hT := Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit
  let q : G ⟶ T := hT.from G
  have : PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (Type (u + 1))) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (constantSheaf (ProEt.topology X) (Type (u + 1))) := by
    unfold constantSheaf
    infer_instance
  have hCE : IsTerminal
      ((constantSheaf X.smallEtaleTopology (Type (u + 1))).obj PUnit.{u + 2}) :=
    Types.isTerminalPUnit.isTerminalObj _
  have hCP : IsTerminal
      ((constantSheaf (ProEt.topology X) (Type (u + 1))).obj PUnit.{u + 2}) :=
    Types.isTerminalPUnit.isTerminalObj _
  have hLT : IsTerminal (L.obj T) := hCP.ofIso
    (L.mapIso (hT.uniqueUpToIso hCE) ≪≫ (comparisonConstantIso X).app PUnit).symm
  have hep : Epi (L.map q) := epi_of_cover_sections (ProEt.topology X) (L.map q) hLT hU
    (fun i ↦ (hs i).map (e.hom.hom.app (op (U i))))
  have : Epi q := ⟨fun a b hab ↦ by
    apply L.map_injective
    apply (cancel_epi (L.map q)).mp
    simpa only [← L.map_comp] using congrArg L.map hab⟩
  have hlocal : Presheaf.IsLocallySurjective X.smallEtaleTopology q.hom :=
    (Sheaf.isLocallySurjective_iff_epi q).mpr inferInstance
  refine ⟨(Σ W : X.Etale, G.obj.obj (op W)), Sigma.fst, ?_, ?_⟩
  · intro W
    apply X.smallEtaleTopology.superset_covering _
      (Presheaf.imageSieve_mem X.smallEtaleTopology q.hom
        (show T.obj.obj (op W) from PUnit.unit))
    rintro V f ⟨s, _⟩
    exact ⟨⟨V, s⟩, ⟨𝟙 V⟩⟩
  · intro i
    exact ⟨e.inv.hom.app (op ((toProEt X).obj i.1))
      (((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).unit.app G).hom.app
        (op i.1) i.2)⟩

/-- Local classicality implies classicality, including for locally constant sheaves.
Local inhabitedness of such a sheaf can be witnessed by an etale cover. There is no
compatibility condition on the local sections, nor a nonemptiness condition on the
index sets or the constant value sets.

Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.4 and Proposition 6.8.4(6)
(auxiliary; not a blueprint node).

Proof:
1. The affine section formula makes the comparison unit invertible. Continuity on
   affine ind-etale presentations makes the counit invertible, by testing it on the
   dense affine subsite and comparing the section colimits. Local classicality
   gives this continuity by the finite-cover equalizer argument isolated in
   `proEtale_locallyClassical_continuity`. The inverse counit presents F as classical.
2. Compose the constant-sheaf adjunction on the etale site with the comparison
   adjunction. Its right adjoint is evaluation at the identity pro-etale object.
   Uniqueness of left adjoints identifies the two constant-sheaf constructions.
   Transport each local trivialization and apply the first conclusion.
3. Write F as the inverse image of G. The given local sections make the map from
   this inverse image to the inverse image of the terminal etale sheaf an epi.
   The latter object is terminal by the constant-sheaf comparison. Full faithfulness
   makes comparison faithful, hence reflects epimorphisms. Thus G maps epimorphically
   to the terminal etale sheaf. Epimorphisms of sheaves of sets are locally surjective;
   the family of all etale objects equipped with a section of G therefore covers.
   The comparison unit transports these sections to F. This argument also handles
   empty schemes, empty covering families, and empty constant value sets. -/
theorem proEtale_locallyClassical_etaleCover (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1))) :
    (IsProEtaleLocallyClassical X F → IsProEtaleClassical X F) ∧
    (IsProEtaleLocallyConstant X F →
      IsProEtaleLocallyClassical X F ∧ IsProEtaleClassical X F) ∧
    (IsProEtaleLocallyClassical X F →
      (∃ (I : Type (u + 1)) (U : I → X.ProEt),
        (ProEt.topology X).CoversTop U ∧ ∀ i : I, Nonempty (F.obj.obj (op (U i)))) →
      ∃ (I : Type (u + 1)) (Y : I → X.Etale),
        X.smallEtaleTopology.CoversTop Y ∧
          ∀ i : I, Nonempty (F.obj.obj (op ((toProEt X).obj (Y i))))) := by
  have hclass : IsProEtaleLocallyClassical X F → IsProEtaleClassical X F := by
    rintro ⟨I, U, hU, hF⟩
    have hcont := proEtale_locallyClassical_continuity X F I U hU hF
    have := proEtaleComparisonCounitSets_isIso_of_continuous X F hcont
    exact ⟨_, ⟨(asIso
      ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).counit.app F)).symm⟩⟩
  refine ⟨hclass, ?_, ?_⟩
  · intro h
    have hlocal := locallyConstant_locallyClassical X F h
    exact ⟨hlocal, hclass hlocal⟩
  · intro h hsec
    exact etale_cover_sections_of_classical X F (hclass h) hsec

end AlgebraicGeometry.Scheme
