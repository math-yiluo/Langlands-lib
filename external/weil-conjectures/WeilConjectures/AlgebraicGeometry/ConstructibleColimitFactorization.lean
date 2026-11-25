/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Factorization from constructible sheaves into filtered colimits

Source: Stacks Project, Tag 09Z4, the surjectivity assertion for module sheaves.
(blueprint: lem-weil-pbc-constructible-large-colimit-factorization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Cardinal.fact_isRegular_aleph0

private noncomputable def affineFreeHomEquiv
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) ≃
      F.obj.obj (Opposite.op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _).trans
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans uliftYonedaEquiv)

private theorem affineFreeHomEquiv_comp
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) (f : F ⟶ H) :
    affineFreeHomEquiv W H (p ≫ f) = f.hom.app (Opposite.op W) (affineFreeHomEquiv W F p) := by
  simp only [affineFreeHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def affineFreeCoyonedaIso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] (W : X.Etale) :
    coyoneda.obj (Opposite.op ((presheafToSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ))) ≅
      (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (Opposite.op W) ⋙
        CategoryTheory.forget (ModuleCat.{u + 1} Λ) :=
  NatIso.ofComponents (fun F ↦ (affineFreeHomEquiv W F).toIso) (by
    intro F H f
    ext p
    exact affineFreeHomEquiv_comp W p f)

private theorem affineFree_finitelyPresentable
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) [IsAffine W.left] :
    IsFinitelyPresentable.{u + 1}
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)) := by
  let E := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (Opposite.op W)
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} E := by
    refine ⟨fun I _ _ ↦ ⟨fun {D} ↦ ?_⟩⟩
    have : IsIso ((colimit.isColimit (D ⋙ E)).desc (E.mapCocone (colimit.cocone D))) :=
      (ConcreteCategory.isIso_iff_bijective _).2
      (etale_sections_filtered_colimit X Λ W I D (colimit.cocone D) (colimit.isColimit D))
    exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
      ((colimit.isColimit (D ⋙ E)).ofPointIso)
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  refine ⟨fun I _ _ ↦ ?_⟩
  exact preservesColimitsOfShape_of_natIso (affineFreeCoyonedaIso W).symm

/-- Maps from constructible module sheaves into filtered colimits factor through a stage,
including indexing categories in the coefficient universe.

Source: Stacks Project, Tag 09Z4 (lemma-constructible-is-compact), module-sheaf case.
(blueprint: lem-weil-pbc-constructible-large-colimit-factorization).

Proof: A constructible sheaf has a finite presentation by sums of extensions by zero of
rank-one constant modules on affine etale objects (Tag 095N). Hom from each such free
sheaf is evaluation on its affine etale object, by the free-Yoneda and sheafification
adjunctions. Evaluation on a quasi-compact quasi-separated etale object commutes with
filtered colimits (Sites Tag 0738, using Etale Cohomology Tag 03Q4). Hom from the
presented sheaf is therefore the equalizer of the two Hom maps from the finite presentation.
Filtered colimits of sets commute
with finite limits, so Hom from the presented sheaf commutes with filtered colimits.
Every element of a filtered colimit of sets is represented at one stage, yielding the
asserted factorization. These arguments apply to a small category in universe u+1:
the site is essentially small there and the module values and morphisms live there.
An empty scheme or the zero sheaf gives the zero map; filteredness still supplies an
index. No constructibility assumption is made on the diagram objects. -/
theorem exists_constructible_hom_of_isColimit
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf G)
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {c : Cocone D} (hc : IsColimit c) (p : G ⟶ c.pt) :
    ∃ (a : A) (q : G ⟶ D.obj a), q ≫ c.ι.app a = p := by
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W ↦
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  obtain ⟨n, m, U, V, hU, hV, f, g, w, ⟨hg⟩⟩ :=
    exists_affine_free_etale_presentation X Λ G hG
  have hfree (W : X.Etale) (hW : IsAffine W.left) : IsFinitelyPresentable.{u + 1} (P W) := by
    have := hW
    exact affineFree_finitelyPresentable W
  have hsum (k : ℕ) (W : Fin k → X.Etale) (hW : ∀ i, IsAffine (W i).left) :
      IsFinitelyPresentable.{u + 1} (∐ fun i ↦ P (W i)) := by
    have (i : Discrete (Fin k)) : IsFinitelyPresentable.{u + 1}
        ((Discrete.functor (fun i ↦ P (W i))).obj i) := hfree (W i.as) (hW i.as)
    exact isCardinalPresentable_of_isColimit _
      (colimit.isColimit (Discrete.functor (fun i ↦ P (W i)))) Cardinal.aleph0.{u + 1}
      ((hasCardinalLT_aleph0_iff _).2 inferInstance)
  have (i : WalkingParallelPair) : IsFinitelyPresentable.{u + 1} ((parallelPair f 0).obj i) := by
    cases i
    · exact hsum m V hV
    · exact hsum n U hU
  have : IsFinitelyPresentable.{u + 1} G :=
    isCardinalPresentable_of_isColimit _ hg Cardinal.aleph0.{u + 1}
      ((hasCardinalLT_aleph0_iff _).2 inferInstance)
  exact IsFinitelyPresentable.exists_hom_of_isColimit hc p

end AlgebraicGeometry.Scheme
