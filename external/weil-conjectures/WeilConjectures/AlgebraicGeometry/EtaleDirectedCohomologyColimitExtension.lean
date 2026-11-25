/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit


public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveColimitAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Directed colimits of derived etale cohomology at coefficient size

Source: Stacks Project, Tag 03Q5 (lemma-colimit).
(blueprint: lem-weil-pbc-etale-directed-cohomology-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem sections_isColimit (X : Scheme.{u}) (U : X.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) :
    Nonempty (IsColimit
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op U)).mapCocone c)) := by
  let J := X.smallEtaleTopology
  let G := (Functor.asEquivalence (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).inverse
  have : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} ℤ) :=
    IsGrothendieckAbelian.of_equivalence
      (Functor.asEquivalence (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).symm
  let S := sheafCompose J G
  let E := (sheafSections J (ModuleCat.{u + 1} ℤ)).obj (Opposite.op U)
  let e : Sheaf.composeAndSheafify J G ≅ S :=
    Functor.isoWhiskerLeft S (sheafificationNatIso J (ModuleCat.{u + 1} ℤ)).symm ≪≫
      Functor.rightUnitor S
  have : S.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  have hS : IsColimit (S.mapCocone c) := isColimitOfPreserves S hc
  have hb := etale_sections_filtered_colimit X ℤ U I (D ⋙ S) (S.mapCocone c) hS
  have : IsIso (colimit.desc ((D ⋙ S) ⋙ E) (E.mapCocone (S.mapCocone c))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  obtain ⟨hE⟩ :=
    (colimit.isColimit ((D ⋙ S) ⋙ E)).nonempty_isColimit_iff_isIso_desc.mpr
      (inferInstance : IsIso (colimit.desc ((D ⋙ S) ⋙ E) (E.mapCocone (S.mapCocone c))))
  exact ⟨isColimitOfReflects G hE⟩

/-- Derived etale cohomology preserves directed colimit cocones indexed in the
same universe as the abelian coefficients.
Source: Stacks Project, Tag 03Q5 (lemma-colimit), direct proof, and
Tag 0739 (lemma-colim-works-over-collection), proof.
(blueprint: lem-weil-pbc-etale-directed-cohomology-colimit)

Proof: Work simultaneously on all qcqs etale objects. Every etale cover of one
of these objects has a finite qcqs refinement whose finite fibre products are
qcqs. Sections of a directed colimit commute with evaluation on these objects:
choose representatives on the finite cover and move their finitely many matching
equalities to one upper stage. This proves the degree-zero comparison.
Embed the sheaf diagram functorially into injectives and take its cokernel
diagram. Exactness of filtered colimits gives the corresponding short exact
sequence after colimiting. For every finite qcqs cover, sections commute with
colimits, and finite products do too, so the Cech complex of the colimit of
injectives is the colimit of their Cech complexes. Their augmented complexes
are exact. Exactness of filtered abelian-group colimits therefore gives Cech
vanishing for the colimit of injectives. The Cech vanishing criterion on the
qcqs basis makes that colimit acyclic. Compare the natural long exact sequences
of the stagewise short exact sequences and of their colimit. Degree one is the
cokernel of the same map of degree-zero sections. In degree greater than one,
acyclicity identifies the comparison with the preceding-degree comparison for
the cokernel diagram. Induction simultaneously for all diagrams proves every
degree. Injective resolutions identify this cohomology naturally with the
homology of derived global sections, sending every coprojection to the displayed
functor's map. Thus the image cocone is a colimit. Only finite upper bounds are
used, so an index in universe u+1 is allowed. Identity diagrams and zero sheaves
give identity and zero colimit cocones; no torsion hypothesis is required. -/
theorem etaleCohomology_isColimit_of_isFiltered_coefficientSize
    (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).mapCocone c)) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : CompactSpace (Scheme.Etale.mk (𝟙 X)).left := ‹CompactSpace X›
  have : QuasiSeparatedSpace (Scheme.Etale.mk (𝟙 X)).left := ‹QuasiSeparatedSpace X›
  have hΓ : PreservesColimitsOfShape I Γ := by
    let e := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      ((CategoryTheory.Over.mkIdTerminal (X := X)).isTerminalOfObj
        (Scheme.Etale.forget X) (Scheme.Etale.mk (𝟙 X)))
    have : PreservesColimitsOfShape I
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (Opposite.op (Scheme.Etale.mk (𝟙 X)))) :=
      ⟨fun {D} ↦ ⟨fun {c} hc ↦ sections_isColimit X (Scheme.Etale.mk (𝟙 X)) hc⟩⟩
    exact preservesColimitsOfShape_of_natIso e.symm
  have hderived : ∀ n : ℕ, PreservesColimitsOfShape I (Γ.rightDerived n) := by
    intro n
    induction n with
    | zero =>
      exact preservesColimitsOfShape_of_natIso Γ.rightDerivedZeroIsoSelf.symm
    | succ n hn =>
      let := hn
      exact Γ.preservesColimitsOfShape_rightDerived_succ I n
        (fun J hJ ↦
          isZero_rightDerived_globalSections_colimit_of_injective_coefficientSize X hJ
            (colimit.isColimit J) (n + 1) (Nat.succ_pos n))
  let := hderived q
  let e : DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ) ≅ Γ.rightDerived q :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        Γ.rightDerivedFunctorPlusCompatibility.symm)
      (DerivedCategory.homologyFunctor AddCommGrpCat (q : ℤ)) ≪≫
        Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  exact ⟨IsColimit.mapCoconeEquiv e.symm (isColimitOfPreserves (Γ.rightDerived q) hc)⟩



end AlgebraicGeometry.Scheme
