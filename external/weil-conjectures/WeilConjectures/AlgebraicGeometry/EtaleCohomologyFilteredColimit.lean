/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleFilteredInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor

/-!
# Filtered colimits of etale cohomology

Source: Stacks Project, Tags 03Q5, 0739 and 03FD; blueprint
`sec-curve-estimates/lem-sc-second-kummer-divisors` (blueprint:
lemma-finiteness-small-etale-topoi--2).

The image cocone has legs induced by the original coprojections. Its colimit property
expresses that the canonical comparison map is an isomorphism, rather than merely asserting
an unspecified isomorphism between the two cohomology objects.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def cohomologySingleIsoRightDerived (Y : Scheme.{u}) (q : ℕ) :
    DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ) ≅
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q := by
  let Γ := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  exact Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0)
      (Functor.isoWhiskerRight Γ.rightDerivedFunctorPlusCompatibility.symm H) ≪≫
    Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q

private theorem abelianSectionsColimit (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) :
    Nonempty (IsColimit ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapCocone c)) := by
  let R := ULift.{u + 1} ℤ
  let U := ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := U.asEquivalence
  let S := sheafCompose Y.smallEtaleTopology U
  have : S.EssSurj := ⟨fun P ↦ by
    let Q := (sheafCompose Y.smallEtaleTopology e.inverse).obj P
    refine ⟨Q, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      (Functor.isoWhiskerLeft P.obj e.counitIso)⟩
  have : S.IsEquivalence := {}
  let T := S.asEquivalence.inverse
  let G := F ⋙ T
  let d := T.mapCocone c
  have hd : IsColimit d := isColimitOfPreserves T hc
  let V : Y.Etale := Etale.mk (𝟙 Y)
  have : CompactSpace V.left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace V.left := inferInstanceAs (QuasiSeparatedSpace Y)
  let E := (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (Opposite.op V)
  have hbij := AlgebraicGeometry.etale_sections_filtered_colimit Y R V I G d hd
  have hE : IsColimit (E.mapCocone d) := by
    exact (colimit.isColimit (G ⋙ E)).ofPointIso (t := E.mapCocone d)
      (i := (ConcreteCategory.isIso_iff_bijective _).2 hbij)
  let Eab := (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (Opposite.op V)
  have hEU := isColimitOfPreserves U hE
  change IsColimit ((T ⋙ S ⋙ Eab).mapCocone c) at hEU
  have hAb := IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerRight S.asEquivalence.counitIso Eab) hEU
  have hV : IsTerminal V := MorphismProperty.Over.mkIdTerminal @Etale Y
  exact ⟨IsColimit.mapCoconeEquiv
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1} hV).symm hAb⟩

/-- On a quasi-compact quasi-separated scheme, etale cohomology of abelian sheaves commutes
with filtered colimits, with no torsion hypothesis. Source: Stacks Tags 03Q5 and 0739
(blueprint: lemma-finiteness-small-etale-topoi--2).

Proof:
1. Sections on the terminal identity étale object commute with filtered colimits by
   lemma-finiteness-small-etale-topoi--2. Use modules over the lifted integers
   and the integer-module/abelian-group equivalence to match its coefficient universe.
   Transfer the colimit through the induced sheaf equivalence and identify evaluation
   at the terminal object with global sections.
2. The natural isomorphism `Γ.rightDerivedZeroIsoSelf` gives the degree-zero case.
   Sheaves and abelian groups have exact filtered colimits by their Mathlib AB5 instances;
   shrink these instances to the index universe.
3. Induct on the degree using lemma-finiteness-small-etale-topoi--2.
   Its proof embeds the diagram functorially into injectives, uses its cokernel and
   the horseshoe delta-functor to construct two right-exact rows, and compares them
   by naturality of the connecting maps and the four lemma.
4. Supply the successor step's vanishing hypothesis using
   lemma-finiteness-small-etale-topoi--2: on qcqs finite coverings the Čech
   complex of a filtered colimit of injectives is the colimit of their complexes,
   hence has zero positive cohomology; the Čech criterion gives derived acyclicity.
5. The source library's plus-derived compatibility and single-functor homology
   isomorphism identify classical derived global sections with the precise unbounded
   cohomology functor below. Transport the image cocone along this natural isomorphism.
   All its legs remain induced by the original coprojections. No torsion is used. -/
theorem etaleCohomology_isColimit_of_isFiltered (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).mapCocone c)) :=
  by
    let Γ := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    have : HasFilteredColimitsOfSize.{u, u}
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
    have : AB5OfSize.{u, u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
      hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
    have hpres (n : ℕ) : PreservesColimitsOfShape I (Γ.rightDerived n) := by
      induction n with
      | zero =>
        have hΓ : PreservesColimitsOfShape I Γ :=
          ⟨fun {G} ↦ ⟨fun {d} hd ↦ abelianSectionsColimit Y hd⟩⟩
        exact preservesColimitsOfShape_of_natIso Γ.rightDerivedZeroIsoSelf.symm
      | succ n ih =>
        have := ih
        exact Γ.preservesColimitsOfShape_rightDerived_succ I n
          (fun J hJ ↦ isZero_rightDerived_globalSections_colimit_of_injective Y I J hJ n)
    have := hpres q
    exact ⟨IsColimit.mapCoconeEquiv (cohomologySingleIsoRightDerived Y q).symm
      (isColimitOfPreserves (Γ.rightDerived q) hc)⟩

/-- The same canonical comparison is an isomorphism for etale sheaves of modules over a
fixed constant commutative ring. Source: Stacks Tags 03FD, 03CO and 03Q5
(blueprint: lemma-finiteness-small-etale-topoi--2).

Proof (step 8 of the node): the underlying sheaf functor is a left adjoint by
restriction/coextension of coefficient scalars and the sheafification adjunction;
it therefore preserves the input colimit. Apply the abelian theorem to this diagram.
The natural comparison lem-weil-pbc-etale-module-cohomology-forget is proved by exact
forgetful functors, underlying injective acyclicity, and the source library's derived
base-change comparison. Transport the abelian cohomology cocone along this comparison.
The coefficient forgetful functor preserves colimits and reflects isomorphisms, hence
reflects colimits. Applying that reflection gives precisely the module image cocone. -/
theorem etaleModuleCohomology_isColimit_of_isFiltered (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] (Λ : Type (u + 1)) [CommRing Λ]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)).mapCocone c)) :=
  by
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let S := sheafCompose Y.smallEtaleTopology U
    have : S.IsLeftAdjoint := moduleSheafForgetIsLeftAdjoint Y Λ
    have : ReflectsColimitsOfShape I U := reflectsColimitsOfShape_of_reflectsIsomorphisms
    let H := DerivedCategory.singleFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      Etale.cohomology (ModuleCat.{u + 1} Λ) Y (q : ℤ)
    obtain ⟨e⟩ := nonempty_etaleModuleCohomology_forgetIso Y Λ q
    have hAb := (etaleCohomology_isColimit_of_isFiltered Y
      (isColimitOfPreserves S hc) q).some
    have hU : IsColimit ((H ⋙ U).mapCocone c) :=
      IsColimit.mapCoconeEquiv e.symm hAb
    exact ⟨isColimitOfReflects U hU⟩


end AlgebraicGeometry.Scheme
