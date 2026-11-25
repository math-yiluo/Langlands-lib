/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedGlobalSectionsAffinizationComparison
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux

/-! # Derived global sections preserves quasi-coherent coproducts. -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Derived global sections takes an ambient coproduct of quasi-coherent complexes
on a qcqs scheme to a coproduct in the derived module category.
Source: Stacks Project, Tag 09M1, first paragraph of the proof.
(blueprint: lem-pc-derived-global-sections-preserves-coproducts)
Proof: Put A = Γ(X,O_X), Y = Spec A, and a = X.toSpecΓ. Since X is qcqs,
a is quasi-compact and quasi-separated. Quasi-coherent cohomology is closed
under ambient coproducts, so the given apex S is quasi-coherent. Derived
pushforward preserves the given coproduct and takes its summands and apex
into D_QCoh(Y). The fully faithful inclusion reflects its colimit property,
giving a colimiting cofan in D_QCoh(Y). The inverse of the affine derived
equivalence preserves this coproduct; its natural comparison identifies the
mapped cofan with derived global sections on Y, transported along ΓSpecIso.
The affinization comparison identifies that composite with RΓ(X,-).
Transporting the colimit across this natural isomorphism gives exactly the
maps RΓ(X,ι_i) appearing in the conclusion. The argument includes the empty
family and unbounded complexes; it needs no restriction to integer scalars. -/
theorem derivedGlobalSections_preserves_coproducts (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let G := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
    ∀ (I : Type u) (E : I → schemeDerivedQCohCategory X)
      (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S),
      IsColimit (Cofan.mk S ι) →
      Nonempty (IsColimit (Cofan.mk (G.obj S) (fun i ↦ G.map (ι i)))) := by
  classical
  let A := Γ(X, ⊤)
  let Y := Spec A
  let : HasDerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u} A) :=
    inferInstanceAs (HasDerivedCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))
  let G := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
  let H := (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).rightDerivedFunctor
  let F := schemeDerivedDirectImage X.toSpecΓ
  obtain ⟨e, _, ⟨he⟩, _, _⟩ := exists_affineQCohDerivedEquivalence A
  obtain ⟨hG⟩ := derivedGlobalSections_affinization_comparison X
  dsimp only
  intro I E S ι hc
  have : (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts X I
  have hS : schemeDerivedQCohProperty X S :=
    (schemeDerivedQCohProperty X).prop_of_isColimit hc (fun i ↦ (E i.as).property)
  have hFE (i : I) : schemeDerivedQCohProperty Y (F.obj (E i).obj) :=
    schemeDerivedDirectImage_preserves_QCoh X.toSpecΓ _ (E i).property
  have hFS : schemeDerivedQCohProperty Y (F.obj S) :=
    schemeDerivedDirectImage_preserves_QCoh X.toSpecΓ _ hS
  let E' : I → schemeDerivedQCohCategory Y := fun i ↦ ⟨F.obj (E i).obj, hFE i⟩
  let S' : schemeDerivedQCohCategory Y := ⟨F.obj S, hFS⟩
  let c : Cofan E' := Cofan.mk S' (fun i ↦ ObjectProperty.homMk (F.map (ι i)))
  have : PreservesColimit (Discrete.functor (fun i ↦ (E i).obj)) F :=
    derivedDirectImagePreservesDirectSums X.toSpecΓ I E
  have hFc : IsColimit (Cofan.mk (F.obj S) (fun i ↦ F.map (ι i))) :=
    Cofan.isColimitMapCoconeEquiv F _ _ (isColimitOfPreserves F hc)
  have hc' : IsColimit c :=
    isColimitOfReflects (schemeDerivedQCohProperty Y).ι
      ((Cofan.isColimitMapCoconeEquiv (schemeDerivedQCohProperty Y).ι E' c).symm hFc)
  have hHc : IsColimit
      (Cofan.mk (H.obj (F.obj S)) (fun i ↦ H.map (F.map (ι i)))) :=
    Cofan.isColimitMapCoconeEquiv ((schemeDerivedQCohProperty Y).ι ⋙ H) E' c
      (IsColimit.mapCoconeEquiv he (isColimitOfPreserves e.inverse hc'))
  have hcomp : IsColimit ((F ⋙ H).mapCocone (Cofan.mk S ι)) :=
    (Cofan.isColimitMapCoconeEquiv (F ⋙ H) _ _).symm hHc
  exact ⟨Cofan.isColimitMapCoconeEquiv G _ _
    (IsColimit.mapCoconeEquiv hG.symm hcomp)⟩

end AlgebraicGeometry
