/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedSectionPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- Sheafification of the full section cohomology presheaf computes the cohomology
sheaf of derived direct image.

Source: Stacks Project, Cohomology, Tag 0D5X (the unbounded higher-direct-image
presheaf description), with Tag 0BKJ (sheafification of cohomology)
(blueprint: new-qcoh-acyclic-sheafification-component).

Proof:
1. Resolve a complex representing E functorially by a K-injective complex I.
   Both right derived functors in the statement are computed on I: the presheaf
   complex is the underlying module presheaf of f_*I, whereas the sheaf complex
   is f_*I. Additive functors preserve homotopy equivalences, so this comparison
   is independent of the resolution and descends to the derived category.
2. The presheaf category computes kernels and cokernels on each open. Thus its
   degree-i cohomology is the quotient of sectionwise cycles by boundaries,
   with exactly the restriction maps in schemeDerivedSectionPresheaf.
3. Module sheafification is exact and its counit on a sheaf is invertible.
   It therefore sends the cycles, boundaries and their quotient in step 2 to
   the cycles, boundaries and cohomology sheaf of f_*I. The latter is
   H^i(Rf_*E), by the K-injective computation of derived direct image.
4. Exact-functor homology comparison and the counit are natural in chain maps.
   Their compatibility with homotopy and quasi-isomorphism gives a natural
   isomorphism on the derived category. Restrict it along the full inclusion
   of objects with quasi-coherent cohomology to obtain the displayed result.
   This argument does not need qcqs or hacyc, but applies under the given hypotheses. -/
theorem qcoh_acyclic_derived_sections_comparison_sheafification {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.sheafification.{u}
            (𝟙 (moduleRings Y.toRingedSpace).obj) ≅
        (schemeDerivedQCohProperty X).ι ⋙ schemeHigherDirectImage f i) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let P := PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj
  let := HasDerivedCategory.standard P
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let U := SheafOfModules.forget (moduleRings Y.toRingedSpace)
  let S := F ⋙ U
  let a := PresheafOfModules.sheafification.{u} (𝟙 (moduleRings Y.toRingedSpace).obj)
  have : a.Additive := Functor.additive_of_preserves_binary_products a
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let γ : DerivedCategory.Q ⟶ I ⋙ DerivedCategory.Q :=
    Functor.whiskerRight η DerivedCategory.Q
  have : IsIso γ := by
    have (K : CochainComplex C ℤ) : IsIso (γ.app K) := by
      have : QuasiIso (η.app K) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
      change IsIso (DerivedCategory.Q.map (η.app K))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  -- The derived unit is invertible on the chosen K-injective resolution.
  let β : S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ S.rightDerivedFunctor :=
    (Functor.isoWhiskerLeft (S.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso P)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      S.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
      S.rightDerivedFunctor).hom
  have : IsIso (Functor.whiskerLeft I β) := by
    have (K : CochainComplex C ℤ) : IsIso ((Functor.whiskerLeft I β).app K) := by
      dsimp [β]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let eS : DerivedCategory.Q ⋙ S.rightDerivedFunctor ≅
      I ⋙ S.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    asIso (Functor.whiskerRight γ S.rightDerivedFunctor) ≪≫
      (asIso (Functor.whiskerLeft I β)).symm
  -- Sheafifying the underlying presheaf of a sheaf recovers that sheaf.
  let ε : U ⋙ a ≅ 𝟭 D :=
    asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (moduleRings Y.toRingedSpace).obj)).counit
  let e : S ⋙ a ≅ F :=
    Functor.isoWhiskerLeft F ε ≪≫ F.rightUnitor
  obtain ⟨eF⟩ := RingedSpace.derivedModuleDirectImageFactorization f.toLRSHom.toShHom
  let L := S.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor P i ⋙ a
  let R := F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D i
  -- Compare on complexes, commute exact sheafification with homology, then descend.
  let eQ : DerivedCategory.Q ⋙ L ≅ DerivedCategory.Q ⋙ R :=
    Functor.isoWhiskerRight eS (DerivedCategory.homologyFunctor P i ⋙ a) ≪≫
    Functor.isoWhiskerLeft (I ⋙ S.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors P i) a) ≪≫
    Functor.isoWhiskerLeft (I ⋙ S.mapHomologicalComplex (ComplexShape.up ℤ))
      (a.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) i).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft I (Functor.mapHomologicalComplexCompIso e
        (ComplexShape.up ℤ))) (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i) ≪≫
    Functor.isoWhiskerLeft (I ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactors D i).symm ≪≫
    Functor.isoWhiskerRight eF.symm (DerivedCategory.homologyFunctor D i)
  let eD : L ≅ R :=
    (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) D).preimageIso eQ
  exact ⟨Functor.isoWhiskerLeft (schemeDerivedQCohProperty X).ι eD⟩

end AlgebraicGeometry
