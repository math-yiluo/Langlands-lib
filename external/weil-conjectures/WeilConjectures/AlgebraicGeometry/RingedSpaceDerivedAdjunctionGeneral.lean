/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlatPullback
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Derived pullback/direct-image adjunction for ringed spaces

Source: Stacks Project, Cohomology, Tag 079W, Lemma cohomology-lemma-adjoint,
with Tag 06YJ, Lemma cohomology-lemma-derived-base-change
(blueprint: lem-pc-ringed-spaces-derived-adjoint-general).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The total left derived tensor pullback is left adjoint to derived direct image.
The additive functor `P` is specified on both objects and morphisms as inverse image
followed by extension of scalars along the adjoint structure map. Its total left
derived functor `L`, with comparison `ε`, is computed on K-flat complexes.
The adjunction includes its natural bifunctorial Hom equivalences.
Source: Stacks Project, Cohomology, Tags 06YJ and 079W
(blueprint: lem-pc-ringed-spaces-derived-adjoint-general).

Proof, following the three steps of the node:
1. Let `ρ : g⁻¹ OY ⟶ OX` be the map adjoint to `g`'s structure-sheaf map.
Compose the inverse-image/direct-image module adjunction
(lem-pc-module-inverse-image-adjunction, Tags 008X/008Y) with the extension/restriction
of scalars adjunction along `ρ` (lem-pc-module-change-of-rings-adjunction, Tag 008A).
This identifies tensor pullback with the left adjoint of `moduleDirectImage g`;
the latter has sections `F(g⁻¹ V)` with the scalar action through `g`'s structure map.
2. Resolve each source complex by a K-flat complex (lem-pc-kflat-resolution).
Exact inverse image preserves the resolution quasi-isomorphism. Its inverse image
is K-flat over the inverse-image ring, by lem-pc-kflat-pullback-preservation applied
to `(g,id)`. Apply lem-pur-derived-change-of-rings along `ρ` to compute `L` by
termwise tensor pullback on this resolution, with comparison `ε` invertible there.
The functor `derivedModuleDirectImage g` is computed on K-injective resolutions
(def-pc-ringed-spaces-derived-direct-image, def-pur-kinjective-complex,
prop-pur-kinjective-resolutions-exist). Apply lem-sc-derived-adjunction-from-underived
to the underived adjunction and these derived comparison maps. It yields the
adjunction and the counit induced by the underived counit.
3. The resulting adjunction's `homEquiv` gives
`Hom(L E,F) ≃ Hom(E,Rg_* F)`, natural in both arguments. Substitution of the
specified tensor-pullback construction gives exactly the displayed node formula. -/
theorem derivedModulePullback_adjunction
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y) :
    ∃ (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
      (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
        P.obj M = SheafOfModules.changeOfRings.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
      (_ : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
        P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
          (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
          eqToHom (h N).symm)
      (_ : P.Additive),
      ∃ (L : DerivedCategory (SheafOfModules.{u} (moduleRings Y)) ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings X)))
        (ε : DerivedCategory.Qh ⋙ L ⟶
          P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
        L.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
            (ComplexShape.up ℤ)) ∧
        (∀ K : CochainComplex (SheafOfModules.{u} (moduleRings Y)) ℤ,
          K.IsKFlatTensor → IsIso
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
        Nonempty (L ⊣ derivedModuleDirectImage g) := by
  obtain ⟨P, h, hm, hP, ⟨adj⟩⟩ := exists_tensorModulePullback g
  let := hP
  obtain ⟨L, ε, hL, hK, hcomp⟩ :=
    exists_absolute_leftDerived_tensorModulePullback g P h hm
  let := hL
  let := hcomp (derivedModuleDirectImage g)
  let β := (moduleDirectImage g).rightDerivedFunctorUnit
  let : (derivedModuleDirectImage g ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism
      (SheafOfModules.{u} (moduleRings X)))
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
        _ (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
          _).isIso_of_isRightDerivedFunctor _ I) _
  exact ⟨P, h, hm, hP, L, ε, hL, hK,
    ⟨(adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Y))
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ)) ε β⟩⟩

end AlgebraicGeometry.RingedSpace
