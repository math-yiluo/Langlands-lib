/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral
import WeilConjectures.AlgebraicGeometry.AffineAlgebraTensorPullbackExact
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoh
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Quasi-coherence in the affine algebra derived adjunction

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof
(blueprint: lem-sc-affine-algebra-derived-adjunction-qcoh).
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Every left adjoint to the canonical affine algebra derived direct image preserves
quasi-coherent cohomology.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof
(blueprint: lem-sc-affine-algebra-derived-adjunction-qcoh).

Proof: Use the ringed-space derived adjunction to obtain the concrete tensor
pullback P and its left-derived functor D. The affine stalk calculation
(affine_algebra_tensorModulePullback_exact) makes P exact on all module sheaves.
Consequently P.mapDerivedCategory is also a left-derived functor, with its
invertible localization comparison. Uniqueness of left-derived functors gives
D isomorphic to P.mapDerivedCategory. Uniqueness of left adjoints identifies
the given L with D. The exact-functor homology comparison identifies every
H^n(P.mapDerivedCategory M) with P(H^n(M)), without boundedness. Tensor
pullback preserves quasi-coherence by the local free-presentation argument
of Stacks 01BG (tensorModulePullback_isQuasicoherent). Apply it to H^n(M),
then transport along the homology comparison and the isomorphism from L. -/
theorem affine_algebra_derived_pullback_preserves_qcoh
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)) :
    (∀ M : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))),
      directImageAlgebraDerivedQCohProperty f M →
        schemeDerivedQCohProperty X (L.obj M)) := by
  obtain ⟨P, h, hm, hP, D, ε, hD, _, ⟨adjD⟩⟩ :=
    RingedSpace.derivedModulePullback_adjunction (toDirectImageAlgebraSpace f)
  let := hP
  obtain ⟨hlim, hcolim⟩ := affine_algebra_tensorModulePullback_exact f P h hm
  let := hlim
  let := hcolim
  let := hD
  have hPD : P.mapDerivedCategory.IsLeftDerivedFunctor
      P.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))
        (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ P.mapDerivedCategoryFactorsh
  let := hPD
  let eD : D ≅ P.mapDerivedCategory :=
    Functor.leftDerivedUnique P.mapDerivedCategory D ε
      P.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))
        (ComplexShape.up ℤ))
  let e : L ≅ P.mapDerivedCategory := adj.leftAdjointUniq adjD ≪≫ eD
  intro M hM n
  have hq : (P.obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))
        n).obj M)).IsQuasicoherent := by
    rw [h]
    exact RingedSpace.tensorModulePullback_isQuasicoherent
      (toDirectImageAlgebraSpace f) _ (hM n)
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    (((P.mapDerivedCategoryHomologyFunctorIso n).app M) ≪≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings X.toRingedSpace)) n).mapIso
          ((e.app M).symm)) hq

end AlgebraicGeometry
