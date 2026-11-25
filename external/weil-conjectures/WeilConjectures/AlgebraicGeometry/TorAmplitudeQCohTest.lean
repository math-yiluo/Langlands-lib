/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.AffineQCohTorAmplitudeDetection
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal

/-! # Testing Tor amplitude on quasi-coherent modules

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.6,
Tag 08EA, implication (2) implies (1) (blueprint: lem-pc-tor-amplitude-qcoh-test).
-/

@[expose] public section

universe uT wT u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Quasi-coherent test modules detect the Tor amplitude of an object with
quasi-coherent cohomology on a quasi-separated scheme.
Source: Stacks Project, Tag 08EA (blueprint: lem-pc-tor-amplitude-qcoh-test).

Proof:
1. For an affine open `j : U → X`, quasi-separatedness makes `j` quasi-compact
   and separated. Pushforward preserves quasi-coherence (`pqf-lem-pushforward-qcoh`),
   and `j* j_* G = G`, so all quasi-coherent modules on `U` extend to `X`.
   Restriction is exact and commutes with derived tensor
   (`lem-pc-affine-derived-pullback-tensor-tilde`), so the assumed vanishing holds
   on `U` against every quasi-coherent module there.
   Exact restriction preserves quasi-coherence of the cohomology sheaves, so
   `E|U` lies in `D_QCoh(O_U)`.
2. Write `U = Spec A`. The affine derived equivalence
   (`lem-pc-affine-qcoh-derived-equivalence`) represents `E|U` by an A-module complex.
   The tensor/tilde comparison (`lem-pc-affine-derived-pullback-tensor-tilde`)
   and exactness and faithfulness of tilde give Tor amplitude `[a,b]` for that complex.
   The affine criterion (`lem-pc-affine-tor-amplitude-criterion`) gives vanishing
   against every O_U-module.
3. For any O_X-module, restriction of its derived tensor with `E` to every affine
   open has cohomology zero outside `[a,b]`. Restriction commutes with derived tensor
   by `lem-pc-affine-derived-pullback-tensor-tilde`. A sheaf zero on an affine open
   cover is zero, proving the required global vanishing. -/
theorem torAmplitude_of_quasiCoherent_tests (X : Scheme.{uT}) [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ F : SheafOfModules.{uT} (moduleRings X.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes X E F i) :
    ∀ G : SheafOfModules.{uT} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by
  classical
  let : ∀ U : X.Opens, HasDerivedCategory
      (SheafOfModules.{uT} (moduleRings U.toScheme.toRingedSpace)) :=
    fun U ↦ HasDerivedCategory.standard _
  have local_tests (U : X.Opens) (hU : IsAffineOpen U) :
      let R := SheafOfModules.overFunctor.{uT} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{uT} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)
      ∀ (G : SheafOfModules.{uT} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
        i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes U.toScheme
          (R.mapDerivedCategory.obj E) G i := by
    let R := SheafOfModules.overFunctor.{uT} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uT} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    have : IsAffine U.toScheme := hU
    have hqc : schemeDerivedQCohProperty U.toScheme (R.mapDerivedCategory.obj E) :=
      (schemeDerivedQCoh_openRestriction_iff X U E).2 (fun n ↦ by
        have := hE n
        exact SheafOfModules.isQuasicoherent_over ((DerivedCategory.homologyFunctor
          (SheafOfModules.{uT} (moduleRings X.toRingedSpace)) n).obj E) U)
    apply affineQCoh_torAmplitude_detection U.toScheme _ hqc a b hab
    intro F hF i hi
    have := hF
    let J := Scheme.Modules.pushforward U.ι
    have hJ : (J.obj F).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated U.ι F
    have hz := (tensor_vanishes_iff X E (J.obj F) i).1 (h _ hJ i hi)
    have hzR := R.map_isZero hz
    have hzD := hzR.of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso i).app
        (E ⊗ (DerivedCategory.singleFunctor _ 0).obj (J.obj F))).symm
    obtain ⟨cmp⟩ := derivedTensor_openRestriction_iso_universes X U
      E ((DerivedCategory.singleFunctor _ 0).obj (J.obj F))
    let counit : R.obj (J.obj F) ≅ F :=
      (Scheme.Modules.overFunctorEquiv U).app (J.obj F) ≪≫
        asIso ((Scheme.Modules.restrictAdjunction U.ι).counit.app F)
    let singleIso := (R.mapDerivedCategorySingleFunctor 0).app (J.obj F) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso counit
    exact (tensor_vanishes_iff U.toScheme _ F i).2
      (hzD.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
        (cmp ≪≫ tensorIso (Iso.refl _) singleIso)).symm)
  intro G i hi
  apply (tensor_vanishes_iff X E G i).2
  apply Scheme.Modules.isZero_of_iSup_eq_top _
    (fun U : X.affineOpens ↦ (U : X.Opens)) (iSup_affineOpens_eq_top X)
  intro U
  let R := SheafOfModules.overFunctor.{uT} (moduleRings X.toRingedSpace) U.1 ⋙
    Equivalence.functor
      (C := SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U.1))
      (D := SheafOfModules.{uT} (moduleRings U.1.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U.1)
  have hz := (tensor_vanishes_iff U.1.toScheme
    (R.mapDerivedCategory.obj E) (R.obj G) i).1 (local_tests U.1 U.2 (R.obj G) i hi)
  obtain ⟨cmp⟩ := derivedTensor_openRestriction_iso_universes X U.1
    E ((DerivedCategory.singleFunctor _ 0).obj G)
  have hzD := hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    (cmp ≪≫ tensorIso (Iso.refl _) ((R.mapDerivedCategorySingleFunctor 0).app G)))
  have hzR := hzD.of_iso ((R.mapDerivedCategoryHomologyFunctorIso i).app
    (E ⊗ (DerivedCategory.singleFunctor _ 0).obj G))
  exact hzR.of_iso ((Scheme.Modules.overFunctorEquiv U.1).app
    ((DerivedCategory.homologyFunctor _ i).obj
      (E ⊗ (DerivedCategory.singleFunctor _ 0).obj G))).symm

end AlgebraicGeometry
