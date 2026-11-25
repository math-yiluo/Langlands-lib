/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
import WeilConjectures.AlgebraicGeometry.CoherentOpenMapTensorExtension
import WeilConjectures.AlgebraicGeometry.IdealPowerTensorImageLift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Ambient ideal-power extension for a closed structure module

Source: Stacks Project, Tags 01YB, 01XZ and 01QY.
(blueprint: lem-pc-closed-structure-ambient-ideal-extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Extend a local map from a closed structure module using an ambient ideal power.
Source: Stacks Project, Tag 01YB (lemma-homs-over-open), with Tags 01QY and 01XZ.
(blueprint: lem-pc-closed-structure-ambient-ideal-extension)

Proof: Write H = i_* O_W. A closed immersion is quasi-compact and separated, so H
is quasi-coherent by the quasi-coherent pushforward theorem. On an affine open
Spec A of X its sections are A/K, with the scalar action through the quotient;
these sections are cyclic over A. The affine finite-type criterion makes H finite
type, and the locally Noetherian coherence criterion makes H coherent. The same
criterion makes G quasi-coherent. Apply Tag 01YB with coherent source H and
quasi-coherent target G. Its open complement of the ideal support equals U by hI.
Its surjectivity clause produces n and a map from I^n H agreeing with phi after
the product inclusion on all of U. The recursively formed ideal power and the
ideal-sheaf-data power have the same affine section ideals I(V)^n. Their monic
inclusions therefore identify them as subobjects of O_X, and the induced image
isomorphism identifies their products with H, preserving inclusions. Transport
through this isomorphism. Finally overFunctor followed by overEquiv is naturally
isomorphic to restrictFunctor; conjugation by this natural isomorphism gives the
stated equality. No generic point or integrality is used. At n = 0 the ideal is
the unit ideal; for U empty every local map is the unique map and n = 0 works. -/
theorem closed_structure_ambient_ideal_extension
    {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) (G : X.Modules)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (U : X.Opens) (hI : (I.support : Set X) = (U : Set X)ᶜ)
    (φ : (restrictFunctor U.ι).obj
        ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (restrictFunctor U.ι).obj G) :
    ∃ (n : ℕ) (χ : idealModuleProduct (I ^ n).toModulesι
        ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶ G),
      (restrictFunctor U.ι).map χ =
        (restrictFunctor U.ι).map (idealModuleProductι (I ^ n).toModulesι
          ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))) ≫ φ := by
  let H := (pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)
  have : (SheafOfModules.unit W.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have : (SheafOfModules.unit W.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit W.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit W.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : (SheafOfModules.unit W.ringCatSheaf).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} _
  have hH : RingedSpace.IsCoherent X.toRingedSpace H :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X H).mpr
      (isQuasicoherent_and_isFiniteType_pushforward_of_isFinite i _)
  have : G.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG).1
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨n, β, hβ⟩ := coherent_open_map_tensor_extension I H G hH U hI φ
  obtain ⟨m, a, ha⟩ := ideal_power_tensor_image_lift I H hH n
  refine ⟨n + m, a ≫ β, ?_⟩
  rw [Functor.map_comp, hβ, ← Category.assoc, ← Functor.map_comp, ha]

end AlgebraicGeometry.Scheme.Modules
