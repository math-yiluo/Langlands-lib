/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Coherence of an ideal pushforward.
(blueprint: lem-pc-r2-coherent-pushforward-ideal)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent ideal on a closed integral subscheme has coherent pushforward.
Source: Stacks Project, Cohomology of Schemes, Tag 01YH, the paragraph beginning
"Next, suppose"; this is the coherence subargument isolated for reuse.
(blueprint: lem-pc-r2-coherent-pushforward-ideal)

Proof: A closed immersion is finite, so W is locally Noetherian. The structure
module on W is coherent. The closed immersion defined by I is finite too, and
its pushed structure module is coherent. The module I.toModules is the kernel
of the comparison from the structure module to that pushed structure module;
coherent kernel closure makes it coherent. Finite pushforward along i preserves
coherence. This also proves the result for the zero and unit ideals.
-/
theorem coherent_pushforward_ideal {X W : Scheme.{u}} [IsLocallyNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I : W.IdealSheafData) :
    RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian i
  have (T : W.IdealSheafData) : IsLocallyNoetherian T.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian T.subschemeι
  have coherent_unit (T : Scheme.{u}) [IsLocallyNoetherian T] :
      RingedSpace.IsCoherent T.toRingedSpace (SheafOfModules.unit T.ringCatSheaf) := by
    have : (SheafOfModules.unit T.ringCatSheaf).IsInvertible :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have : (SheafOfModules.unit T.ringCatSheaf).IsFiniteLocallyFree :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    have : (SheafOfModules.unit T.ringCatSheaf).IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
    exact (isCoherent_iff_isQuasicoherent_and_isFiniteType T _).mpr
      ⟨SheafOfModules.isQuasicoherent_unit.{u, u, u},
        SheafOfModules.instIsFiniteTypeOfIsFinitePresentation.{u, u, u} _⟩
  have coherent_pushforward {S T : Scheme.{u}} (f : S ⟶ T)
      [IsFinite f] [IsLocallyNoetherian T] (G : S.Modules)
      (hG : RingedSpace.IsCoherent S.toRingedSpace G) :
      RingedSpace.IsCoherent T.toRingedSpace ((pushforward f).obj G) := by
    have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian f
    obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType S G).mp hG
    have : G.IsQuasicoherent := hq
    have : G.IsFiniteType := ht
    exact (isCoherent_iff_isQuasicoherent_and_isFiniteType T _).mpr
      (isQuasicoherent_and_isFiniteType_pushforward_of_isFinite f G)
  have hunit := coherent_unit I.subscheme
  have hquot := coherent_pushforward I.subschemeι _ hunit
  have hW := coherent_unit W
  have hI := ((isCoherent_kernel_cokernel_biprod_and_submodule W).1 _ _
    hW hquot).1 I.toPushforwardSubscheme |>.1
  exact coherent_pushforward i I.toModules hI

end AlgebraicGeometry.Scheme.Modules
