/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! Generic coherent ideal lattices. Source: Stacks Project, Tag 01YE. -/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Finite coproducts of a coherent ideal module remain coherent on a Noetherian scheme.

Source: Stacks Project, Tag 01YE, the finite-sum coherence assertion. A coherent ideal is
quasi-coherent and of finite type on a locally Noetherian scheme. Finite coproducts preserve
quasi-coherence and finite type, hence are coherent by the local Noetherian criterion.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-sigma-coherent)
-/
theorem coherent_sigma_of_coherent_ideal (Z : Scheme.{w}) [IsNoetherian Z]
    (r : ℕ) (I : Z.IdealSheafData)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules) :
    RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules) := by
  classical
  have h := (isCoherent_iff_isQuasicoherent_and_isFiniteType Z I.toModules).mp hI
  have : I.toModules.IsQuasicoherent := h.1
  have : I.toModules.IsFiniteType := h.2
  let e : (∐ fun _ : ULift.{w} (Fin r) ↦ I.toModules) ≅
      (∐ fun _ : Fin r ↦ I.toModules) :=
    Sigma.reindex Equiv.ulift (fun _ : Fin r ↦ I.toModules)
  have hqcLift := isQuasicoherent_sigma (fun _ : ULift.{w} (Fin r) ↦ I.toModules)
  have hqc : (∐ fun _ : Fin r ↦ I.toModules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e hqcLift
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData I.toModules
  let Q : (∐ fun _ : Fin r ↦ I.toModules).LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i ↦
        (SheafOfModules.GeneratingSections.sigma
          (fun _ : ULift.{w} (Fin r) ↦ I.toModules.over (q.X i))
          (fun _ ↦ q.generators i)).ofEpi
          ((PreservesCoproduct.iso
            (SheafOfModules.overFunctor Z.ringCatSheaf (q.X i))
            (fun _ : ULift.{w} (Fin r) ↦ I.toModules)).inv ≫
            (SheafOfModules.overFunctor Z.ringCatSheaf (q.X i)).map e.hom) }
  have hQ : Q.IsFiniteType := by
    constructor
    intro i
    have := hq.isFiniteType i
    dsimp [Q]
    infer_instance
  have ht : (∐ fun _ : Fin r ↦ I.toModules).IsFiniteType :=
    SheafOfModules.IsFiniteType.mk (R := Z.ringCatSheaf) ⟨Q, hQ⟩
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType Z _).mpr ⟨hqc, ht⟩

end AlgebraicGeometry.Scheme.Modules
