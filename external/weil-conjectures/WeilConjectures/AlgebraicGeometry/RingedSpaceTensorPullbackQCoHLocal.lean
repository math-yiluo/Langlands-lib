/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackPresentation
import Mathlib.CategoryTheory.Sites.Spaces

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.RingedSpace

/-- Local quasi-coherence of tensor pullback.
Source: Stacks Project, Modules, Tag 01BG, Lemma 17.10.4.
The proof chooses affine-style presentation neighbourhoods and transports them through
inverse image and extension of scalars; this is the local step of the standard proof.
(blueprint: lem-pc-ringed-space-tensor-pullback-qcoh-local) -/
theorem tensorModulePullback_isQuasicoherent_local
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (G : SheafOfModules.{u} (moduleRings Y)) (hG : G.IsQuasicoherent) (x : X) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ((SheafOfModules.changeOfRings.{u, u, u}
        (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).over U).IsQuasicoherent := by
  obtain ⟨q⟩ := hG.nonempty_quasicoherentData
  have hcov := (Opens.coversTop_iff Y q.X).mp q.coversTop
  obtain ⟨i, hi⟩ := hcov.exists_mem (g.hom.base x)
  obtain ⟨p⟩ := tensorModulePullback_presentation_over g G (q.X i) (q.presentation i)
  exact ⟨(TopologicalSpace.Opens.map g.hom.base).obj (q.X i), hi,
    p.isQuasicoherent⟩

end AlgebraicGeometry.RingedSpace
