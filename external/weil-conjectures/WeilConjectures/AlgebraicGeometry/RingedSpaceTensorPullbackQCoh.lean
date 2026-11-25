/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoHLocal

/-! # Quasi-coherence of tensor pullback on ringed spaces

Source: Stacks Project, Modules, Tag 01BG
(blueprint: lem-pc-ringed-space-tensor-pullback-qcoh).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/-- Tensor pullback along any morphism of ringed spaces preserves quasi-coherence.
Source: Stacks Project, Modules, Tag 01BG, Lemma 17.10.4
(blueprint: lem-pc-ringed-space-tensor-pullback-qcoh).

Proof: Near each point of Y choose a presentation of G as the cokernel of a map
between free module sheaves. Restrict to the inverse-image open in X. Inverse
image and extension of scalars are left adjoints and hence preserve coproducts
and cokernels. Their composite takes the free module on a set over O_Y to the
free module on the same set over O_X: on pure tensors the identification is
b tensor a maps to b times g-sharp(a), with inverse b maps to b tensor 1.
Applying this composite to the presentation therefore gives a presentation of
the displayed tensor pullback by free O_X-modules. The inverse-image opens
cover X, so these presentations supply quasicoherent data everywhere. This
argument imposes no flatness or finite-presentation assumption. -/
theorem tensorModulePullback_isQuasicoherent
    {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    (G : SheafOfModules.{u} (moduleRings Y)) (hG : G.IsQuasicoherent) :
    (SheafOfModules.changeOfRings.{u, u, u}
      (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
      (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)).IsQuasicoherent := by
  classical
  let M := SheafOfModules.changeOfRings.{u, u, u}
    (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
    (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf G)
  choose U hU hQU using fun x ↦ tensorModulePullback_isQuasicoherent_local g G hG x
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hcov

end AlgebraicGeometry.RingedSpace
