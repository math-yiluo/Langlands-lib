/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Projective bundles on frame charts

## References

* Stacks Project, Tags 01OB, 01O3, 01OE
* Stacks Project, Constructions, Tags 01OB, 01OE, 01NR, 01MN and 01MS
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

/-- A symmetric-algebra projective bundle with its normalized quotient and charts for
all frames. Properness, invertibility, and base-change coherence are separate consequences. -/
structure ProjectiveBundleFrameModels (n : ℕ) where
  bundle : ∀ (B : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F), ProjectiveBundleRealization B F
  frame : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart (bundle B F hF) n U e

/-- Existence of the frame models, without the properness or coherence conclusions. -/
theorem exists_projectiveBundleFrameModels (n : ℕ) :
    Nonempty (ProjectiveBundleFrameModels.{u} n) := by
  sorry

end AlgebraicGeometry
