/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Zero
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

set_option linter.privateModule false

/-! # Rank-zero projective bundles

The sole normalized coordinate is a global free generator on each frame open.

## References

* Stacks Project, Tag 01OE
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

end AlgebraicGeometry
