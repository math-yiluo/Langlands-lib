/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport

/-!
# Transport of finite constant-model stratification witnesses

Source: blueprint main-20261015, sec-six-functors/sk-lem-sf-open-ctf/
sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(blueprint: lem-sf-constant-model-stratification-transport).

The adapters keep all partition and immersion data. The transport statements fix the
cover and scalar modules before changing the module being modelled. Constructibility
and bounded constructible cohomology use the finite constant-model convention.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale
