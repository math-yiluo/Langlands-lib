/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCohDegree

/-! # Quasi-coherent cohomology of pseudo-coherent complexes

Source: Stacks Project, Derived Categories of Schemes, Tag 08E5 (lemma-pseudo-coherent),
invoked in the first sentence of the proof of Tag 08EE
(blueprint: lem-sc-pseudo-coherent-qcoh).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every pseudo-coherent object of `D(𝒪_Y)` has quasi-coherent cohomology in every degree.
Source: Stacks Project, Tag 08E5 (lemma-pseudo-coherent), invoked in the proof of Tag 08EE
(blueprint: lem-sc-pseudo-coherent-qcoh).

Proof: By `def-pur-pseudo-coherent-complex`, each point has an open neighbourhood on which
`E` is represented by a bounded-above complex of finite free modules. Its cohomology sheaves
identify with the restrictions of those of `E`. The terms are quasi-coherent by
`pqf-def-coherent`: on an affine open they are associated to finite free modules. The kernel
of each differential is quasi-coherent by `lem-weil-pbc-quasi-coherent-module-kernel`.
Its quotient by the preceding differential's image is quasi-coherent by
`lem-weil-pbc-quasi-coherent-module-cokernel-image`; this quotient is the cohomology sheaf.
Quasi-coherence is local by `pqf-def-coherent`, so every cohomology sheaf of `E` is
quasi-coherent. This is membership in `D_QCoh(𝒪_Y)` by
`lemma-coherent-base-change-invertible-sheaves`. -/
theorem schemeDerivedQCohProperty_of_isPseudoCoherent (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) (hE : IsPseudoCoherent Y E) :
    schemeDerivedQCohProperty Y E := by
  intro n
  exact schemeDerivedQCohProperty_of_isPseudoCoherent_degree Y E hE n

end AlgebraicGeometry.Scheme
