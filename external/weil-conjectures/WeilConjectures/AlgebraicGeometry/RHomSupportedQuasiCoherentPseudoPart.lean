/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartQC
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBound

/-! # PseudoPart of derived internal Hom

Source: Stacks Project, Tag 0A6H
(blueprint: lem-sc-rhom-supported-qcoherent-pseudo-part).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Pseudo-coherent internal Hom is quasi-coherent and locally bounded below.

Source: Stacks Project, Tag 0A6H (1)
(blueprint: lem-sc-rhom-supported-qcoherent-pseudo-part).

Proof: Choose a neighbourhood of each point on which K has a bounded-above finite-free
representative, and shrink it to an affine open. The matrices of the differentials give a
bounded-above finite-free module complex. Use the affine quasi-coherent derived equivalence
to represent L there by a module complex. Exact restriction and exact, faithful tilde
transfer the cohomological lower bound of L to that complex. The affine pseudo-coherent
RHom calculation gives quasi-coherent cohomology and a lower bound for the internal Hom:
if the source vanishes above b and the target below a, its Hom complex vanishes below a-b.
The restriction isomorphism identifies this calculation with restriction of RHom(K,L).
Quasi-coherence glues over the affine cover. The individual bounds give the claimed
neighbourhood bound at each point; no finite cover or uniform global bound is required. -/
theorem rhom_supported_quasiCoherent_pseudo_part
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L)
    (hK : Scheme.IsPseudoCoherent X K) (hGE : ∃ a : ℤ, L.IsGE a) :
    schemeDerivedQCohProperty X
        ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K, L)) ∧
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
        IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
              ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
                X.toRingedSpace.sheaf).obj (op K, L)))) := by
  exact ⟨rhom_supported_quasiCoherent_pseudo_part_qc X K L hL hK hGE,
    rhom_supported_quasiCoherent_pseudo_part_bound X K L hL hK hGE⟩

end AlgebraicGeometry
