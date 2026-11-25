/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentSupportPart

/-! # Quasi-coherence and support of derived internal Hom

Source: Stacks Project, Derived Categories of Schemes, Tag 0A6H (1), (2),
and the support observation in the proof of Tag 0A9C
(blueprint: lem-sc-rhom-supported-qcoherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Derived internal Hom from a pseudo-coherent source into a bounded-below quasi-coherent
object is quasi-coherent and locally bounded below; from a perfect source into an arbitrary
quasi-coherent object it is quasi-coherent. In both cases it preserves support on a closed
subset in the second variable. Local boundedness means that each point has a neighbourhood
on which all cohomology sheaves below some integer vanish. Support means that every
cohomology sheaf restricts to zero on the open complement.

Source: Stacks Project, Tag 0A6H (1), (2), and Tag 0A9C, proof
(blueprint: lem-sc-rhom-supported-qcoherent).

Proof:
1. By def-pur-pseudo-coherent-complex, locally choose a bounded-above finite-free model
   of K and shrink to an affine open. By lem-pc-affine-qcoh-derived-equivalence represent
   L there by a module complex. Exactness and faithfulness of associated sheaves transfer
   its cohomological lower bound. By lem-sc-derived-internal-hom-restrict-open and
   lem-sc-affine-pseudo-coherent-rhom-qcoherent the restricted internal Hom has
   quasi-coherent cohomology vanishing below a bound.
2. A perfect K has quasi-coherent cohomology, since its local strictly perfect models have
   quasi-coherent terms. By lem-pc-perfect-rhom-tensor-comparison its dual is perfect and
   quasi-coherent, and RHom(K,L) is the derived tensor of L with that dual. By
   lem-pc-derived-pullback-tensor-qcoh this tensor has quasi-coherent cohomology.
3. If L is supported on T, its restriction to the complement is zero in the derived
   category. By lem-sc-derived-internal-hom-restrict-open the restriction of RHom(K,L)
   is RHom of the restricted objects, hence zero. Its cohomology restricts to zero.
4. Quasi-coherence is local, so the affine conclusions give quasi-coherence globally.
   The neighbourhood bounds from step 1 give exactly local boundedness, without claiming
   a uniform lower bound on a non-quasi-compact scheme. Step 3 gives support in both cases. -/
theorem rhom_supported_quasiCoherent
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hL : schemeDerivedQCohProperty X L) :
    (Scheme.IsPseudoCoherent X K → (∃ a : ℤ, L.IsGE a) →
      schemeDerivedQCohProperty X
        ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K, L)) ∧
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
        IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
              ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
                X.toRingedSpace.sheaf).obj (op K, L))))) ∧
    (Scheme.IsPerfect X K → schemeDerivedQCohProperty X
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L))) ∧
    ∀ (T : Set X) (hT : IsClosed T),
      ((Scheme.IsPseudoCoherent X K ∧ ∃ a : ℤ, L.IsGE a) ∨ Scheme.IsPerfect X K) →
      (∀ n : ℤ,
        IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
          ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj L))) →
      ∀ n : ℤ,
        IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
          ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
              ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
                X.toRingedSpace.sheaf).obj (op K, L)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hpc hge
    exact rhom_supported_quasiCoherent_pseudo_part X K L hL hpc hge
  · intro hp
    exact rhom_supported_quasiCoherent_perfect_part X K L hL hp
  · intro T hT _hcase hzero n
    exact rhom_supported_quasiCoherent_support_part X K L T hT hzero n

end AlgebraicGeometry
