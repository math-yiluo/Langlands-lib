/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherent
import WeilConjectures.AlgebraicGeometry.DerivedLocallyBoundedBelowGlobal
import WeilConjectures.AlgebraicGeometry.DerivedAlgebraQCohOfUnderlying
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Derived internal Hom from a pseudo-coherent algebra

Source: Stacks Project, Tag 0A6H (1), and Tags 0BV0, 0BV1, 0AX2
(blueprint: lem-sc-pseudo-coherent-rhom-qcoherent).
-/

@[expose] public section

universe u w wA

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- On a Noetherian scheme, derived internal Hom from a quasi-coherent algebra that is
pseudo-coherent as an underlying module takes bounded-below quasi-coherent objects to
bounded-below quasi-coherent algebra-module objects. Forgetting the algebra action gives
an object of the bounded-below quasi-coherent derived category of the scheme.

Source: Stacks Project, Tag 0A6H (1), and Tags 0BV0, 0BV1, 0AX2
(blueprint: lem-sc-pseudo-coherent-rhom-qcoherent).

Proof:
1. By def-pur-pseudo-coherent-complex, choose affine neighbourhoods with bounded-above
   finite-free models for A. Noetherian schemes are quasi-compact, so finitely many suffice.
   By lem-sc-derived-internal-hom-restrict-open, internal Hom restricts to these models.
   By lem-sc-derived-open-restriction-adjunction-exact, K retains its lower bound.
2. Matrices of maps of finite-free sheaves come from the affine coordinate ring by
   lem-weil-pbc-spec-module-tilde-sections. By lem-pc-affine-qcoh-derived-equivalence,
   represent K on each affine by a bounded-below module-derived object. Apply
   lem-sc-affine-pseudo-coherent-rhom-qcoherent to obtain quasi-coherent cohomology and a
   lower bound there. Quasi-coherence is local; take the minimum of the finitely many
   lower bounds to get a global bound.
3. The first argument's algebra action gives def-pc-derived-rhom-algebra-module. By
   def-pc-derived-category-qcoh-algebra, quasi-coherence means quasi-coherence after
   restriction of scalars, which is exact. Thus both asserted memberships follow. -/
theorem pseudoCoherentRHomQuasiCoherent
    (Y : Scheme.{u}) [IsNoetherian Y]
    (A : Y.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj A.right))]
    (hpc : Scheme.IsPseudoCoherent Y (DerivedCategory.Q.obj
      ((HomologicalComplex.single (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (ComplexShape.up ℤ) 0).obj A.toModule)))
    (K : schemeDerivedCategory Y)
    (hK : schemeDerivedQCohProperty Y K) (hbounded : ∃ a : ℤ, K.IsGE a) :
    sheafAlgebraDerivedQCohProperty Y A hA ((derivedRHomAlgebraModule Y A hA).obj K) ∧
    schemeDerivedQCohProperty Y
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)) ∧
    ∃ a : ℤ,
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)).IsGE a := by
  let S := DerivedCategory.Q.obj
    ((HomologicalComplex.single (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (ComplexShape.up ℤ) 0).obj A.toModule)
  obtain ⟨hq, hlocal⟩ := (rhom_supported_quasiCoherent Y S K hK).1 hpc hbounded
  obtain ⟨e⟩ := derivedRHomAlgebraModule_underlying Y A hA
  let eK := e.app K
  have hq' : schemeDerivedQCohProperty Y
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso eK.symm) (hq n)
  obtain ⟨a, ha⟩ := derivedLocallyBoundedBelowGlobal Y _ hlocal
  have hb : ∃ a : ℤ,
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj
            ((derivedRHomAlgebraModule Y A hA).obj K)).IsGE a := by
    refine ⟨a, (DerivedCategory.isGE_iff _ a).mpr ?_⟩
    intro n hn
    exact ((DerivedCategory.isGE_iff _ a).mp ha n hn).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso eK)
  exact ⟨derivedAlgebraQCohOfUnderlying Y A hA _ hq' hb, hq', hb⟩

end AlgebraicGeometry
