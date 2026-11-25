/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Algebra-module quasi-coherence from exact scalar restriction

Source: Stacks Project, Tags 0BV0, 0BV1 and 0AX2.
-/

@[expose] public section

universe u w wA

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A bounded-below algebra-derived object whose underlying object has quasi-coherent
cohomology belongs to the bounded-below quasi-coherent algebra-derived category.
Source: Stacks Project, Tags 0BV0, 0BV1 and 0AX2.
(blueprint: lem-sc-derived-algebra-qcoh-of-underlying).

Proof: Restriction of scalars is exact and does not change underlying abelian sheaves,
so it commutes with cohomology and reflects zero objects. Thus vanishing of the
underlying cohomology below a bound implies vanishing of algebra cohomology below
the same bound. The isomorphism between restricted algebra cohomology and underlying
cohomology transports quasi-coherence in each degree. These are exactly the two
clauses of sheafAlgebraDerivedQCohProperty. This works for zero algebras and empty
schemes and does not use any pseudo-coherence assumption. -/
theorem derivedAlgebraQCohOfUnderlying (Y : Scheme.{u})
    (A : Y.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj A.right))]
    (E : sheafAlgebraDerivedCategory Y A hA)
    (hq : schemeDerivedQCohProperty Y
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj E))
    (hb : ∃ a : ℤ,
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map A.hom)).mapDerivedCategory.obj E).IsGE a) :
    sheafAlgebraDerivedQCohProperty Y A hA E := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map A.hom)
  let p := DerivedCategory.Q.objPreimage E
  let ep := DerivedCategory.Q.objObjPreimageIso E
  have eh (n : ℤ) : F.obj ((DerivedCategory.homologyFunctor _ n).obj E) ≅
      (DerivedCategory.homologyFunctor _ n).obj (F.mapDerivedCategory.obj E) :=
    F.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso ep.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app p) ≪≫
    ((p.sc n).mapHomologyIso F).symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).symm.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj p) ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      (F.mapDerivedCategoryFactors.symm.app p ≪≫ F.mapDerivedCategory.mapIso ep)
  obtain ⟨a, ha⟩ := hb
  constructor
  · refine ⟨a, ?_⟩
    intro n hn
    have hz := ((DerivedCategory.isGE_iff _ a).mp ha n hn).of_iso (eh n)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    have h := (IsZero.iff_id_eq_zero _).mp hz
    exact congrArg (fun f ↦ (f.val.app U).hom x) h
  · intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      (eh n).symm (hq n)

end AlgebraicGeometry
