/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.Strict.StrictPerfectStalkFiberData
import WeilConjectures.AlgebraicGeometry.BoundedFreeStalkModelSpread
import WeilConjectures.RingTheory.MinimalFreeModel

/-! # Existence of minimal finite free models near a point

## References

* Stacks Project, More on Algebra, Tags 0BCD, 0BCC, 0BC7
* Stacks Project, Derived Categories of Schemes, Tags 08EB and 09RE
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- If `E` is strictly perfect near `x` with finite and bounded residue fibre cohomology, then
on an affine neighbourhood of `x` it is represented by a bounded complex of finite free modules
whose ranks are the fibre Betti numbers at `x`. -/
theorem finiteFreeModel_of_fiberData
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    (hfin : ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x))
    (hbound : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin (derivedFiberBetti X E i x))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj K) := by
  let R := X.presheaf.stalk x
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let G := DerivedCategory.Q.objPreimage E
  let eG : DerivedCategory.Q.obj G ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let C := ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj G
  obtain ⟨hC, hfinite, hd⟩ := strictPerfect_stalk_fiberData X E x G eG hlocal hfin
  obtain ⟨a, b, hbounds⟩ := hbound
  have hup : ∃ b : ℤ, ∀ i : ℤ, b < i → derivedFiberBetti X E i x = 0 :=
    ⟨b, fun i hi => hbounds i (Or.inr hi)⟩
  obtain ⟨F, _, ⟨eF⟩, hfree, _⟩ :=
    DerivedCategory.exists_unique_minimalFreeModel.{u, 0, u + 1}
      (DerivedCategory.Q.obj C) hC (fun i => derivedFiberBetti X E i x) hfinite hd hup
  have hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i) := by
    refine ⟨a, b, ?_⟩
    intro i hi
    obtain ⟨ei⟩ := hfree i
    rw [hbounds i hi] at ei
    exact (ModuleCat.isZero_of_subsingleton _).of_iso ei
  exact spread_boundedFree_stalkModel X E x G eG hlocal
    (fun i => derivedFiberBetti X E i x) F hbounded hfree eF

end
end AlgebraicGeometry.Scheme
