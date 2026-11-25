/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.LocalStrictPerfectStalkProjectiveModel
import WeilConjectures.AlgebraicGeometry.AbelianVariety.StalkFreeResidueCohomologyComparison
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Finite residue fibre cohomology of a strictly perfect neighbourhood

## References

* Stacks Project, More on Algebra, Tag 0BCD
* Stacks Project, Cohomology of Sheaves, Tag 08C4 (strictly perfect complexes)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A strictly perfect neighbourhood has finite residue-field fibre cohomology in every degree. -/
theorem finiteFiberCohomology
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
          DerivedCategory.Q.obj P)) :
    ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  let G := DerivedCategory.Q.objPreimage E
  let eG : DerivedCategory.Q.obj G ≅ E := DerivedCategory.Q.objObjPreimageIso E
  obtain ⟨L, a, b, hbound, hterms, ⟨eL⟩⟩ :=
    exists_localStrictPerfect_stalk_projective_model X E x G eG hlocal
  have hb : L.IsStrictlyLE b := (L.isStrictlyLE_iff b).2
    (fun j hj ↦ hbound j (Or.inr hj))
  have hfree (j : ℤ) : Module.Free (X.presheaf.stalk x) (L.X j) := by
    have := (hterms j).1
    have := (hterms j).2
    exact Module.free_of_flat_of_isLocalRing
  let K := ((ModuleCat.extendScalars
    (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  intro i
  have hfinite : Module.Finite (X.residueField x) (K.X i) := by
    have := (hterms i).1
    change Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
      ((ModuleCat.extendScalars (IsLocalRing.residue (X.presheaf.stalk x))).obj (L.X i))
    let := (IsLocalRing.residue (X.presheaf.stalk x)).toAlgebra
    change Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (TensorProduct (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) (L.X i))
    infer_instance
  have := hfinite
  have hhom : Module.Finite (X.residueField x) (K.homology i) := by
    let S := K.sc i
    have : Module.Finite (X.residueField x) S.moduleCatLeftHomologyData.H := by
      change Module.Finite (X.residueField x)
        (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
      have : Module.Finite (X.residueField x) S.X₂ := hfinite
      infer_instance
    exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm
  obtain ⟨e⟩ := nonempty_stalkFree_residueCohomology_linearEquiv
    X E x G eG L b hb hfree eL i
  exact Module.Finite.equiv e.symm

end
end AlgebraicGeometry.Scheme
