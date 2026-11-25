/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ExtEvaluation
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import WeilConjectures.AlgebraicGeometry.HomComplexSingle
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Derived internal Hom from a finite locally free sheaf

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, Lemma 20.50.5,
specialized to a finite locally free module in degree zero
(blueprint: lem-sc-finite-locally-free-derived-hom).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- For a finite locally free `P`, derived internal Hom from `P[0]` to `L[0]` is
ordinary sheaf Hom in degree zero. In particular its positive cohomology sheaves
(the higher sheaf Exts) vanish. The finite rank may vary over the open cover.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ (the case `K = P[0]`)
(blueprint: lem-sc-finite-locally-free-derived-hom).

Proof:
1. On a trivializing cover the dual of `P` is finite free. By
   `lem-sc-ext-tensor-exact`, tensoring with this dual is exact, and
   `lem-sc-ext-evaluation` identifies it naturally with sheaf Hom from `P`
   (`def-pur-sheaf-hom`). Thus `T = Hom(P,-)` is exact.
2. By `def-pur-derived-internal-hom`, a K-injective resolution `L[0] → I`
   computes derived Hom as the Hom complex from `P[0]` to `I`, namely `T(I)`.
   Exactness of `T` identifies its degree-`n` cohomology with `T(H^n(I))`:
   this is `Hom(P,L)` for `n = 0` and zero otherwise. In particular all
   positive sheaf Exts vanish. The truncation quasi-isomorphisms identify this
   complex in `D(O_Y)` (`lemma-coherent-base-change-invertible-sheaves`) with `Hom(P,L)[0]`. -/
theorem finiteLocallyFree_derivedInternalHom_single
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P L : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} P] :
    Nonempty
      ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf) P L)) ∧
    ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
            (op ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P),
              (DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L))) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Pc := (CochainComplex.singleFunctor A 0).obj P
  let Lc := (CochainComplex.singleFunctor A 0).obj L
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  have : QuasiIso (η.app Lc) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A Lc).2
  have : (I.obj Lc).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A Lc
  obtain ⟨e⟩ := derivedInternalHom_obj_iso
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    ((DerivedCategory.singleFunctor A 0).obj P)
    ((DerivedCategory.singleFunctor A 0).obj L) Pc (I.obj Lc)
    (Iso.refl _)
    ((asIso (DerivedCategory.Q.map (η.app Lc))).symm)
  let Pd : Y.Modules := Scheme.Modules.dual P
  have : Pd.IsFiniteLocallyFree := Scheme.Modules.IsFiniteLocallyFree.dual P
  obtain ⟨ev, _, hn⟩ := Scheme.Modules.dual_tensor_hom_iso Y P
  let t : CategoryTheory.MonoidalCategory.tensorLeft Pd ≅
      (SheafOfModules.homFunctor Y.sheaf).obj (op P) :=
    NatIso.ofComponents ev (fun g ↦ (hn g).symm)
  obtain ⟨hl, hc⟩ := Scheme.Modules.finiteLocallyFree_tensorLeft_exact Pd
  have := hl
  have := hc
  have : PreservesFiniteLimits ((SheafOfModules.homFunctor Y.sheaf).obj (op P)) :=
    preservesFiniteLimits_of_natIso t
  have : PreservesFiniteColimits ((SheafOfModules.homFunctor Y.sheaf).obj (op P)) :=
    preservesFiniteColimits_of_natIso t
  let T := (SheafOfModules.homFunctor Y.sheaf).obj (op P)
  obtain ⟨h⟩ := homComplex_single_iso Y P (I.obj Lc)
  let f := (T.mapHomologicalComplex (ComplexShape.up ℤ)).map (η.app Lc)
  have : QuasiIso f := inferInstance
  let s := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).app L
  let d := e ≪≫ DerivedCategory.Q.mapIso h ≪≫
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.mapIso s
  refine ⟨⟨d⟩, ?_⟩
  intro i hi
  exact (DerivedCategory.isZero_of_isLE
    ((DerivedCategory.singleFunctor A 0).obj
      (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf) P L)) 0 i hi).of_iso
    ((DerivedCategory.homologyFunctor A i).mapIso d)

end AlgebraicGeometry
