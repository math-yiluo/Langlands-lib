/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTensorNaturality
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Open restriction of total tensor complexes

Source: Stacks Project, Tag 08DX, proof of (1).
(blueprint: lem-pc-open-restriction-total-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The recorded sheaf tensor, used for total complexes. Source: Stacks, Tag 06Y7
(blueprint: lem-pc-open-restriction-total-tensor). -/
noncomputable local instance openRestrictionTotalTensorTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Restriction commutes with the signed direct-sum total tensor of arbitrary complexes.
Source: Stacks Project, Tag 08DX, proof of (1); Tag 01CD for the sheaf tensor comparison.
Proof: the restriction tensor comparison identifies the tensor of restricted terms
with restriction of the tensor in every bidegree. It is natural in both terms:
the comparison on pure tensors commutes with restriction of either module map.
Restriction preserves arbitrary coproducts, so summing these comparisons over
p + q = n gives an isomorphism in each total degree n. Naturality intertwines
both differentials; additivity intertwines the sign (-1)^p in the second one.
The degreewise isomorphisms and their inverses thus define inverse complex maps.
The over equivalence transports the same calculation to modules on U.toScheme.
No boundedness is used; the empty open and zero complexes give the zero comparison.
(blueprint: lem-pc-open-restriction-total-tensor). -/
theorem openRestriction_totalTensor_iso (X : Scheme.{u}) (U : X.Opens)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let R :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    Nonempty
      ((R.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P N
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))) ≅
        CochainComplex.mapBifunctor
          ((R.mapHomologicalComplex (.up ℤ)).obj P)
          ((R.mapHomologicalComplex (.up ℤ)).obj N)
          (curriedTensor (SheafOfModules.{u}
            (moduleRings U.toScheme.toRingedSpace)))) := by
  let R :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
  have : PreservesColimitsOfSize.{0, 0} R := by
    dsimp [R, SheafOfModules.overFunctor]
    infer_instance
  let K := (((curriedTensor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj P).obj N
  have : R.PreservesTotalComplex K (.up ℤ) := fun _ => inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso R K (.up ℤ)).symm
  obtain ⟨e, he⟩ := exists_openRestriction_tensor_natural X U
  let e₂ :
      (((R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj K) ≅
        (((curriedTensor (SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace))).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
              ((R.mapHomologicalComplex (.up ℤ)).obj N) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (P.X p) (N.X q))
        (by
          intro q q' hq
          change (e (P.X p) (N.X q)).hom ≫ R.obj (P.X p) ◁ R.map (N.d q q') =
            R.map (P.X p ◁ N.d q q') ≫ (e (P.X p) (N.X q')).hom
          simpa [R] using (he (P.X p) (P.X p) (N.X q) (N.X q') (𝟙 _) (N.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (P.X p) (N.X q)).hom ≫ R.map (P.d p p') ▷ R.obj (N.X q) =
          R.map (P.d p p' ▷ N.X q) ≫ (e (P.X p') (N.X q)).hom
        simpa [R] using (he (P.X p) (P.X p') (N.X q) (N.X q) (P.d p p') (𝟙 _)).symm)
  exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩

end AlgebraicGeometry
