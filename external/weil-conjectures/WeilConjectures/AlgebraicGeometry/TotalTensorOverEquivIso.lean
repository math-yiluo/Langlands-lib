/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.AlgebraicGeometry.LocalizedOpenTensorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Total tensor comparison for the open-site equivalence

Source: Stacks Project, Tags 06YN and 08DJ, ordinary tensor totalization;
Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-total-tensor-over-equiv-iso). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private noncomputable local instance totalTensorSchemeTensor (X : Scheme.{u}) :
    MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf

noncomputable local instance totalTensorOverPreadditive (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

noncomputable local instance totalTensorSchemePreadditive (X : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} X.ringCatSheaf) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1

/-- The degreewise open-site equivalence commutes with the actual total tensor.
Source: Stacks Project, Tags 06YN and 08DJ; Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-total-tensor-over-equiv-iso).

Proof: use `exists_localizedOpen_tensor_equivalence` for the natural comparison
L(A tensor B) -> L(A) tensor L(B) on sheaves. Apply it in each bidegree of the
bicomplex. Its naturality with the identity on the first factor identifies the
vertical differential, and naturality with the identity on the second identifies
the horizontal differential. Form the bicomplex isomorphism by two applications
of `HomologicalComplex.Hom.isoOfComponents`. The equivalence is additive and
preserves coproducts, so `HomologicalComplex₂.mapTotalIso` identifies the image
of the total complex with the total of the image bicomplex. Compose its inverse
with `HomologicalComplex₂.total.mapIso` of the bicomplex comparison. Totalization
handles the signed vertical differential. There is no boundedness assumption:
all coproducts in each total degree are preserved by the equivalence. Zero
complexes, zero rings and the empty open use the same construction. -/
theorem exists_totalTensor_overEquiv_iso (X : Scheme.{u}) (U : X.Opens)
    (A K : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := SheafOfModules.{u} (X.ringCatSheaf.over U))
      (D := SheafOfModules.{u} U.toScheme.ringCatSheaf)
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    Nonempty (T.obj (CochainComplex.mapBifunctor A K (curriedTensor _)) ≅
      CochainComplex.mapBifunctor (T.obj A) (T.obj K) (curriedTensor _)) := by
  let R := (Scheme.Modules.overEquiv U).functor
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesColimitsOfSize.{0, 0} R := by
    dsimp [R]
    infer_instance
  let B := (((curriedTensor
    (localEvaluationModules X U)).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj A).obj K
  have : R.PreservesTotalComplex B (.up ℤ) := fun _ ↦ inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso R B (.up ℤ)).symm
  obtain ⟨e, he⟩ := exists_localizedOpen_tensor_equivalence X U
  let e₂ :
      (((R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj B) ≅
        (((curriedTensor (SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace))).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj A)).obj
              ((R.mapHomologicalComplex (.up ℤ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (A.X p) (K.X q))
        (by
          intro q q' hq
          change (e (A.X p) (K.X q)).hom ≫ R.obj (A.X p) ◁ R.map (K.d q q') =
            R.map (A.X p ◁ K.d q q') ≫ (e (A.X p) (K.X q')).hom
          simpa [R] using (he (A.X p) (A.X p) (K.X q) (K.X q') (𝟙 _) (K.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (A.X p) (K.X q)).hom ≫ R.map (A.d p p') ▷ R.obj (K.X q) =
          R.map (A.d p p' ▷ K.X q) ≫ (e (A.X p') (K.X q)).hom
        simpa [R] using (he (A.X p) (A.X p') (K.X q) (K.X q) (A.d p p') (𝟙 _)).symm)
  exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩


end AlgebraicGeometry
