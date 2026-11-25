/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Quasi-coherent closure for the canonical derived tensor

Source: Stacks Project, perfect.tex, Tag 08DX.
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The canonical derived tensor preserves quasi-coherent cohomology.
Source: Stacks Project, perfect.tex, Tag 08DX
(blueprint: lem-pc-canonical-derived-tensor-qcoh).
Proof: choose a K-flat resolution P of E and a complex N representing F. The canonical
K-flat derived tensor is isomorphic to Q(Tot(P tensor N)). Apply the second clause of
`derivedPullback_tensor_preserve_QCoh` with the identity morphism of X. Transport its
quasi-coherence conclusion along the canonical tensor comparison isomorphism, using
that homology functors preserve isomorphisms and quasi-coherence is invariant under
isomorphism of sheaves. This argument works for unbounded E and F and the zero objects. -/
theorem canonical_derivedTensor_preserve_QCoh (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E F : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) (hF : schemeDerivedQCohProperty X F) :
    schemeDerivedQCohProperty X (E ⊗ F) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let Q := DerivedCategory.Q (C := C)
  let M := Q.objPreimage E
  let N := Q.objPreimage F
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolution M
  have : QuasiIso f := hf
  let eP : Q.obj P ≅ E := asIso (Q.map f) ≪≫ Q.objObjPreimageIso E
  let eN : Q.obj N ≅ F := Q.objObjPreimageIso F
  have hQP : schemeDerivedQCohProperty X (Q.obj P) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor C n).mapIso eP.symm) (hE n)
  have hNQ : schemeDerivedQCohProperty X (Q.obj N) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor C n).mapIso eN.symm) (hF n)
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  let eTensor : E ⊗ F ≅
      Q.obj (CochainComplex.mapBifunctor P N (curriedTensor C)) :=
    (tensorIso eP eN).symm ≪≫ (e.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  have h := (derivedPullback_tensor_preserve_QCoh (X := X) (Y := X) (𝟙 X)).2
    P N hP hQP hNQ
  intro n
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor C n).mapIso eTensor.symm) (h n)

end AlgebraicGeometry
