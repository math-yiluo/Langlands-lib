/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-! # Ordinary scalar coordinates for an integral constant model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient

/-- A finitely presented internal scalar module gives an ordinary finitely presented
integral scalar model on a scheme.

Source: blueprint latest, ctf-equals-bc, Local models, first two sentences; Stacks Tag 093J.
(blueprint: lem-sfb-integral-scalar-model-coordinates).

Proof: write Q as the cokernel of a finite matrix over the scalar ring. The regular-module
universal property rewrites its entries as scalar sections. The constant realization sends
this matrix to the corresponding scalar matrix over the coefficient sheaf on T. The same
matrix over the continuous coefficient ring at the profinite point has finitely presented
cokernel. The existing continuousScalarFinitePresentation theorem realizes that cokernel
as the continuous extension of an ordinary finitely presented module P. Pull it to T.
Preservation of finite biproducts and cokernels identifies both resulting scalar matrices,
so their cokernels are isomorphic. This includes zero ranks and the empty scheme. No
quotient, derived reduction, cohomology calculation or flatness assumption is involved. -/
theorem integral_scalar_model_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u})
    (Q : Mod Ab.{u + 1} (scalarRingObj (DerivedNakayama.integerRing l E)))
    (hQ : Mod.IsFinitelyPresented (scalarRingObj (DerivedNakayama.integerRing l E)) Q) :
    ∃ P : ModuleCat.{u + 1} (A l E), Module.FinitePresentation (A l E) P ∧
      Nonempty ((finiteConstantScalarExtension (DerivedNakayama.integerRing l E) T).obj Q ≅
        model l E T P) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let Λ := DerivedNakayama.integerRing l E
  let F := (upperStarFromPoint T).mapMod Λ
  obtain ⟨n, m, d, ⟨ed⟩⟩ := hQ
  let entries (j : Fin m) (k : Fin n) : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ :=
    (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
      (biproduct.ι _ j ≫ d ≫ biproduct.π _ k).hom
  let ds := biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular (scalarRingObj Λ)) (entries j k)
  have hds : ds = d := scalarMatrix_reconstruct Λ d
  let dp := biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (entries j k))
  have hfp : Mod.IsFinitelyPresented Λ (cokernel dp) := ⟨n, m, dp, ⟨Iso.refl _⟩⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    (continuousScalarFinitePresentation (A l E) (cokernel dp)).mp hfp
  refine ⟨P, hP, ⟨?_⟩⟩
  let G := finiteConstantScalarExtension Λ T
  have eQ : Q ≅ cokernel ds := by rw [hds]; exact ed
  have e₁ : G.obj Q ≅ cokernel (scalarMatrix Λ T entries) :=
    G.mapIso eQ ≪≫ PreservesCokernel.iso G ds ≪≫
      cokernel.mapIso (G.map ds) (scalarMatrix Λ T entries)
        (scalarFreeIso Λ T m) (scalarFreeIso Λ T n) (by
          rw [← scalarMatrix_map]
          simp only [G, ds, Iso.hom_inv_id_assoc])
  have e₂ : cokernel (scalarMatrix Λ T entries) ≅ F.obj (cokernel dp) :=
    (cokernel.mapIso (F.map dp) (scalarMatrix Λ T entries)
      (pointFreeIso Λ T m) (pointFreeIso Λ T n) (by
        rw [← pointMatrix_map]
        simp only [dp, F, Iso.hom_inv_id_assoc])).symm ≪≫
      (PreservesCokernel.iso F dp).symm
  exact e₁ ≪≫ e₂ ≪≫ F.mapIso eP

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
