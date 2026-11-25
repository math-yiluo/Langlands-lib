/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-! # Descent of the scalar tensor comparison from K-flat representatives.

Source: Stacks Project, Tags 06YS, 07A4 and Categories 04VK.
(blueprint: lem-sf-ringed-finite-free-tensor-data). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- The strong scalar tensor comparison and its representative normalization.
The universal scalar pair and both normalized closed models are already supplied;
this assertion constructs only the chain comparison and its derived localization.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-data).

Proof: use the actual chain scalar tensor comparison and preservation of K-flatness.
K-flat resolutions make restriction of two-variable functors to K-flat representatives
fully faithful. Compose the inverse R tensor representative comparison, the universal
scalar counit on the tensor, the chain comparison, the S tensor representative
comparison and the inverse scalar counits on the two factors. The existing tensor
descent theorem lifts this natural isomorphism uniquely to the derived categories and
proves its displayed square. The counit on the tensor is invertible because the tensor
of two K-flat complexes is K-flat. The chain generator formula is retained unchanged. -/
theorem ringedFiniteFreeHomBaseChange_tensor
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (AR : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS) :
    ∃ (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          D.E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (D.E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (D.E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ D.T ≅ D.T.prod D.T ⋙ AS.tensor),
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)) ∧
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
            D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom) := by
  obtain ⟨κ, hκ, hF⟩ := ringedFiniteFreeHomBaseChange_complex.{c, v, r, w} J φ D
  let A := SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)
  let B := SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J S)
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X),
        HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  set_option backward.isDefEq.respectTransparency true in
    have hff := resolvingRepresentativesFullyFaithfulWhiskering
      (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
      (D := DerivedCategory A) (DerivedCategory B)
      (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
      (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  obtain ⟨ff⟩ := hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  set_option backward.isDefEq.respectTransparency true in
    have hdes := tensorComparisonDescent
      (K := CochainComplex A ℤ) (H := CochainComplex B ℤ)
      (D := DerivedCategory A) (E := DerivedCategory B)
      DerivedCategory.Q DerivedCategory.Q (D.E.mapHomologicalComplex (.up ℤ)) D.T D.ε
      PR PS hF ff' (WeilConjectures.coefficientTotalTensor.{r, c, v} J R)
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J S) AR.tensor AS.tensor
      MR.comparison MS.comparison κ D.computes
      (fun P Q hP hQ ↦ D.computes _
        (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ))
  obtain ⟨μ, hμ, _⟩ := hdes
  refine ⟨κ, μ, hκ, ?_⟩
  intro P Q hP hQ
  exact ⟨hF P hP, hF Q hQ, hμ P Q hP hQ⟩

end Site
end CategoryTheory
