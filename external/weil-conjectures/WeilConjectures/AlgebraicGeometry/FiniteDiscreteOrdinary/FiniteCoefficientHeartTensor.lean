/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Pure tensor normalization of the coefficient heart functor

Source: the finite coefficient transport paragraph, and the normalized internal/section,
ring-isomorphism, and constant-scalar tensor comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

private theorem monoidal_with_tensor
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (t : ∀ X Y, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (z : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ X X' Y Y' (f : X ⟶ X') (g : Y ⟶ Y'),
      F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
        (t X Y).hom ≫ (F.map f ⊗ₘ F.map g))
    (ha : ∀ X Y Z, (t (X ⊗ Y) Z).hom ≫ (t X Y).hom ▷ F.obj Z ≫
      (α_ _ _ _).hom = F.map (α_ X Y Z).hom ≫ (t X (Y ⊗ Z)).hom ≫
        F.obj X ◁ (t Y Z).hom)
    (hl : ∀ X, (t (𝟙_ C) X).hom ≫ z.hom ▷ F.obj X ≫ (λ_ _).hom =
      F.map (λ_ X).hom)
    (hr : ∀ X, (t X (𝟙_ C)).hom ≫ F.obj X ◁ z.hom ≫ (ρ_ _).hom =
      F.map (ρ_ X).hom) :
    ∃ m : F.Monoidal, ∀ X Y, m.toLaxMonoidal.μ X Y = (t X Y).inv := by
  let c : F.CoreMonoidal := Functor.CoreMonoidal.mk' z.symm (fun X Y ↦ (t X Y).symm)
    (by
      intro X Y f Z
      simpa only [Iso.symm_inv, tensorHom_id, F.map_id] using (hn X Y Z Z f (𝟙 Z)).symm)
    (by
      intro X Y Z f
      simpa only [Iso.symm_inv, id_tensorHom, F.map_id] using (hn Z Z X Y (𝟙 Z) f).symm)
    ha
    (by
      intro X
      apply (cancel_mono (λ_ (F.obj X)).hom).mp
      rw [Iso.symm_inv, Iso.symm_inv, Iso.inv_hom_id, Category.assoc, Category.assoc, hl X,
        ← F.map_comp, Iso.inv_hom_id, F.map_id])
    (by
      intro X
      apply (cancel_mono (ρ_ (F.obj X)).hom).mp
      rw [Iso.symm_inv, Iso.symm_inv, Iso.inv_hom_id, Category.assoc, Category.assoc, hr X,
        ← F.map_comp, Iso.inv_hom_id, F.map_id])
  exact ⟨c.toMonoidal, fun _ _ ↦ rfl⟩

private theorem section_monoidal_normalized
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, r}] [HasSheafify J Ab.{r}]
    [(J.W (A := Ab.{r})).IsMonoidal]
    (R : Sheaf J Ab.{r}) [MonObj R] [IsCommMonObj R] :
    ∃ m : (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal,
      ∀ (M N : Mod (Sheaf J Ab.{r}) R) (V : Cᵒᵖ)
        (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((m.toLaxMonoidal.μ M N).val.app V)
          (InternalAbelianSheafModule.comparison_sectionTmul J R _ _ V x y) =
            InternalAbelianSheafModule.comparison_internalTmul J R M N V x y := by
  obtain ⟨_, t, z, ht, _, hn, ha, hl, hr, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison J R
  obtain ⟨m, hm⟩ := monoidal_with_tensor _ t z hn ha hl hr
  refine ⟨m, ?_⟩
  intro M N V x y
  rw [hm, ← ht M N V x y]
  exact congrArg (fun f ↦ (f.val.app V)
      (InternalAbelianSheafModule.comparison_internalTmul J R M N V x y))
    (t M N).hom_inv_id

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

/-- Restriction along the inverse coefficient isomorphism preserves the internal pure
pairing. Source: the coequalizer tensor comparison for restriction along an isomorphism
(blueprint: lem-sfb-finite-coefficient-section-tensor-normalization).
Proof: precompose the inverse tensorator with the relative tensor projection and use
its defining coequalizer equation; evaluate the resulting sheaf map on a pure tensor. -/
private theorem comap_μ_pure (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u})
    (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T))
    [IsIso (coefficientMap e.inv.hom T)] (V : T.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    (((Functor.LaxMonoidal.μ (Mod.comap (coefficientMap e.inv.hom T)) M N).hom.hom.app V).hom)
      (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
        (condensedRingObj (coefficient A) T) _ _ V x y) =
      InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
        (condensedRingObj R T) M N V x y := by
  have h := Mod.tensorπ_comapTensorIso_hom_hom (coefficientMap e.inv.hom T) M N
  exact congrArg (fun f ↦ (f.hom.app V).hom
    (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      M.X N.X).app V).hom (x ⊗ₜ[ℤ] y))) h

/-- The actual composite section encoding has a tensorator normalized on every local
pure tensor. This assertion is independent of any scheme morphism or adjunction mate.
Source: normalized internal/section, ring-isomorphism, and constant-scalar tensor transport
(blueprint: lem-sfb-finite-coefficient-section-tensor-normalization).
Proof: choose the internal/section comparisons together with their generator formula,
build their strong monoidal structure without discarding that formula, and compose with
the normalized ring-isomorphism and constant-scalar tensor structures. Each of the three
tensorators and coefficient restriction preserves the pure pairing, so their composite
does too. No finiteness or nonzero-ring hypothesis is needed. -/
theorem coefficientSectionTensor_normalized
    (e : Mon.mk R ≅ Mon.mk (coefficient A)) (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T)
    [IsIso (coefficientMap e.inv.hom T)] :
    let F := Mod.comap (coefficientMap e.inv.hom T) ⋙
      (sectionEncoding A T c ⋙ fixedRestriction A T)
    ∃ m : F.Monoidal,
      ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T))
        (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((m.toLaxMonoidal.μ M N).hom.app V)
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
            (F.obj M) (F.obj N) V x y) =
          InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
            (condensedRingObj R T) M N V x y := by
  obtain ⟨ms, hs⟩ := section_monoidal_normalized
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)
  let := ms
  let := HasDerivedCategory.standard (Ordinary A T)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sectionRing A T)))
  obtain ⟨r⟩ := SheafOfModules.ringIso_tensor_transport c
  let := r.monoidal
  let : (sectionEncoding A T c).Monoidal := by
    unfold sectionEncoding
    infer_instance
  let : (fixedRestriction A T).Monoidal :=
    (ConstantScalarRestriction.ordinary (Scheme.ProEt.topology T)
      (ULift.{u + 1} A)).braided.toMonoidal
  refine ⟨inferInstance, ?_⟩
  intro M N V x y
  let H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T) ⥤
      Internal A T := Mod.comap (coefficientMap e.inv.hom T)
  let S := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)).functor
  have hr : ((r.monoidal.toMonoidal.toLaxMonoidal.μ
      (S.obj (H.obj M)) (S.obj (H.obj N))).val.app V)
      (ConstantScalarRestriction.ringPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
        ((sectionEncoding A T c).obj (H.obj M))
        ((sectionEncoding A T c).obj (H.obj N)) V x y) =
    InternalAbelianSheafModule.comparison_sectionTmul (Scheme.ProEt.topology T)
      (condensedRingObj (coefficient A) T) (S.obj (H.obj M)) (S.obj (H.obj N)) V x y := by
    exact r.pure_inv (S.obj (H.obj M)) (S.obj (H.obj N)) V x y
  have hc := (ConstantScalarRestriction.ordinary (Scheme.ProEt.topology T)
    (ULift.{u + 1} A)).tensor_inv
      ((sectionEncoding A T c).obj (H.obj M))
      ((sectionEncoding A T c).obj (H.obj N)) V x y
  let fH := ((Functor.LaxMonoidal.μ H M N).hom.hom.app V).hom
  let fS := (Functor.LaxMonoidal.μ S (H.obj M) (H.obj N)).val.app V
  let fR := (r.monoidal.toMonoidal.toLaxMonoidal.μ
    (S.obj (H.obj M)) (S.obj (H.obj N))).val.app V
  exact (congrArg (fun z ↦ fH (fS (fR z))) hc).trans
    ((congrArg (fun z ↦ fH (fS z)) hr).trans
      ((congrArg (fun z ↦ fH z) (hs (H.obj M) (H.obj N) V x y)).trans
        (comap_μ_pure A e T M N V x y)))

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
