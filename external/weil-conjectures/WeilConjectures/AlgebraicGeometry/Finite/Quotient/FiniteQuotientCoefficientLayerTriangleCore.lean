/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Representative short exact sequence for the finite coefficient layer
Source: Stacks Project, sites-cohomology.tex, Tag 0942.
(blueprint: lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

section TensorSequence

variable {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C]

private def tensorSequence (S : ShortComplex C) (P : CochainComplex C ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      ((MonoidalCategory.curriedTensor C).flip.map S.f) (.up ℤ)).app P)
    ((NatTrans.mapHomologicalComplex
      ((MonoidalCategory.curriedTensor C).flip.map S.g) (.up ℤ)).app P)
    (by
      ext i : 1
      change (MonoidalCategory.tensorLeft (P.X i)).map S.f ≫
        (MonoidalCategory.tensorLeft (P.X i)).map S.g = 0
      rw [← Functor.map_comp, S.zero, Functor.map_zero])

private theorem tensorSequence_shortExact (S : ShortComplex C) (hS : S.ShortExact)
    (P : CochainComplex C ℤ)
    (hflat : ∀ i : ℤ, exactFunctor C C (MonoidalCategory.tensorRight (P.X i))) :
    (tensorSequence S P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hl : exactFunctor C C (MonoidalCategory.tensorLeft (P.X i)) :=
    (exactFunctor C C).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X i)).symm (hflat i)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i)) := hl.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft (P.X i)) := hl.2
  exact hS.map_of_exact (MonoidalCategory.tensorLeft (P.X i))

end TensorSequence

private theorem quotientPresheaf_surjective
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Surjective ((completedAdicFinitePresheafStep X d n).app U) := by
  classical
  let q : completedAdicQuotient d (n + 1) →+* completedAdicQuotient d n :=
    RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.down
    refine ⟨ULift.up (Ideal.Quotient.mk _ x), ?_⟩
    apply ULift.ext
    simpa [q, adicQuotientMap] using hx
  intro f
  change C(ConnectedComponents U.unop.left, completedAdicQuotient d n) at f
  let g : C(ConnectedComponents U.unop.left, completedAdicQuotient d (n + 1)) :=
    ⟨Function.surjInv hq ∘ f, (continuous_of_discreteTopology).comp f.continuous⟩
  refine ⟨g, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact Function.surjInv_eq hq (f x)

private theorem quotientUnit_epi
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) : Epi (finiteQuotientUnitMap X d n) := by
  let J := ProEt.topology X
  let step := completedAdicFinitePresheafStep X d n
  have hs : Presheaf.IsLocallySurjective J step :=
    Presheaf.isLocallySurjective_of_surjective J step (quotientPresheaf_surjective X d n)
  have hstep : Sheaf.IsLocallySurjective (completedAdicFiniteStep X d n) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J step).2 hs
  have hq : ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))) =
      completedAdicFiniteStep X d n := by
    change (completedAdicRingSystem X d).map (homOfLE (Nat.le_succ n)).op = _
    exact Functor.ofOpSequence_map_homOfLE_succ _ n
  let F := SheafOfModules.toSheaf.{t + 1} (completedAdicFiniteRing X d (n + 1))
  have hF : Sheaf.IsLocallySurjective (F.map (finiteQuotientUnitMap X d n)) := by
    constructor
    intro U s
    change Presheaf.imageSieve _ s ∈ J U
    let q := (sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
    have : Sheaf.IsLocallySurjective q := by rw [show q = _ from hq]; exact hstep
    apply J.superset_covering (S := Presheaf.imageSieve q.hom s)
    · rintro V f ⟨a, ha⟩
      exact ⟨a, ha⟩
    · exact Presheaf.imageSieve_mem J q.hom s
  have : Epi (F.map (finiteQuotientUnitMap X d n)) := Sheaf.epi_of_isLocallySurjective _
  exact F.epi_of_epi_map inferInstance

attribute [local irreducible] completedAdicChangeData

private theorem homotopyModelIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ)
    (hε : IsIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    Nonempty (L.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) := by
  have := hε
  exact ⟨L.mapIso ((DerivedCategory.quotientCompQhIso C).app P).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso D).app _⟩

private theorem completedChange_modelIso
    (X : Scheme.{t}) {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S)
    (P : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ)
    (hk : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    Nonempty ((completedAdicDerivedChange X φ).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let E := completedAdicChange X φ
  let L := completedAdicDerivedChange X φ
  have hEAdd : E.Additive := inferInstance
  obtain ⟨ε, hu, ht, hc⟩ := completedChangeModels X φ
  change DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh at ε
  have hε : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc P hk
  change Nonempty (L.obj (DerivedCategory.Q.obj P) ≅
    DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
  clear hu ht hc
  -- Abstract the chosen functors before the kernel checks the localization composition.
  clear_value E L
  as_aux_lemma => exact homotopyModelIso E L ε P hε

private theorem completedChange_obj
    (X : Scheme.{t}) {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    (completedAdicChange X φ).obj N = SheafOfModules.changeOfRings φ N :=
  (completedAdicChangeData X φ).choose_spec.choose N

private theorem completedChange_map
    (X : Scheme.{t}) {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) {N N' : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)} (f : N ⟶ N') :
    (completedAdicChange X φ).map f =
      eqToHom (completedChange_obj X φ N) ≫ SheafOfModules.changeOfRingsHom φ N f ≫
        eqToHom (completedChange_obj X φ N').symm :=
  (completedAdicChangeData X φ).choose_spec.choose_spec.choose f

private def restrictedModelIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {Z W V : CochainComplex C ℤ}
    (e : DerivedCategory.Q.obj Z ≅ DerivedCategory.Q.obj W) (e' : W ≅ V) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Z) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj V) :=
  (F.mapDerivedCategoryFactors.app Z).symm ≪≫
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app W ≪≫
    DerivedCategory.Q.mapIso ((F.mapHomologicalComplex (.up ℤ)).mapIso e')

private theorem completedBalanceIso
    (X : Scheme.{t}) {R S V : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ) :
    Nonempty (((completedAdicChange X ψ).mapHomologicalComplex (.up ℤ)).obj
      (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((completedAdicChange X χ).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact ⟨asIso (completedAdicBalance X φ ψ χ h P)⟩

private theorem restrictedChangeComplexIso
    (X : Scheme.{t}) {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [EssentiallySmall.{t + 1} X.ProEt]
    (P : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ) :
    letI := SheafOfModules.cochainModulesMonoidal R
    let F := SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
      (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj P) ≅
      (((MonoidalCategory.tensorRight (F.obj (SheafOfModules.unit
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))).mapHomologicalComplex
        (.up ℤ)).obj P)) := by
  obtain ⟨e⟩ := completedOrdinaryRestrictionComparison X φ
  exact ⟨(Functor.mapHomologicalComplexCompIso e (.up ℤ)).app P⟩

private theorem quotientRepresentativeIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ)
    (C : CochainComplex (CompletedAdicModules X d) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := completedAdicCommRing X d) C)
    (eC : DerivedCategory.Q.obj C ≅ M) :
    Nonempty (DerivedCategory.Q.obj
      (DerivedCategory.Q.objPreimage ((completedAdicQuotientReduction X d n).obj M)) ≅
      DerivedCategory.Q.obj (((completedAdicChange X
        (completedAdicCommProjection X d n)).mapHomologicalComplex (.up ℤ)).obj C)) := by
  obtain ⟨e⟩ := completedChange_modelIso X (completedAdicCommProjection X d n) C hC
  exact ⟨DerivedCategory.Q.objObjPreimageIso
      ((completedAdicQuotientReduction X d n).obj M) ≪≫
    (completedAdicDerivedChange X (completedAdicCommProjection X d n)).mapIso eC.symm ≪≫ e⟩

private theorem restriction_exact
    (X : Scheme.{t}) {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (φ : R ⟶ S) [EssentiallySmall.{t + 1} X.ProEt] :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} φ) := by
  let F := SheafOfModules.restrictScalars.{t + 1} φ
  let U := SheafOfModules.toSheaf.{t + 1} R
  have : PreservesFiniteLimits (F ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{t + 1} S))
  have : PreservesFiniteColimits (F ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{t + 1} S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F U,
    preservesFiniteColimits_of_reflects_of_preserves F U⟩

private theorem previousModelIso
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ)
    (C : CochainComplex (CompletedAdicModules X d) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := completedAdicCommRing X d) C)
    (eC : DerivedCategory.Q.obj C ≅ M) :
    letI : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
    letI := SheafOfModules.cochainModulesMonoidal
      (completedAdicFiniteCommRing X d (n + 1))
    let P := ((completedAdicChange X
      (completedAdicCommProjection X d (n + 1))).mapHomologicalComplex (.up ℤ)).obj C
    let N := (SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)))).obj
          (SheafOfModules.unit (completedAdicFiniteRing X d n))
    Nonempty (finiteQuotientPreviousObject X d M n ≅ DerivedCategory.Q.obj
      (((MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : MonoidalCategory (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1))) :=
    SheafOfModules.cochainModulesMonoidal (completedAdicFiniteCommRing X d (n + 1))
  let φ := completedAdicCommProjection X d (n + 1)
  let ψ := completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)
  let χ := completedAdicCommProjection X d n
  let P := ((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj C
  let F := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)
  have he := restriction_exact X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)
  have : PreservesFiniteLimits F := he.1
  have : PreservesFiniteColimits F := he.2
  let en' := Classical.choice (quotientRepresentativeIso X d M n C hC eC)
  let et := Classical.choice (restrictedChangeComplexIso X ψ P)
  let eb := Classical.choice (completedBalanceIso X φ ψ χ
    (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n)) C)
  exact ⟨restrictedModelIso F en' eb.symm ≪≫ DerivedCategory.Q.mapIso et⟩

/-- The flat representative and coefficient sequence underlying the coefficient-layer triangle.
The construction resolves the successor reduction by a flat-term K-flat complex, tensors the
actual kernel-unit-quotient sequence, and records the resulting degreewise short exact sequence.
The later triangle theorem only applies `triangleOfSES` and identifies the three representatives.

Source: Stacks Project, sites-cohomology.tex, Tag 0942, lemma-bounded, proof (1).
(blueprint: lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core).
-/
theorem finiteQuotient_coefficient_layer_core
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) :
    ∃ S : ShortComplex (CochainComplex
      (SheafOfModules.{t + 1} (completedAdicFiniteRing X d (n + 1))) ℤ),
      S.ShortExact ∧
      Nonempty (finiteQuotientLayerObject X d M n ≅ DerivedCategory.Q.obj S.X₁) ∧
      Nonempty ((completedAdicQuotientReduction X d (n + 1)).obj M ≅
        DerivedCategory.Q.obj S.X₂) ∧
      Nonempty (finiteQuotientPreviousObject X d M n ≅ DerivedCategory.Q.obj S.X₃) := by
  classical
  let : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (completedAdicFiniteCommRing X d (n + 1))
  let : MonoidalCategory (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1))) :=
    SheafOfModules.monoidalCategory (completedAdicFiniteCommRing X d (n + 1))
  let : SymmetricCategory (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1))) :=
    SheafOfModules.symmetricCategory (completedAdicFiniteCommRing X d (n + 1))
  let : MonoidalPreadditive (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1))) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicFiniteCommRing X d (n + 1))
  let G := DerivedCategory.Q.objPreimage M
  obtain ⟨C, f, hC, hfC, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedAdicCommRing X d) G
  have : QuasiIso f := hf
  let eC : (DerivedCategory.Q (C := CompletedAdicModules X d)).obj C ≅ M :=
    asIso ((DerivedCategory.Q (C := CompletedAdicModules X d)).map f) ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  let φ := completedAdicCommProjection X d (n + 1)
  let E : CompletedAdicModules X d ⥤
      SheafOfModules.{t + 1} (completedAdicFiniteRing X d (n + 1)) := completedAdicChange X φ
  have hEAdd : E.Additive := completedAdicChange_additive X φ
  let P := (E.mapHomologicalComplex (.up ℤ)).obj C
  have hp := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ C E (completedChange_obj X φ) (fun g ↦ completedChange_map X φ g) hC hfC
  obtain ⟨cp⟩ := completedChange_modelIso X φ C hC
  let ep : (completedAdicQuotientReduction X d (n + 1)).obj M ≅ DerivedCategory.Q.obj P :=
    (completedAdicDerivedChange X φ).mapIso eC.symm ≪≫ cp
  let q := finiteQuotientUnitMap X d n
  have : Epi q := quotientUnit_epi X d n
  let S₀ := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS₀ : S₀.ShortExact := { exact := ShortComplex.exact_kernel q }
  let S := tensorSequence S₀ P
  have hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedAdicFiniteCommRing X d (n + 1)) P := hp.1
  have hS : S.ShortExact := tensorSequence_shortExact S₀ hS₀ P hp.2
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · obtain ⟨c, _, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison
      (completedAdicFiniteCommRing X d (n + 1))
    clear_value ep
    clear_value P
    as_aux_lemma =>
      refine ⟨?_⟩
      exact ((SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X)
        (completedAdicFiniteCommRing X d (n + 1))).mapIso
        (ep.prod (Iso.refl _))) ≪≫ c P hP (kernel q)
  · clear_value ep
    clear_value P
    as_aux_lemma =>
      let eu : S.X₂ ≅ P := HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ MonoidalCategory.rightUnitor (P.X i)) (by
          intro i j h
          exact (MonoidalCategory.rightUnitor_naturality (P.d i j)).symm)
      exact ⟨ep ≪≫ DerivedCategory.Q.mapIso eu.symm⟩
  · exact previousModelIso X d M n C hC eC

end AlgebraicGeometry.Scheme
