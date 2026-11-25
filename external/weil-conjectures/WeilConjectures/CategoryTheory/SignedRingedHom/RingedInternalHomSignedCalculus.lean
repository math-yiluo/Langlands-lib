/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses

/-! # Canonical closed calculus for the recorded ringed-site internal Hom

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 08J9, 08JB and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
The original tensor, restriction and exactness statements are retained by public import.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.SignedRingedHom

/-- The module category of the ringed site.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

/-- The sheafified tensor, before deriving.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleMonoidal : MonoidalCategory (Modules J R) :=
  SheafOfModules.monoidalCategory R

/-- The ordinary symmetry of module sheaves.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleSymmetric : SymmetricCategory (Modules J R) :=
  SheafOfModules.symmetricCategory R

/-- The sheaf tensor--Hom adjunction.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleClosed : MonoidalClosed (Modules J R) :=
  SheafOfModules.monoidalClosed (R := R)

/-- The module category is Grothendieck abelian.
Source: Stacks 07A5 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: sheafification is exact and module sheaves have the local free generators. -/
instance moduleGrothendieck : IsGrothendieckAbelian.{u} (Modules J R) :=
  SheafOfModules.isGrothendieckAbelian _

/-- Additivity of tensoring module sheaves in either variable.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: tensor is the sheafification of the sectionwise module tensor, whose
maps are additive in each factor; sheafification is additive. -/
theorem moduleMonoidalPreadditive : MonoidalPreadditive (Modules J R) := by
  have (M : Modules J R) : (tensorLeft M).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have (M : Modules J R) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

attribute [instance] moduleMonoidalPreadditive

/-- Functorial flat covers used to construct the ordinary K-flat derived tensor.
Source: Stacks 06YL and 06YS, local free covers and their functorial direct sums
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: take the sum of the free modules extended by zero from site objects, indexed
by all local sections of the module. The evaluation is an epimorphism, each free
summand is flat, and sums of flat modules are flat. A module map sends the summand
indexed by a section to the summand indexed by its image. This gives a functorial
flat cover, and hence the flat resolutions used in the tensor--Hom construction. -/
theorem moduleFlatResolution : Abelian.HasFunctorialFlatResolution (Modules J R) := by
  exact SheafOfModules.hasFunctorialFlatResolution_kfi R

attribute [instance] moduleFlatResolution

/-- The unbounded module derived category, with its small Hom universe.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
abbrev D [HasDerivedCategory.{u} (Modules J R)] := DerivedCategory (Modules J R)

/-- The countable-colimit convention used by the native derived tensor API.
Source: Stacks 06YS (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance moduleCountableColimits : HasColimitsOfSize.{0, 0} (Modules J R) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} (Modules J R)

variable [HasDerivedCategory.{u} (Modules J R)]

/-- The ordinary K-flat derived monoidal structure, with coherences descended
from total tensor complexes.
Source: Stacks 06YS, 08J9
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance derivedMonoidal : MonoidalCategory (D J R) :=
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory (Modules J R)

/-- Cache the native localization tensor map with the same monoidal instance.
Source: Stacks 06YS (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance localizationLaxMonoidal :
    (DerivedCategory.Q : CochainComplex (Modules J R) ℤ ⥤ D J R).LaxMonoidal :=
  DerivedCategory.laxMonoidalQ (Modules J R)

private theorem nativeMonoidalEquality (A : Type (u + 1)) [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
    [HasDerivedCategory.{u} A] :
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory A =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (.up ℤ)) := by
  rfl

/-- The native derived tensor and its explicit localization implementation agree.
Source: Stacks 06YS, 08J9
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: both are the localization monoidal structure induced by the same K-flat
left derivability structure and the same ordinary total tensor. Unfold the
native instance and identify the localization structure fields. -/
theorem derivedMonoidal_eq_localization :
    derivedMonoidal J R =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules J R) (ComplexShape.up ℤ)) := by
  exact nativeMonoidalEquality (Modules J R)

/-- The recorded derived internal Hom, with independent-universe implementation
specialized to this small site.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def homFunctor : (D J R)ᵒᵖ × D J R ⥤ D J R :=
  derivedInternalHomOfUniverses.{u, u, u, u} J R

/-- The unary recorded Hom functor.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable abbrev hom (K : D J R) : D J R ⥤ D J R :=
  Prod.sectR (op K) (D J R) ⋙ homFunctor J R

/-- The ordinary Koszul braiding descended from complexes.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable instance derivedBraiding : BraidedCategory (D J R) :=
  Eq.mp (congrArg (fun m ↦ @BraidedCategory (D J R) _ m)
    (derivedMonoidal_eq_localization J R).symm)
    (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules J R) (ComplexShape.up ℤ)))

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
/-- The total tensor used in the representative model is the native complex tensor.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: both are the totalization of the curried sheaf tensor, with the same
summands, differential and Koszul sign. Unfold the two totalizations. -/
theorem totalTensor_eq_native (P L : CochainComplex (Modules J R) ℤ) :
    (WeilConjectures.coefficientTotalTensor.{u, u, u} J R).obj (P, L) = P ⊗ L := by
  rfl

/-- The explicit identification of the two ordinary total-tensor implementations.
Source: Stacks 06YL (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def totalTensorNativeIso (P L : CochainComplex (Modules J R) ℤ) :
    (WeilConjectures.coefficientTotalTensor.{u, u, u} J R).obj (P, L) ≅ P ⊗ L :=
  eqToIso (totalTensor_eq_native J R P L)

section Normalization

private theorem nativeMonoidal_eq :
    RingedDerivedNative.monoidal.{u, u, u, u} J R = derivedMonoidal J R := by
  unfold RingedDerivedNative.monoidal derivedMonoidal
  with_reducible_and_instances rfl

private theorem normalizedAdjunction_exists :
    ∃ S : WeilConjectures.CoefficientClosedStructure (homFunctor J R),
      ∃ (h : S.monoidal = derivedMonoidal J R)
        (M : WeilConjectures.CoefficientTensorModels.{u, u, u, u} J R S),
        ∀ P L, (M.comparison.app (P, L)).hom ≫
          eqToHom (congrArg (fun (m : MonoidalCategory (D J R)) ↦
            @MonoidalCategory.tensorObj (D J R) _ m.toMonoidalCategoryStruct
            (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj L.obj)) h) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj ≫
          DerivedCategory.Q.map (totalTensorNativeIso J R P.obj L.obj).inv = 𝟙 _ := by
  have h0 : ∃ S : WeilConjectures.CoefficientClosedStructure (homFunctor J R),
      S.monoidal = RingedDerivedNative.monoidal.{u, u, u, u} J R ∧
        ∃ T : WeilConjectures.CoefficientTensorModels.{u, u, u, u} J R S,
          HEq T.comparison (RingedDerivedNative.comparison.{u, u, u, u} J R) :=
    RingedDerivedNative.closedAdjunction.{u, u, u, u} J R
  obtain ⟨S, hm, T, hT⟩ := h0
  rw [nativeMonoidal_eq] at hm
  rcases S with ⟨m, adj, ev⟩
  dsimp only at hm
  subst hm
  refine ⟨⟨_, adj, ev⟩, rfl, T, ?_⟩
  rcases T with ⟨comp, um⟩
  have ht : comp = RingedDerivedNative.comparison.{u, u, u, u} J R := eq_of_heq hT
  subst ht
  intro P L
  have := RingedDerivedNative.isIso_mu.{u, u, u, u} J R P.obj L.obj (Or.inl P.property)
  change inv (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj) ≫ 𝟙 _ ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj ≫ DerivedCategory.Q.map (𝟙 _) = 𝟙 _
  simpa only [Category.id_comp, Functor.map_id, Category.comp_id] using
    IsIso.inv_hom_id (Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj)

private theorem kFlat_representative (X : D J R) :
    ∃ L : CochainComplex (Modules J R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L ∧
        Nonempty (DerivedCategory.Q.obj L ≅ X) := by
  obtain ⟨K, f, hK, -, hf, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (DerivedCategory.Q.objPreimage X)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

omit [HasDerivedCategory (Modules J R)] in
private theorem resolution_isKInjective (M : CochainComplex (Modules J R) ℤ) :
    ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M).IsKInjective := by
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
    u, u, u} J R).1
  exact CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M

private theorem homRepresentative_surjective (P L M : CochainComplex (Modules J R) ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (ξ : DerivedCategory.Q.obj P ⟶
      (homFunctor J R).obj (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)) :
    ∃ φ : P ⟶ homComplex (R := R) L
        ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M),
      DerivedCategory.Q.map φ ≫
        (WeilConjectures.coefficientHomResolutionIso.{u, u, u, u} J R L M).inv = ξ := by
  have := resolution_isKInjective J R M
  have : (homComplex (R := R) L
      ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M)).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, u, u}
      (J := J) (R := R) L _ hL
  obtain ⟨f, hf⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj P) _).2
      ((DerivedCategory.quotientCompQhIso (Modules J R)).hom.app P ≫ ξ ≫
        (WeilConjectures.coefficientHomResolutionIso.{u, u, u, u} J R L M).hom ≫
          (DerivedCategory.quotientCompQhIso (Modules J R)).inv.app _)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient (Modules J R) (.up ℤ)).map_surjective f
  refine ⟨φ, ?_⟩
  have hn := DerivedCategory.quotientCompQhIso_hom_naturality (C := Modules J R) φ
  rw [hf] at hn
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hn
  rw [← (cancel_epi _).1 hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [HasDerivedCategory (Modules J R)] in
attribute [local irreducible] SheafOfModules.monoidalCategory in
private theorem totalTensor_ext (P L I : CochainComplex (Modules J R) ℤ)
    (f g : (WeilConjectures.coefficientTotalTensor.{u, u, u} J R).obj (P, L) ⟶ I)
    (h : ∀ (a b : ℤ) (U : Cᵒᵖ) (x : (P.X a).val.obj U) (y : (L.X b).val.obj U),
      (f.f (a + b)).val.app U
          (WeilConjectures.coefficientTensorGenerator.{u, u, u} J R P L a b (a + b) rfl U x y) =
        (g.f (a + b)).val.app U
          (WeilConjectures.coefficientTensorGenerator.{u, u, u} J R P L a b (a + b) rfl U x y)) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = k at hab
  subst k
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X a) (L.X b)).inv).1
  apply ((PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).homEquiv
        ((P.X a).val ⊗ (L.X b).val) (I.X (a + b))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h a b U

/-- Two adjunction families with the same source-natural evaluations agree once they agree
on the uncurried maps out of K-flat representatives. -/
private theorem adjunction_eq_of_representatives
    (adj₁ adj₂ : ∀ P : D J R, tensorRight P ⊣ hom J R P)
    (ev₁ : ∀ (P P' Q : D J R) (f : P' ⟶ P),
      (tensorRight P').map ((homFunctor J R).map (Prod.mkHom f.op (𝟙 Q))) ≫
          (adj₁ P').counit.app Q =
        (tensorLeft ((homFunctor J R).obj (op P, Q))).map f ≫ (adj₁ P).counit.app Q)
    (ev₂ : ∀ (P P' Q : D J R) (f : P' ⟶ P),
      (tensorRight P').map ((homFunctor J R).map (Prod.mkHom f.op (𝟙 Q))) ≫
          (adj₂ P').counit.app Q =
        (tensorLeft ((homFunctor J R).obj (op P, Q))).map f ≫ (adj₂ P).counit.app Q)
    (gen : ∀ (P L M : CochainComplex (Modules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L →
      ∀ φ : P ⟶ homComplex (R := R) L
          ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M),
        ((adj₁ (DerivedCategory.Q.obj L)).homEquiv _ _).symm
            (DerivedCategory.Q.map φ ≫
              (WeilConjectures.coefficientHomResolutionIso.{u, u, u, u} J R L M).inv) =
          ((adj₂ (DerivedCategory.Q.obj L)).homEquiv _ _).symm
            (DerivedCategory.Q.map φ ≫
              (WeilConjectures.coefficientHomResolutionIso.{u, u, u, u} J R L M).inv)) :
    adj₁ = adj₂ := by
  have hQ (L : CochainComplex (Modules J R) ℤ)
      (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
      (M : CochainComplex (Modules J R) ℤ) :
      (adj₁ (DerivedCategory.Q.obj L)).counit.app (DerivedCategory.Q.obj M) =
        (adj₂ (DerivedCategory.Q.obj L)).counit.app (DerivedCategory.Q.obj M) := by
    obtain ⟨P, hP, ⟨σ⟩⟩ := kFlat_representative J R
      ((hom J R (DerivedCategory.Q.obj L)).obj (DerivedCategory.Q.obj M))
    obtain ⟨φ, hφ⟩ := homRepresentative_surjective J R P L M hL σ.hom
    have h := gen P L M hP hL φ
    rw [hφ, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit] at h
    exact (cancel_epi _).1 h
  have hL (L : CochainComplex (Modules J R) ℤ)
      (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L) (Y : D J R) :
      (adj₁ (DerivedCategory.Q.obj L)).counit.app Y =
        (adj₂ (DerivedCategory.Q.obj L)).counit.app Y := by
    let e := DerivedCategory.Q.objObjPreimageIso Y
    apply (cancel_epi ((hom J R (DerivedCategory.Q.obj L) ⋙
      tensorRight (DerivedCategory.Q.obj L)).map e.hom)).1
    rw [(adj₁ _).counit.naturality, (adj₂ _).counit.naturality, hQ L hL]
  funext P
  apply Adjunction.ext_counit
  ext Y
  obtain ⟨L, hL', ⟨eP⟩⟩ := kFlat_representative J R P
  have h₁ := ev₁ P (DerivedCategory.Q.obj L) Y eP.hom
  have h₂ := ev₂ P (DerivedCategory.Q.obj L) Y eP.hom
  rw [hL L hL' Y] at h₁
  exact (cancel_epi ((tensorLeft ((homFunctor J R).obj (op P, Y))).map eP.hom)).1
    (h₁.symm.trans h₂)

private theorem comparison_hom_eq {X Y : D J R} {x₁ x₂ : X ⟶ Y} [IsIso x₁] [IsIso x₂]
    {y₁ y₂ : Y ⟶ X} (h₁ : x₁ ≫ y₁ = 𝟙 X) (h₂ : x₂ ≫ y₂ = 𝟙 X) (hy : y₁ = y₂) :
    x₁ = x₂ := by
  subst hy
  have h := IsIso.eq_inv_of_hom_inv_id h₂
  calc x₁ = (x₁ ≫ y₁) ≫ x₂ := by rw [h, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    _ = x₂ := by rw [h₁, Category.id_comp]

private theorem normalizedAdjunction_unique
    (S₁ S₂ : WeilConjectures.CoefficientClosedStructure (homFunctor J R))
    (hS₁ : ∃ (h : S₁.monoidal = derivedMonoidal J R)
        (M : WeilConjectures.CoefficientTensorModels.{u, u, u, u} J R S₁),
        ∀ P L, (M.comparison.app (P, L)).hom ≫
          eqToHom (congrArg (fun (m : MonoidalCategory (D J R)) ↦
            @MonoidalCategory.tensorObj (D J R) _ m.toMonoidalCategoryStruct
            (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj L.obj)) h) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj ≫
          DerivedCategory.Q.map (totalTensorNativeIso J R P.obj L.obj).inv = 𝟙 _)
    (hS₂ : ∃ (h : S₂.monoidal = derivedMonoidal J R)
        (M : WeilConjectures.CoefficientTensorModels.{u, u, u, u} J R S₂),
        ∀ P L, (M.comparison.app (P, L)).hom ≫
          eqToHom (congrArg (fun (m : MonoidalCategory (D J R)) ↦
            @MonoidalCategory.tensorObj (D J R) _ m.toMonoidalCategoryStruct
            (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj L.obj)) h) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj ≫
          DerivedCategory.Q.map (totalTensorNativeIso J R P.obj L.obj).inv = 𝟙 _) :
    S₁ = S₂ := by
  rcases S₁ with ⟨m₁, adj₁, ev₁⟩
  rcases S₂ with ⟨m₂, adj₂, ev₂⟩
  obtain ⟨h₁, M₁, c₁⟩ := hS₁
  obtain ⟨h₂, M₂, c₂⟩ := hS₂
  dsimp only at h₁ h₂
  subst h₁ h₂
  suffices adj₁ = adj₂ by subst this; rfl
  apply adjunction_eq_of_representatives J R adj₁ adj₂ ev₁ ev₂
  intro P L M hP hL φ
  obtain ⟨ψ₁, g₁, e₁⟩ := M₁.uncurry_model ⟨P, hP⟩ ⟨L, hL⟩ M φ
  obtain ⟨ψ₂, g₂, e₂⟩ := M₂.uncurry_model ⟨P, hP⟩ ⟨L, hL⟩ M φ
  have hψ : ψ₁ = ψ₂ := totalTensor_ext J R P L _ ψ₁ ψ₂ (fun a b U x y ↦
    (g₁ a b (a + b) rfl (add_comm b a) U x y).trans
      (g₂ a b (a + b) rfl (add_comm b a) U x y).symm)
  have hc : (M₁.comparison.app (⟨P, hP⟩, ⟨L, hL⟩)).hom =
      (M₂.comparison.app (⟨P, hP⟩, ⟨L, hL⟩)).hom :=
    comparison_hom_eq J R (c₁ ⟨P, hP⟩ ⟨L, hL⟩) (c₂ ⟨P, hP⟩ ⟨L, hL⟩) rfl
  apply (cancel_epi (M₁.comparison.hom.app (⟨P, hP⟩, ⟨L, hL⟩))).1
  refine e₁.trans ?_
  refine (congrArg (fun ψ ↦ DerivedCategory.Q.map ψ ≫
    WeilConjectures.coefficientHomResolutionInverse.{u, u, u, u} J R M) hψ).trans ?_
  refine e₂.symm.trans ?_
  exact congrArg (fun f ↦ f ≫ _) hc.symm

/-- The tensor--Hom adjunction is uniquely fixed by ordinary evaluation on
K-flat representatives, for the actual derived monoidal structure.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: compute the tensor by a K-flat source and Hom by a K-injective target.
Componentwise evaluation identifies the two Hom sets by ordinary currying.
The Hom differential and total-tensor Koszul differential agree under this
identification. Quasi-isomorphism invariance descends the equivalence through
the two localizations. It is natural also in the source, giving a closed
structure S. The total-tensor localization comparison is its representative
model. Conversely that model fixes uncurrying on every K-flat representative;
these representatives present the derived category, so it fixes the Hom
bijections everywhere. An adjunction is determined by its Hom bijections. -/
theorem normalizedAdjunction_existsUnique :
    ∃! S : WeilConjectures.CoefficientClosedStructure (homFunctor J R),
      ∃ (h : S.monoidal = derivedMonoidal J R)
        (M : WeilConjectures.CoefficientTensorModels.{u, u, u, u} J R S),
        ∀ P L, (M.comparison.app (P, L)).hom ≫
          eqToHom (congrArg (fun (m : MonoidalCategory (D J R)) ↦
            @MonoidalCategory.tensorObj (D J R) _ m.toMonoidalCategoryStruct
            (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj L.obj)) h) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P.obj L.obj ≫
          DerivedCategory.Q.map (totalTensorNativeIso J R P.obj L.obj).inv = 𝟙 _ := by
  exact (normalizedAdjunction_exists J R).elim fun S hS ↦
    ExistsUnique.intro S hS fun S' hS' ↦ normalizedAdjunction_unique J R S' S hS' hS

end Normalization

/-- The unique evaluation-normalized adjunction, not an arbitrary chosen adjoint.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def adjunction (K : D J R) : tensorRight K ⊣ hom J R K :=
  Eq.mp (congrArg (fun (m : MonoidalCategory (D J R)) ↦ ∀ P : D J R,
      @MonoidalCategory.tensorRight (D J R) _ m P ⊣ hom J R P)
    (normalizedAdjunction_existsUnique J R).choose_spec.1.choose)
    (normalizedAdjunction_existsUnique J R).choose.adjunction K

/-- Moving a shift between the two tensor inputs, using ordinary totalization.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def tensorParameterShiftIso (K : D J R) (s : ℤ) (X : D J R) :
    X ⊗ K⟦s⟧ ≅ X⟦s⟧ ⊗ K :=
  (((curriedTensor (D J R)).obj X).commShiftIso s).app K ≪≫
    ((((curriedTensor (D J R)).flip.obj K).commShiftIso s).app X).symm

/-- Naturality of the ordinary tensor shift comparison.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: the second-input total-tensor shift is natural in the first input by the
bifunctor shift structure. The inverse first-input shift is natural by its
functor commutation with shifts. Compose these two naturality equations. -/
theorem tensorParameterShift_naturality (K : D J R) (s : ℤ)
    (X Y : D J R) (f : X ⟶ Y) :
    (tensorRight (K⟦s⟧)).map f ≫ (tensorParameterShiftIso J R K s Y).hom =
      (tensorParameterShiftIso J R K s X).hom ≫
        (shiftFunctor (D J R) s ⋙ tensorRight K).map f := by
  dsimp only [tensorParameterShiftIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.comp_map]
  rw [← Category.assoc]
  change (((curriedTensor (D J R)).map f).app (K⟦s⟧) ≫
      (((curriedTensor (D J R)).obj Y).commShiftIso s).hom.app K) ≫ _ = _
  rw [← NatTrans.shift_app_comm ((curriedTensor (D J R)).map f) s K,
    Category.assoc]
  change _ ≫ (shiftFunctor (D J R) s).map
      (((curriedTensor (D J R)).flip.obj K).map f) ≫ _ = _
  rw [Functor.commShiftIso_inv_naturality, Category.assoc]

/-- The natural tensor parameter shift comparison.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def tensorParameterShift (K : D J R) (s : ℤ) :
    tensorRight (K⟦s⟧) ≅ shiftFunctor (D J R) s ⋙ tensorRight K :=
  NatIso.ofComponents (tensorParameterShiftIso J R K s)
    (fun {X Y} f ↦ tensorParameterShift_naturality J R K s X Y f)

/-- The signed source shift of internal Hom, defined as the unique adjunction
mate of the ordinary total-tensor shift. It has the signed reindexing of the
Hom complex; changing its normalization by a scalar depending only on s
multiplies every component by that same scalar.
Source: Stacks 0A8X and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
noncomputable def sourceShift (K : D J R) (s : ℤ) :
    hom J R (K⟦s⟧) ≅ hom J R K ⋙ shiftFunctor (D J R) (-s) :=
  (adjunction J R (K⟦s⟧)).rightAdjointUniq
    (((shiftEquiv (D J R) s).toAdjunction.comp (adjunction J R K)).ofNatIsoLeft
      (tensorParameterShift J R K s).symm)

end CategoryTheory.SignedRingedHom
