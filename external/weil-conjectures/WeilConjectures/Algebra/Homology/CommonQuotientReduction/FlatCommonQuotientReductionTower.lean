/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CommonQuotientTowerPresentation.CommonQuotientTowerPresentationSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Homology.OrdinaryCommonQuotientTower.OrdinaryCommonQuotientTowerSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Flat common-quotient reduction, with strict towers and quotient cones

Source: Stacks Project, proetale.tex, Tag 099L, section-derived-completion-noetherian;
sites-cohomology.tex, Tags 06YS, 06YT, 06YY; sites-modules.tex, Tag 03EK.
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower).

The quotient ideals are the kernel ideal sheaves in the common-quotient presentation.
Both derived scalar extensions are the existing universal cochain models. The ordinary
comparisons, transitions and cones are characterized by their actual sheafified tensor
sections. Scalar extension in the existing library writes the scalar first: `s ⊗ p`.
-/

@[expose] public noncomputable section
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v r wR wB wS wA wT
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules.CommonQuotientReduction

attribute [local irreducible] monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients IsFlatOnSite

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The recorded module category, with no change of encoding or coefficient universe.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev Modules (A : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J A)

/-- Actual restriction of scalars, used also termwise on complexes.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev restriction {A T : Sheaf J CommRingCat.{r}} (a : A ⟶ T) :
    Modules T ⥤ Modules A :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)

/-- A pure scalar-extension section in the prescribed ordinary presentation of a
cochain derived-change-of-rings model. This is precisely the sheafification-unit
image of the balanced tensor, transported along the model's object equality.
Source: Stacks 03EK (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
def scalarSection {A T : Sheaf J CommRingCat.{r}} {a : A ⟶ T}
    [HasDerivedCategory.{wA} (Modules A)] [HasDerivedCategory.{wT} (Modules T)]
    (F : DerivedChangeOfRingsCochainModel a) (M : Modules A)
    (U : Cᵒᵖ) (s : T.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
      (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x))

variable {R B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
  (D : CommonQuotientTowerPresentation φ)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wB} (Modules B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Modules (D.S.obj (op n)))]
  (a : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} (D.projection n))
  (b : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (D.extensionProjection n))

/-- The actual `S_n`-linear complex obtained by reduction over `R`.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev leftComplex (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((a n).E.mapHomologicalComplex (.up ℤ)).obj
    (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The actual `S_n`-linear complex obtained by reduction over `B`.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev rightComplex (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((b n).E.mapHomologicalComplex (.up ℤ)).obj P

/-- The levels of the first strict tower, restricted to `R`.
Source: Stacks 099L (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev leftLevel (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).obj
    (leftComplex D a n P)

/-- The levels of the second strict tower, also restricted to `R` through `q_n`.
Source: Stacks 099L (blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
abbrev rightLevel (n : ℕ) (P : CochainComplex (Modules B) ℤ) :=
  ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).obj
    (rightComplex D b n P)

attribute [local irreducible] scalarSection

/-- The full normalized comparison specification. All maps below are fixed by pure
sections or by localization/counit compatibility; in particular the strict cones
are the quotient cones, not arbitrary morphisms with the same vertices.

Source: Stacks 099L, 03EK and 06YY
(blueprint: lem-weil-pbc-flat-common-quotient-reduction-tower). -/
structure Comparison where
  /-- Restriction on derived categories. -/
  res : DerivedCategory (Modules B) ⥤ DerivedCategory (Modules R)
  /-- Its prescribed localization of termwise restriction. -/
  resFactors : DerivedCategory.Q ⋙ res ≅
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- Ordinary, `S_n`-linear, natural comparisons on cochain complexes. -/
  ordinary : ∀ n : ℕ,
    (restriction φ).mapHomologicalComplex (.up ℤ) ⋙
      (a n).E.mapHomologicalComplex (.up ℤ) ≅ (b n).E.mapHomologicalComplex (.up ℤ)
  /-- The ordinary comparison sends `s ⊗ p` to the same pure section. -/
  ordinary_sections : ∀ (n : ℕ) (P : CochainComplex (Modules B) ℤ) (i : ℤ)
    (U : Cᵒᵖ) (s : (D.S.obj (op n)).obj.obj U) (p : (P.X i).val.obj U),
    (((ordinary n).hom.app P).f i).val.app U
      (scalarSection (a n) ((restriction φ).obj (P.X i)) U s p) =
        scalarSection (b n) (P.X i) U s p
  /-- The induced natural derived comparisons. -/
  derived : ∀ n : ℕ, res ⋙ (a n).T ≅ (b n).T
  /-- Their canonical representative normalization, using the existing derived counits. -/
  computes : ∀ (n : ℕ) (P : CochainComplex (Modules B) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
      (derived n).hom.app (DerivedCategory.Q.obj P) ≫ (b n).ε.app P =
        (a n).T.map (resFactors.hom.app P) ≫
          (a n).ε.app (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((ordinary n).hom.app P)
  /-- One flat-term K-flat representative works simultaneously at every level. -/
  representatives : ∀ M : DerivedCategory (Modules B),
    ∃ P : CochainComplex (Modules B) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B) P ∧
      (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ M)
  /-- The strict tower comparisons, their transition formulas and their quotient cones. -/
  strict : ∀ P : CochainComplex (Modules B) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := B) P →
    (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) →
    ∃ (tL : ∀ n : ℕ, leftLevel D a (n + 1) P ⟶ leftLevel D a n P)
      (tR : ∀ n : ℕ, rightLevel D b (n + 1) P ⟶ rightLevel D b n P)
      (e : Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL ≅
        Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR)
      (ηL : (Functor.const ℕᵒᵖ).obj
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Functor.ofOpSequence (X := fun n ↦ leftLevel D a n P) tL)
      (ηR : (Functor.const ℕᵒᵖ).obj
          (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) ⟶
        Functor.ofOpSequence (X := fun n ↦ rightLevel D b n P) tR),
      (∀ n : ℕ, e.hom.app (op n) =
        ((restriction (D.projection n)).mapHomologicalComplex (.up ℤ)).map
          ((ordinary n).hom.app P)) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op (n + 1))).obj.obj U) (p : (P.X i).val.obj U),
        ((tL n).f i).val.app U
          (scalarSection (a (n + 1)) ((restriction φ).obj (P.X i)) U s p) =
            scalarSection (a n) ((restriction φ).obj (P.X i)) U
              ((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s) p) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
        (s : (D.S.obj (op (n + 1))).obj.obj U) (p : (P.X i).val.obj U),
        ((tR n).f i).val.app U (scalarSection (b (n + 1)) (P.X i) U s p) =
          scalarSection (b n) (P.X i) U
            ((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s) p) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (p : (P.X i).val.obj U),
        (((ηL.app (op n)).f i).val.app U p =
          scalarSection (a n) ((restriction φ).obj (P.X i)) U 1 p) ∧
        (((ηR.app (op n)).f i).val.app U p = scalarSection (b n) (P.X i) U 1 p)) ∧
      (ηL ≫ e.hom = ηR) ∧
      (∀ (n : ℕ) (i : ℤ), Epi ((ηL.app (op n)).f i)) ∧
      (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (p : (P.X i).val.obj U),
        ((ηL.app (op n)).f i).val.app U p = 0 ↔
          D.locallyInIdealProduct n ((restriction φ).obj (P.X i)) U p)

attribute [local semireducible] scalarSection

omit [HasDerivedCategory.{wR} (Modules R)] in
private theorem flat_representatives (M : DerivedCategory (Modules B)) :
    ∃ P : CochainComplex (Modules B) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B) P ∧
      (∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let G := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨P, f, hP, hterms, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := B) G
  have := hf
  refine ⟨P, hP, ?_, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e⟩⟩
  intro i
  let := isMonoidal_W_independentCoefficients B
  let := monoidalCategory B
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight (P.X i)) := (hterms i).1
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight (P.X i)) := (hterms i).2
  unfold IsFlatOnSite
  exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso B (P.X i)).symm,
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso B (P.X i)).symm⟩

end SheafOfModules.CommonQuotientReduction
