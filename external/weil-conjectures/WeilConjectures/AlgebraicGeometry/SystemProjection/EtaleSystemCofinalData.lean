/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCoefficientProjection
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.AlgebraicGeometry.System.SystemBlockRepetition
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemOrdinarySelectedExtension
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-! # Cofinal restriction and the compact-support adjunction mate

Source: Zheng, Construction 4.1 and Lemma 5.22, printed pp. 21 and 36;
the finite-block and arbitrary finite-coefficient extension in the DAG
(blueprint: lem-pur-etale-system-cofinal-mate).

The index n denotes positive level n+1. All categories are ordinary unbounded
localizations of actual strict systems. No cartesianness or flatness is imposed.
The auxiliary presentations specify canonical maps before evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a av b bv c cv d dv
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Restrict the coefficient tower, retaining its actual composite maps.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalCoefficients {l : ℕ} (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    Coefficients.{u} l where
  rings := r.toOrderHom.toFunctor.op ⋙ B.rings
  finite n := B.finite (r n)
  torsion n := B.torsion (r n)

/-- Reindex the sequence site by the given increasing function.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalSite (W : Scheme.{u}) (r : ℕ ↪o ℕ) : ℕ × W.Etale ⥤ ℕ × W.Etale :=
  r.toOrderHom.toFunctor.prod (𝟭 W.Etale)

/-- The canonical continuity witness.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
instance cofinalSiteContinuous (W : Scheme.{u}) (r : ℕ ↪o ℕ) :
    (cofinalSite W r).IsContinuous
      (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
      (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology) :=
  blockSite_continuous W.smallEtaleTopology r.toOrderHom

private theorem cofinalCoefficientRings (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    WeilConjectures.SemilinearSections.rings W.smallEtaleTopology
        (coefficients W B) (transitions W B) =
      B ⋙ constantSheaf W.smallEtaleTopology CommRingCat.{u + 1} := by
  let cmp : B ⋙ constantSheaf W.smallEtaleTopology CommRingCat.{u + 1} ⟶
      WeilConjectures.SemilinearSections.rings W.smallEtaleTopology
        (coefficients W B) (transitions W B) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, WeilConjectures.SemilinearSections.rings,
        Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id])
  symm
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  have hh := cmp.naturality f
  dsimp only [cmp] at hh
  simpa only [NatTrans.ofOpSequence_app, Category.id_comp, Category.comp_id] using hh

/-- The structural ring map for restriction is the identity at selected levels.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate).
Proof: unfold the sequence ring. The value at (i,U) is C_(r(i))(U) on both
sides. Functoriality identifies horizontal composites; vertical maps are unchanged. -/
theorem cofinalRing (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) :
    ((cofinalSite W r).sheafPushforwardContinuous RingCat.{u + 1}
      (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
      (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)).obj
        (ring _ (rings W B.rings)) = ring _ (rings W (cofinalCoefficients B r).rings) := by
  apply ObjectProperty.FullSubcategory.ext
  change (cofinalSite W r).op ⋙
      (ringPresheaf W.smallEtaleTopology (coefficients W B.rings)
        (transitions W B.rings) ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      ringPresheaf W.smallEtaleTopology (coefficients W (cofinalCoefficients B r).rings)
        (transitions W (cofinalCoefficients B r).rings) ⋙
          forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  dsimp only [ringPresheaf]
  rw [cofinalCoefficientRings W B.rings,
    cofinalCoefficientRings W (cofinalCoefficients B r).rings]
  rfl

/-- Actual restriction of module sheaves on the sequence site, including all maps.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalRestriction (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) : Modules W B.rings ⥤ Modules W (cofinalCoefficients B r).rings :=
  SheafOfModules.pushforward (F := cofinalSite W r) (eqToHom (cofinalRing W B r).symm)

private theorem cofinalPushforward_exact (W : Scheme.{u}) (r : ℕ ↪o ℕ)
    {S R : Sheaf (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
      RingCat.{u + 1}}
    (φ : S ⟶ ((cofinalSite W r).sheafPushforwardContinuous RingCat.{u + 1}
      (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
      (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)).obj R) :
    (SheafOfModules.pushforward.{u + 1} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{u + 1} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1} φ) := by
  let J := WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology
  refine ⟨⟨by intros; ext U x; rfl⟩, ?_, ?_⟩
  · let T := SheafOfModules.forget.{u + 1} S ⋙ PresheafOfModules.toPresheaf S.obj
    have : PreservesFiniteLimits (SheafOfModules.pushforward.{u + 1} φ ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (cofinalSite W r).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ T
  · let : (cofinalSite W r).IsCocontinuous J J := ⟨fun hS ↦ hS⟩
    let : ∀ (F : (ℕ × W.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
        (cofinalSite W r).op.HasPointwiseRightKanExtension F := fun F X ↦ by
      let : HasLimitsOfShape (StructuredArrow X (cofinalSite W r).op)
          AddCommGrpCat.{u + 1} := HasLimitsOfShape.of_essentiallySmall _ _
      infer_instance
    let H := (cofinalSite W r).sheafPushforwardContinuous AddCommGrpCat.{u + 1} J J
    have : PreservesColimitsOfSize.{0, 0} H :=
      ((cofinalSite W r).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        J J).leftAdjoint_preservesColimits
    let T := SheafOfModules.toSheaf.{u + 1} S
    have : PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1} φ ⋙ T) := by
      change PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} R ⋙ H)
      infer_instance
    have : ReflectsFiniteColimits T :=
      { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- Restriction is exact and additive because kernels, cokernels and addition are
componentwise. Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate).
Proof: restriction selects the same components in every finite diagram. Kernels
are termwise and cokernels are vertical sheafifications, which commute with selection. -/
theorem cofinalRestriction_exact (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) :
    (cofinalRestriction W B r).Additive ∧
      PreservesFiniteLimits (cofinalRestriction W B r) ∧
      PreservesFiniteColimits (cofinalRestriction W B r) := by
  exact cofinalPushforward_exact W r (eqToHom (cofinalRing W B r).symm)

/-- Additivity witness for exact localization.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
instance cofinalRestrictionAdditive (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) : (cofinalRestriction W B r).Additive :=
  (cofinalRestriction_exact W B r).1

/-- Finite-limit witness for exact localization.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
instance cofinalRestrictionLimits (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) : PreservesFiniteLimits (cofinalRestriction W B r) :=
  (cofinalRestriction_exact W B r).2.1

/-- Finite-colimit witness for exact localization.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
instance cofinalRestrictionColimits (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) : PreservesFiniteColimits (cofinalRestriction W B r) :=
  (cofinalRestriction_exact W B r).2.2

/-- Restriction on the ordinary unbounded derived categories.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
abbrev cofinalU (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :=
  (cofinalRestriction W B r).mapDerivedCategory

/-- K-flat representatives on the actual ringed sequence site.
Source: Zheng 4.1; Stacks 06YS (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalResolving (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (P : CochainComplex (Modules W B.rings) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := rings W B.rings) P

/-- The normalized right-adjoint comparison of the two composite adjunctions.
Source: Zheng 5.22 (blueprint: lem-pur-etale-system-cofinal-mate).
Its data are constructed by counit-compatible uniqueness, not chosen from existence. -/
def cofinalMate
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {LX : C ⥤ A} {UX : A ⥤ C} {LY : D ⥤ B} {UY : B ⥤ D}
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    (x : LX ⊣ UX) (y : LY ⊣ UY) (f : F ⊣ G) (g : F' ⊣ G')
    (h : LX ⋙ F ≅ F' ⋙ LY) : G ⋙ UX ≅ UY ⋙ G' :=
  (x.comp f).rightAdjointUniq ((g.comp y).ofNatIsoLeft h.symm)

/-- The ordinary coefficient functor on the small etale site.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
abbrev cofinalSheafRings (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l) :
    ℕᵒᵖ ⥤ Sheaf W.smallEtaleTopology CommRingCat.{u + 1} :=
  B.rings ⋙ constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}

/-- Identity-on-sections equivalence between the two recorded strict-system encodings.
This is presentation data for the same category, not a replacement notion of system.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalEncoding (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l) where
  equivalence : Modules W B.rings ≌
    SheafOfModules.StrictRingSystem.{u + 1, u, u + 1} (cofinalSheafRings W B)
  sections : ∀ (M : Modules W B.rings) (n : ℕ) (U : W.Etaleᵒᵖ),
    HEq (((equivalence.functor.obj M).level n).val.obj U)
      (M.val.obj (op (n, U.unop)))
  maps : ∀ {M N : Modules W B.rings} (f : M ⟶ N) (n : ℕ) (U : W.Etaleᵒᵖ),
    HEq (fun x ↦ (((equivalence.functor.map f).app n).val.app U) x)
      (fun x ↦ (f.val.app (op (n, U.unop))) x)
  transitions : ∀ (M : Modules W B.rings) {m n : ℕ} (h : m ≤ n) (U : W.Etaleᵒᵖ),
    HEq (fun x ↦ (((equivalence.functor.obj M).transition h).val.app U) x)
      (fun x ↦ M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)

/-- Termwise evaluation with the exactness witnesses of the recorded evaluation.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def Evaluation.cofinalComplex {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {n : ℕ}
    (e : Evaluation W B n) :=
  letI := e.additive
  (level W B n).mapHomologicalComplex (.up ℤ)

/-- The canonical exact-evaluation comparison on cochain representatives.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def Evaluation.cofinalFactor {W : Scheme.{u}} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {n : ℕ}
    (e : Evaluation W B n) : DerivedCategory.Q ⋙ e.E ≅
      e.cofinalComplex ⋙ DerivedCategory.Q :=
  letI := e.additive
  letI := e.limits
  letI := e.colimits
  (level W B n).mapDerivedCategoryFactors

/-- The ordinary selected tensor comparison on actual cochain representatives.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalLevelComplex {W : Scheme.{u}} {l : ℕ} {B : Coefficients.{u} l} {r : ℕ ↪o ℕ}
    (F : Modules W (cofinalCoefficients B r).rings ⥤ Modules W B.rings) [F.Additive]
    (m : ℕ) (eb : Evaluation W B.rings m)
    (er : Evaluation W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m))
    (o : F ⋙ level W B.rings m ≅
      level W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m) ⋙
        ProEtale.etaleSheafExtendScalars
          (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W)
    (P : CochainComplex (Modules W (cofinalCoefficients B r).rings) ℤ) :
    eb.cofinalComplex.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (Functor.mapHomologicalComplex (ProEtale.etaleSheafExtendScalars
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W)
          (.up ℤ)).obj (er.cofinalComplex.obj P) := by
  letI := eb.additive
  letI := er.additive
  exact (NatIso.mapHomologicalComplex o (.up ℤ)).app P

/-- Ordinary tensor-adjunction normalization at every selected level.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalOrdinaryLevelUnit {W : Scheme.{u}} {l : ℕ} {B : Coefficients.{u} l}
    {r : ℕ ↪o ℕ}
    (model : SheafOfModules.SystemDerivedLeftExtension (cofinalRestriction W B r)
      (cofinalResolving W (cofinalCoefficients B r)))
    (ordinaryLevel : ∀ m : ℕ,
      model.ordinary ⋙ level W B.rings m ≅
        level W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m) ⋙
          ProEtale.etaleSheafExtendScalars
            (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W) :
    Prop :=
  ∀ (m : ℕ) (N : Modules W (cofinalCoefficients B r).rings)
    (U : W.Etaleᵒᵖ),
    HEq ((((ProEtale.etaleSheafExtendScalarsAdjunction
      (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W).homEquiv
        _ _ ((ordinaryLevel m).inv.app N)).hom.app U).hom.toFun)
      (((model.ordinary.obj N).val.map
        (Prod.mkHom (homOfLE (SheafOfModules.systemNextSelected_spec r m).1)
          (𝟙 U.unop)).op).hom.toFun ∘
        ((model.ordinaryAdj.unit.app N).val.app
          (op (SheafOfModules.systemNextSelected r m, U.unop))).hom.toFun)

/-- Normalization of derived evaluation by its universal cochain comparison.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalLevelNormalization {W : Scheme.{u}} {l : ℕ} {B : Coefficients.{u} l}
    {r : ℕ ↪o ℕ}
    (model : SheafOfModules.SystemDerivedLeftExtension (cofinalRestriction W B r)
      (cofinalResolving W (cofinalCoefficients B r)))
    (ordinaryLevel : ∀ m : ℕ,
      model.ordinary ⋙ level W B.rings m ≅
        level W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m) ⋙
          ProEtale.etaleSheafExtendScalars
            (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W)
    (level : ∀ (m : ℕ) (eb : Evaluation W B.rings m)
      (er : Evaluation W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m)),
      model.derived ⋙ eb.E ≅ er.E ⋙ scalarExtension
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W) :
    Prop :=
  ∀ (m : ℕ) (eb : Evaluation W B.rings m)
    (er : Evaluation W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m))
    (P : CochainComplex (Modules W (cofinalCoefficients B r).rings) ℤ),
    (level m eb er).hom.app (DerivedCategory.Q.obj P) ≫
      (scalarExtension
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W).map
          (er.cofinalFactor.hom.app P) ≫
      scalarExtensionRepresentative
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W
          (er.cofinalComplex.obj P) =
      eb.E.map (model.comparison.app P) ≫
        eb.cofinalFactor.hom.app ((model.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (cofinalLevelComplex model.ordinary m eb er (ordinaryLevel m) P).hom

/-- A selected left extension on the sequence-site encoding. Its ordinary functor
is identified with the recorded selected extension, so all transitions and tensor
associators, including repeated least indices, are retained before derivation.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalExtension (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) where
  base : CofinalEncoding W B
  selected : CofinalEncoding W (cofinalCoefficients B r)
  theory : SheafOfModules.SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
    (J := W.smallEtaleTopology)
  model : SheafOfModules.SystemDerivedLeftExtension (cofinalRestriction W B r)
    (cofinalResolving W (cofinalCoefficients B r))
  ordinary : model.ordinary ⋙ base.equivalence.functor ≅
    selected.equivalence.functor ⋙ (theory.selected (cofinalSheafRings W B) r).ordinary
  ordinaryLevel : ∀ m : ℕ,
    model.ordinary ⋙ level W B.rings m ≅
      level W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m) ⋙
        ProEtale.etaleSheafExtendScalars
          (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W
  ordinaryLevel_unit : cofinalOrdinaryLevelUnit (W := W) (B := B) (r := r) model ordinaryLevel
  level : ∀ (m : ℕ) (eb : Evaluation W B.rings m)
    (er : Evaluation W (cofinalCoefficients B r).rings (SheafOfModules.systemNextSelected r m)),
    model.derived ⋙ eb.E ≅ er.E ⋙ scalarExtension
      (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom W
  level_normalization : cofinalLevelNormalization (W := W) (B := B) (r := r)
    model ordinaryLevel level

/-- Cofinal restriction composition, normalized by the identity on selected sections.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalComposition (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r s : ℕ ↪o ℕ) where
  ordinary : cofinalRestriction W B r ⋙
      cofinalRestriction W (cofinalCoefficients B r) s ≅
    cofinalRestriction W B (s.trans r)
  sections : ∀ (M : Modules W B.rings) (n : ℕ) (U : W.Etaleᵒᵖ)
    (x : ((cofinalRestriction W (cofinalCoefficients B r) s).obj
      ((cofinalRestriction W B r).obj M)).val.obj (op (n, U.unop))),
    HEq (((ordinary.hom.app M).val.app (op (n, U.unop))) x) x

/-- Derived restriction composition is the exact localization of the ordinary compositor.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def CofinalComposition.derived {W : Scheme.{u}} {l : ℕ} {B : Coefficients.{u} l}
    {r s : ℕ ↪o ℕ} (a : CofinalComposition W B r s) :
    cofinalU W B r ⋙ cofinalU W (cofinalCoefficients B r) s ≅
      cofinalU W B (s.trans r) := Functor.mapDerivedCategoryCompNatIso a.ordinary

/-- The least-selected index as a monotone map, including constant finite blocks.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalNext (r : ℕ ↪o ℕ) : ℕ →o ℕ :=
  ⟨SheafOfModules.systemNextSelected r, fun _ _ h ↦
    SheafOfModules.systemNextSelected_monotone r h⟩

/-- The intermediate tower D_m=C_(r(t(m))).
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalRepeated {l : ℕ} (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    Coefficients.{u} l where
  rings := (cofinalNext r).toFunctor.op ⋙ (cofinalCoefficients B r).rings
  finite n := B.finite (r (SheafOfModules.systemNextSelected r n))
  torsion n := B.torsion (r (SheafOfModules.systemNextSelected r n))

/-- Naturality of the selected quotient transitions D_m→C_m.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate).
Proof: both composites are the ring map of B for the unique inequality
m≤r(t(n)); use functoriality and monotonicity of t. -/
theorem cofinalCoefficient_naturality {l : ℕ} (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (cofinalRepeated B r).rings.map f ≫
        B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r n.unop).1).op =
      B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m.unop).1).op ≫
        B.rings.map f := by
  change B.rings.map _ ≫ B.rings.map _ = B.rings.map _ ≫ B.rings.map _
  rw [← B.rings.map_comp, ← B.rings.map_comp]
  congr 1

/-- The actual map D→C, not an unspecified coefficient morphism.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalCoefficient {l : ℕ} (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) :
    (cofinalRepeated B r).rings ⟶ B.rings where
  app m := B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m.unop).1).op
  naturality := fun _ _ f ↦ cofinalCoefficient_naturality B r f

/-- Repetition at t(m), specified on module sections, all restrictions and maps.
These data specify the actual block functor of the recorded block-repetition lemma.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalRepeat (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l)
    (r : ℕ ↪o ℕ) where
  R : Modules W (cofinalCoefficients B r).rings ⥤ Modules W (cofinalRepeated B r).rings
  [additive : R.Additive]
  [limits : PreservesFiniteLimits R]
  [colimits : PreservesFiniteColimits R]
  sections : ∀ (M : Modules W (cofinalCoefficients B r).rings) (n : ℕ) (U : W.Etaleᵒᵖ),
    HEq ((R.obj M).val.obj (op (n, U.unop)))
      (M.val.obj (op (SheafOfModules.systemNextSelected r n, U.unop)))
  maps : ∀ {M N : Modules W (cofinalCoefficients B r).rings} (f : M ⟶ N)
    (n : ℕ) (U : W.Etaleᵒᵖ),
    HEq (fun x ↦ ((R.map f).val.app (op (n, U.unop))) x)
      (fun x ↦ (f.val.app (op (SheafOfModules.systemNextSelected r n, U.unop))) x)
  restrictions : ∀ (M : Modules W (cofinalCoefficients B r).rings)
    {U V : (ℕ × W.Etale)ᵒᵖ} (f : U ⟶ V),
    HEq (fun x ↦ (R.obj M).val.map f x)
      (fun x ↦ M.val.map (((cofinalNext r).toFunctor.prod (𝟭 W.Etale)).map f.unop).op x)

attribute [instance] CofinalRepeat.additive CofinalRepeat.limits CofinalRepeat.colimits

/-- Normalized geometric repetition on the fixed compactification, before localization.
The derived comparison is built by the universal derived functor construction below.
Source: Zheng 4.1, paragraph before 4.10
(blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalRepeatSupport {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {l : ℕ} (T : Theory c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) where
  x : CofinalRepeat X B r
  z : CofinalRepeat c.Z B r
  y : CofinalRepeat Y B r
  [kinjectives : z.R.PreservesKInjectiveComplexes]
  proper : z.R ⋙ (T.support (cofinalRepeated B r)).proper.toDirectImage.push ≅
    (T.support (cofinalCoefficients B r)).proper.toDirectImage.push ⋙ y.R
  proper_sections : ∀ (M : Modules c.Z (cofinalCoefficients B r).rings)
    (U : (ℕ × Y.Etale)ᵒᵖ)
    (a : ((z.R ⋙ (T.support (cofinalRepeated B r)).proper.toDirectImage.push).obj M).val.obj U),
    HEq (((proper.hom.app M).val.app U) a) a
  openImage : x.R ⋙ (T.support (cofinalRepeated B r)).openImage.extension ≅
    (T.support (cofinalCoefficients B r)).openImage.extension ⋙ z.R
  open_sections : ∀ (M : Modules X (cofinalCoefficients B r).rings)
    (U : (ℕ × c.Z.Etale)ᵒᵖ)
    (a : ((x.R ⋙ (T.support (cofinalRepeated B r)).openImage.extension).obj M).val.obj U),
    HEq (((openImage.hom.app M).val.app U) a) a

/-- The canonical kappa for repetition: exact open comparison followed by the
universal total-right-derived proper comparison. It is specified before evaluation.
Source: Zheng 4.1, paragraph before 4.10
(blueprint: lem-pur-etale-system-cofinal-mate). -/
def CofinalRepeatSupport.kappa {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {l : ℕ} {T : Theory c l} {B : Coefficients.{u} l} {r : ℕ ↪o ℕ}
    (a : CofinalRepeatSupport T B r) :
    a.x.R.mapDerivedCategory ⋙ (T.support (cofinalRepeated B r)).F ≅
      (T.support (cofinalCoefficients B r)).F ⋙ a.y.R.mapDerivedCategory := by
  letI := (T.support (cofinalRepeated B r)).openImage.extensionAdditive
  letI := (T.support (cofinalRepeated B r)).openImage.extensionLimits
  letI := (T.support (cofinalRepeated B r)).openImage.extensionColimits
  letI := (T.support (cofinalCoefficients B r)).openImage.extensionAdditive
  letI := (T.support (cofinalCoefficients B r)).openImage.extensionLimits
  letI := (T.support (cofinalCoefficients B r)).openImage.extensionColimits
  letI := (T.support (cofinalRepeated B r)).proper.pushAdditive
  letI := (T.support (cofinalCoefficients B r)).proper.pushAdditive
  letI := (T.support (cofinalRepeated B r)).proper.kinjectives
  letI := (T.support (cofinalCoefficients B r)).proper.kinjectives
  letI := a.kinjectives
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso a.openImage)
      (T.support (cofinalRepeated B r)).proper.R ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T.support (cofinalCoefficients B r)).openImage.J
      (blockDerivedComparison a.z.R a.y.R
        (T.support (cofinalCoefficients B r)).proper.toDirectImage.push
        (T.support (cofinalRepeated B r)).proper.toDirectImage.push a.proper) ≪≫
    (Functor.associator _ _ _).symm

/-- The selected-extension/repetition-factor comparison, fixed both on ordinary
units and by the total-left-derived universal counit, before taking evaluations.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalFactor (W : Scheme.{u}) {l : ℕ} (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    (L : CofinalExtension W B r) (R : CofinalRepeat W B r)
    (S : Scalar W (cofinalCoefficient B r)) where
  ordinary : L.model.ordinary ≅ R.R ⋙ S.model.E
  ordinary_unit : ∀ (N : Modules W (cofinalCoefficients B r).rings)
    (i : ℕ) (U : W.Etaleᵒᵖ),
    HEq (fun x ↦ ((L.model.ordinaryAdj.unit.app N ≫
      (cofinalRestriction W B r).map (ordinary.hom.app N)).val.app (op (i, U.unop))) x)
      (fun x ↦ ((S.ordinaryAdj.unit.app (R.R.obj N)).val.app (op (r i, U.unop))) x)
  derived : L.model.derived ≅ R.R.mapDerivedCategory ⋙ S.model.T
  normalization : ∀ P : CochainComplex (Modules W (cofinalCoefficients B r).rings) ℤ,
    L.model.comparison.app P ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      S.model.T.map (R.R.mapDerivedCategoryFactors.hom.app P) ≫
      S.model.ε.app ((R.R.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (R.R ⋙ S.model.E)) (.up ℤ)).inv.app P)

/-- A coherent family of selected extensions and the normalized support comparison.
All support functors come from the recorded projection theory on the fixed compactification.
Source: Zheng 4.1, 5.22 (blueprint: lem-pur-etale-system-cofinal-mate). -/
structure CofinalSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (l : ℕ) where
  projection : Theory c l
  extensionX : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ), CofinalExtension X B r
  extensionY : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ), CofinalExtension Y B r
  compositionX : ∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ), CofinalComposition X B r s
  compositionY : ∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ), CofinalComposition Y B r s
  repetition : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ),
    CofinalRepeatSupport projection B r
  factorX : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ),
    CofinalFactor X B r (extensionX B r) (repetition B r).x
      (projection.scalarX (cofinalCoefficient B r))
  factorY : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ),
    CofinalFactor Y B r (extensionY B r) (repetition B r).y
      (projection.scalarY (cofinalCoefficient B r))
  h : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ),
    (extensionX B r).model.derived ⋙ (projection.support B).F ≅
      (projection.support (cofinalCoefficients B r)).F ⋙ (extensionY B r).model.derived
  normalization : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    (N : Derived X (cofinalCoefficients B r).rings),
    (projection.q (cofinalCoefficient B r)).app
        ((repetition B r).x.R.mapDerivedCategory.obj N) ≫
      (projection.support B).F.map ((factorX B r).derived.inv.app N) ≫
      (h B r).hom.app N ≫ (factorY B r).derived.hom.app
        ((projection.support (cofinalCoefficients B r)).F.obj N) =
      (projection.scalarY (cofinalCoefficient B r)).model.T.map
        ((repetition B r).kappa.hom.app N)
  evaluation : ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ) (m : ℕ)
    (N : Derived X (cofinalCoefficients B r).rings),
    ((projection.evaluationY B m).E).map ((h B r).hom.app N) ≫
      ((extensionY B r).level m (projection.evaluationY B m)
        (projection.evaluationY (cofinalCoefficients B r)
          (SheafOfModules.systemNextSelected r m))).hom.app
            ((projection.support (cofinalCoefficients B r)).F.obj N) ≫
      (scalarExtension
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom Y).map
          ((projection.supportEvaluation (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).iso.hom.app N) ≫
      (compactScalarMap
        (B.rings.map (homOfLE (SheafOfModules.systemNextSelected_spec r m).1).op).hom c).app
          ((projection.evaluationX (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m)).E.obj N) =
    (projection.supportEvaluation B m).iso.hom.app
      ((extensionX B r).model.derived.obj N) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (B.rings.obj (op m))) c).map
        (((extensionX B r).level m (projection.evaluationX B m)
          (projection.evaluationX (cofinalCoefficients B r)
            (SheafOfModules.systemNextSelected r m))).hom.app N)

/-- The actual right-adjoint mate for any fixed compact-support adjunctions.
Source: Zheng 5.22 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def CofinalSupport.rho {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {l : ℕ} (t : CofinalSupport c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    {G : Derived Y B.rings ⥤ Derived X B.rings}
    {H : Derived Y (cofinalCoefficients B r).rings ⥤ Derived X (cofinalCoefficients B r).rings}
    (a : (t.projection.support B).F ⊣ G)
    (b : (t.projection.support (cofinalCoefficients B r)).F ⊣ H) :
    G ⋙ cofinalU X B r ≅ cofinalU Y B r ⋙ H :=
  cofinalMate (t.extensionX B r).model.adjunction (t.extensionY B r).model.adjunction
    a b (t.h B r)

end AlgebraicGeometry.Etale.SystemProjection
