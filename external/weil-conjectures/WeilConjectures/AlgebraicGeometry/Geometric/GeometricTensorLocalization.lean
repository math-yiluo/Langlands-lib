/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryTensor
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorEvaluation
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
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

/-! # Tensor localization for a fixed ordinary geometric realization

Source: Zheng Construction 4.1; Stacks 06YY and 07A4.
(blueprint: lem-coef-semilinear-geometric-tensor-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory SheafOfModules.CanonicalTensorPullbackProof
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

-- The ordinary-to-derived construction, using the existing signed-total and
-- representative descent APIs. Kept private here to avoid a geometric-existence
-- import cycle in the public general constructor.
private theorem geometryInverseChain
    {E : Type a} [Category.{b} E] {X₀ X₁ X₂ X₃ X₄ X₅ : E}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄)
    (q : X₄ ⟶ X₅) (w : X₀ ⟶ X₅)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ q = w) :
    d.inv ≫ c.inv ≫ b.inv ≫ a.inv ≫ w = q := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

@[irreducible] private noncomputable def geometryExactTensorTotalIso
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    {B : Type a} [Category.{b} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) :
    ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor B).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ≅
      Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) := by
  have (P Q : CochainComplex A ℤ) : IsIso (tensorPullbackTotal L μ hn P Q) :=
    tensorPullbackTotal_isIso L μ hn V adj P Q
  exact NatIso.ofComponents (fun Z ↦ asIso (tensorPullbackTotal L μ hn Z.1 Z.2)) (by
    intro Z Z' f
    simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
    exact tensorPullbackTotal_naturality L μ hn f.1 f.2)

private theorem geometryExactTensorTotalIso_hom_app
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    {B : Type a} [Category.{b} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) (P Q : CochainComplex A ℤ) :
    (geometryExactTensorTotalIso L μ hn V adj).hom.app (P, Q) = tensorPullbackTotal L μ hn P Q := by
  unfold geometryExactTensorTotalIso
  rfl

private noncomputable def geometryResolvingQQFullyFaithful
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
    (E : Type ((max c v r) + 1)) [Category.{(max c v r) + 1} E] :
    let P : ObjectProperty (CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :=
      fun P ↦ P.IsKFlatIndependentCoefficients ∧ flatTerms.{c, v, r} J R P
    (((Functor.whiskeringLeft _ _ E).obj
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)))).FullyFaithful := by
  let W := (Functor.whiskeringLeft _ _ E).obj
    (((SheafOfModules.cochainTensorFlatRepresentatives J R).ι ⋙ DerivedCategory.Q).prod
      ((SheafOfModules.cochainTensorFlatRepresentatives J R).ι ⋙ DerivedCategory.Q))
  have h := (SheafOfModules.cochain_tensor_model_rigidity J R).choose_spec.2.2
  exact ((Functor.FullyFaithful.nonempty_iff_map_bijective W).2
    (h E inferInstance)).some

section GeometricTensorConstruction
attribute [local irreducible] SheafOfModules.monoidalCategory
variable {C₀ C₁ : Type c} [Category.{v} C₀] [Category.{v} C₁]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (R : Sheaf J₀ CommRingCat.{max c v r}) (S : Sheaf J₁ CommRingCat.{max c v r})

private theorem geometryModelOfOrdinary
    (F : Mod.{c, v, max c v r} J₀ R ⥤
      Mod.{c, v, max c v r} J₁ S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : Mod.{c, v, max c v r} J₁ S ⥤
      Mod.{c, v, max c v r} J₀ R) (adj : F ⊣ G)
    (A : Closed.{c, v, r} J₀ R)
    (B : Closed.{c, v, r} J₁ S)
    (TA : Models.{c, v, r} J₀ R A)
    (TB : Models.{c, v, r} J₁ S B)
    (e : ∀ M N : Mod.{c, v, max c v r} J₀ R,
      F.obj (ordinaryTensor.{c, v, r} J₀ R M N) ≅
        ordinaryTensor.{c, v, r} J₁ S (F.obj M) (F.obj N))
    (he : ∀ {M M' N N' : Mod.{c, v, max c v r} J₀ R} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (ordinaryTensorHom.{c, v, r} J₀ R a b) ≫ (e M' N').hom =
        (e M N).hom ≫ ordinaryTensorHom.{c, v, r} J₁ S (F.map a) (F.map b))
    (hk : ∀ P : CochainComplex (Mod.{c, v, max c v r} J₀ R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J₀) (R := R) P →
      flatTerms.{c, v, r} J₀ R P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J₁) (R := S)
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ mu : A.tensor ⋙ F.mapDerivedCategory ≅
        (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor,
      ∃ model : TensorComparisonModel.{c, v, r} J₀ J₁ R S F A B TA TB mu,
        model.ordinary = e := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let P : ObjectProperty (CochainComplex (Mod.{c, v, max c v r} J₀ R) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧ flatTerms.{c, v, r} J₀ R P
  let Q : ObjectProperty (CochainComplex (Mod.{c, v, max c v r} J₁ S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let i : P.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J₀) (R := R)) :=
    ObjectProperty.ιOfLE (fun _ h ↦ h.1)
  let r : (P.ι.prod P.ι) ⋙ totalTensor.{c, v, r} J₀ R ⋙ DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ A.tensor :=
    Functor.isoWhiskerLeft (i.prod i) TA.comparison
  let H := F.mapHomologicalComplex (.up ℤ)
  have hH : ∀ X, P X → Q (H.obj X) := fun X h ↦ hk X h.1 h.2
  have hn {M M' N N' : Mod.{c, v, max c v r} J₀ R}
      (b : M ⟶ M') (d : N ⟶ N') :
      F.map (b ⊗ₘ d) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map b ⊗ₘ F.map d) := he b d
  let beta : (H.prod H) ⋙ totalTensor.{c, v, r} J₁ S ≅
      totalTensor.{c, v, r} J₀ R ⋙ H := geometryExactTensorTotalIso F e hn G adj
  obtain ⟨mu, hmu, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q H F.mapDerivedCategory
    (Functor.mapDerivedCategoryFactors F).hom P Q hH
    (geometryResolvingQQFullyFaithful.{c, v, r} J₀ R (DerivedCategory (Mod J₁ S)))
    (totalTensor.{c, v, r} J₀ R) (totalTensor.{c, v, r} J₁ S)
    A.tensor B.tensor r TB.comparison beta.symm
    (fun _ _ ↦ by infer_instance) (fun _ _ _ _ ↦ by infer_instance)
  refine ⟨mu, {
    ordinary := e
    chain := fun X Y ↦ beta.hom.app (X, Y)
    summand := ?_
    kflat := hk
    derived := ?_
  }, rfl⟩
  · intro X Y p q k h
    rw [geometryExactTensorTotalIso_hom_app]
    dsimp only [tensorPullbackTotal, tensorPullbackTotalComponent, tensorSummand]
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  · intro X Y hx hy hfx hfy
    have hpx : P X := ⟨hx, hfx⟩
    have hpy : P Y := ⟨hy, hfy⟩
    have hm := hmu X Y hpx hpy
    change F.mapDerivedCategory.map (tensorModelIso.{c, v, r} J₀ R A TA X Y hx hy).hom ≫
        mu.hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ≫
        B.tensor.map (Prod.mkHom ((Functor.mapDerivedCategoryFactors F).hom.app X)
          ((Functor.mapDerivedCategoryFactors F).hom.app Y)) =
      (Functor.mapDerivedCategoryFactors F).hom.app ((totalTensor.{c, v, r} J₀ R).obj (X, Y)) ≫
        DerivedCategory.Q.map (beta.inv.app (X, Y)) ≫
        (tensorModelIso.{c, v, r} J₁ S B TB (H.obj X) (H.obj Y)
          (hH X hpx) (hH Y hpy)).hom at hm
    have hm' := congrArg (fun f ↦ f ≫
      (tensorModelIso.{c, v, r} J₁ S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).inv ≫
        DerivedCategory.Q.map (beta.hom.app (X, Y))) hm
    have hi : DerivedCategory.Q.map (beta.inv.app (X, Y)) ≫
        DerivedCategory.Q.map (beta.hom.app (X, Y)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← NatTrans.comp_app, beta.inv_hom_id, NatTrans.id_app]
      exact CategoryTheory.Functor.map_id _ _
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at hm'
    rw [hi] at hm'
    have hm'' := hm'.trans (Category.comp_id _)
    have h := geometryInverseChain
      (F.mapDerivedCategory.mapIso
        (tensorModelIso.{c, v, r} J₀ R A TA X Y hx hy))
      (mu.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y))
      (B.tensor.mapIso (Iso.prod ((Functor.mapDerivedCategoryFactors F).app X)
        ((Functor.mapDerivedCategoryFactors F).app Y)))
      (tensorModelIso.{c, v, r} J₁ S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).symm
      (DerivedCategory.Q.map (beta.hom.app (X, Y)))
      ((Functor.mapDerivedCategoryFactors F).hom.app
        ((totalTensor.{c, v, r} J₀ R).obj (X, Y)))
      (by simpa only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
        Iso.symm_hom] using hm'')
    simpa only [H, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv, Iso.symm_inv] using h

end GeometricTensorConstruction

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (A : Data.{c, v, r} J B τ)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)

/-- The system and level tensor comparisons on the specified total-complex models.
No direct image, derived adjunction, or scalar comparison is part of this interface.
Source: Zheng Construction 4.1; Stacks 06YY and 07A4.
(blueprint: lem-coef-semilinear-geometric-tensor-localization). -/
structure GeometryTensor where
  /-- The canonical tensor comparison for inverse image of systems. -/
  tensorPullback : A.closed.tensor ⋙ O.pull.mapDerivedCategory ≅
    (O.pull.mapDerivedCategory.prod O.pull.mapDerivedCategory) ⋙ target.closed.tensor
  /-- Tensor/inverse-image comparison at each actual coefficient level. -/
  levelTensorPullback : ∀ n : ℕ,
    (A.levelClosed n).tensor ⋙
        derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules).prod
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules)) ⋙ (target.levelClosed n).tensor
  /-- The tensor comparison evaluates to the specified level comparison. -/
  tensorPullback_evaluation : ∀ (n : ℕ) (M P : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (tensorPullback.hom.app (M, P)) ≫
        (target.tensorEvaluation n).hom.app
          (O.pull.mapDerivedCategory.obj M, O.pull.mapDerivedCategory.obj P) ≫
        (target.levelClosed n).tensor.map
          (Prod.mkHom (((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).hom.app M)
            (((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).hom.app P)) =
      ((geometryPullEvaluation J B τ J' uInv uPush adjSet O) n).hom.app (A.closed.tensor.obj (M, P))
        ≫
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (O.coefficients n) (O.inverseImage n).modules).map
            ((A.tensorEvaluation n).hom.app (M, P)) ≫
        (levelTensorPullback n).hom.app
          ((e.{c, v, max c v r} J B τ n).obj M, (e.{c, v, max c v r} J B τ n).obj P)
  /-- Level tensor pullback is fixed on the signed total K-flat representatives. -/
  levelTensorModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r} J J' (B n) (O.coefficients n) (O.inverseImage n).modules
      (A.levelClosed n) (target.levelClosed n) (A.levelTensorModels n)
        (target.levelTensorModels n) (levelTensorPullback n)
  /-- Its ordinary maps are the inverse images of pure tensors. -/
  levelTensor_pure : ∀ n : ℕ,
    InverseTensorPure.{c, v, r} J J' uInv (B n) (O.coefficients n) (O.inverseImage n)
      (levelTensorModel n).ordinary
  /-- The system comparison is localized on the system category itself. -/
  tensorModel : TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J)
    (coefficientSequenceTopology J') (systemRing.{c, v, max c v r} J B τ)
      (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition) O.pull A.closed
        target.closed
        A.tensorModels target.tensorModels tensorPullback
  /-- The ordinary system tensor map is fixed by ordinary, faithful evaluations. -/
  tensor_ordinary_evaluation : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (tensorModel.ordinary M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n (O.pull.obj M)
        (O.pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.ordinaryPullEvaluation n).hom.app M) ((O.ordinaryPullEvaluation n).hom.app N) =
      (O.ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J
          B τ) M N) ≫
      (O.inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      ((levelTensorModel n).ordinary ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom

/-- Localization of the ordinary inverse-image pure-tensor comparison.
Source: Zheng Construction 4.1; Stacks 06YY and 07A4.
(blueprint: lem-coef-semilinear-geometric-tensor-localization).

Proof: on ordinary module sheaves the inverse-image tensor comparison is fixed by
sending the inverse image of a pure tensor to the tensor of the inverse images of
its factors. The universal balanced bilinear map constructs it and the inverse;
the inverse equations follow on pure tensors and then by module sheafification.
Apply the same construction on the sequence site, using the actual horizontal
transitions of O. Ordinary evaluation is faithful on systems. Its identity on
component carriers and the pure-tensor normalization of ordinaryEvaluationTensor
therefore give the displayed ordinary evaluation square. In degree k of the signed
total tensor take the sum of these ordinary comparisons over p+q=k. Naturality
makes the maps commute with the first differential and with the signed second
differential. Their ordinary inverses induce the inverse cochain maps.
Inverse image preserves flat-term K-flat complexes. Restrict the construction to
such representatives of the given source tensor models. The fixed source and
target model comparisons now descend these chain isomorphisms along localization.
The defining descent square supplies TensorComparisonModel. The system and level
comparisons have the displayed derived evaluation square because the corresponding
ordinary square holds on every total summand; localization uniqueness proves the
whole square. Equality is established before evaluating derived maps. -/
theorem semilinearGeometryTensor [PreservesFiniteLimits uInv] :
    Nonempty (GeometryTensor.{c, v, r} J B τ J' uInv uPush adjSet A O target) := by
  classical
  obtain ⟨ordinary⟩ := geometricOrdinaryTensor_exists.{c, v, r}
    J B τ J' uInv uPush adjSet O
  obtain ⟨mu, model, hmodel⟩ := geometryModelOfOrdinary.{c, v, r}
    (coefficientSequenceTopology J) (coefficientSequenceTopology J')
    (systemRing.{c, v, max c v r} J B τ)
    (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
    O.pull O.push O.ordinaryAdjunction A.closed target.closed A.tensorModels target.tensorModels
    ordinary.system ordinary.system_natural ordinary.system_kflat
  have levels (n : ℕ) := geometryModelOfOrdinary.{c, v, r}
    J J' (B n) (O.coefficients n) (O.inverseImage n).modules
    (O.levelPush n) (O.levelAdjunction n) (A.levelClosed n) (target.levelClosed n)
    (A.levelTensorModels n) (target.levelTensorModels n)
    (ordinary.level n) (ordinary.level_natural n) (ordinary.level_kflat n)
  choose levelMu levelModel hlevel using levels
  have hpure (n : ℕ) : InverseTensorPure.{c, v, r} J J' uInv
      (B n) (O.coefficients n) (O.inverseImage n) (levelModel n).ordinary := by
    rw [hlevel n]
    exact ordinary.level_pure n
  have heval : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
      (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (model.ordinary M N).hom ≫
        (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
          (O.pull.obj M) (O.pull.obj N)).hom ≫
        ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
          ((O.ordinaryPullEvaluation n).hom.app M) ((O.ordinaryPullEvaluation n).hom.app N) =
        (O.ordinaryPullEvaluation n).hom.app
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, max c v r} J B τ) M N) ≫
          (O.inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
          ((levelModel n).ordinary ((evaluation.{c, v, max c v r} J B τ n).obj M)
            ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom := by
    intro n M N
    rw [hmodel, hlevel n]
    exact ordinary.evaluation n M N
  exact ⟨{
    tensorPullback := mu
    levelTensorPullback := levelMu
    tensorPullback_evaluation := geometricTensorEvaluation.{c, v, r}
      J B τ J' uInv uPush adjSet A O target mu levelMu levelModel model heval
    levelTensorModel := levelModel
    levelTensor_pure := hpure
    tensorModel := model
    tensor_ordinary_evaluation := heval }⟩

end WeilConjectures.SemilinearSections
