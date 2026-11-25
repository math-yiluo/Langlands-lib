/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteOrdinaryHomComparison
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
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
import WeilConjectures.SixFunctors.Supporting.RingedSiteHomComponentProjection
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceTensorConstraints
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceScalarUnit
import WeilConjectures.CategoryTheory.Ringed.RingedSignedBidualLocalization
import WeilConjectures.CategoryTheory.Ringed.RingedOrdinaryEvaluationLocalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
/-! # Canonical coefficient-duality maps on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08JD, 08JE, 0A97 and 0A98
(blueprint: lem-sfb-ringed-site-duality-maps).
The existing closed tensor-Hom representative model pins transposition to actual
sheafified pure tensors. The unit, associator and symmetry below are pinned to
ordinary complexes as well. No perfectness or invertibility is part of this model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w w' a b x y
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory

section Closed
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : WeilConjectures.CoefficientClosedStructure H)
  (s : @SymmetricCategory D _ S.monoidal)
  (O : D) (u : S.monoidal.tensorUnit ≅ O)

/-- Transpose of coefficient evaluation after Koszul interchange.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteBidual (P : D) : P ⟶ H.obj (op (H.obj (op P, O)), O) :=
  S.transpose P (H.obj (op P, O)) O
    ((s.braiding P (H.obj (op P, O))).hom ≫ S.evaluation P O)

/-- The canonical comparison, defined by transposing composite evaluations.
Its source is N tensor the dual; symmetry gives the order in perfect duality.
Source: Stacks 08JD, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluation (P N : D) :
    S.tensor.obj (N, H.obj (op P, O)) ⟶ H.obj (op P, N) :=
  S.transpose _ P N
    ((S.monoidal.associator N (H.obj (op P, O)) P).hom ≫
      S.tensor.map (Prod.mkHom (𝟙 N) (S.evaluation P O)) ≫
      S.tensor.map (Prod.mkHom (𝟙 N) u.inv) ≫ (S.monoidal.rightUnitor N).hom)

/-- Naturality of the actual evaluation comparison in the second variable.
Source: Stacks 08JD, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose both sides. Naturality of the associator, tensor, right unitor,
and the adjunction counit makes the resulting composite evaluations equal. -/
theorem ringedSiteDualEvaluation_naturality (P : D) {N N' : D} (f : N ⟶ N') :
    S.tensor.map (Prod.mkHom f (𝟙 (H.obj (op P, O)))) ≫
        ringedSiteDualEvaluation S O u P N' =
      ringedSiteDualEvaluation S O u P N ≫ H.map (Prod.mkHom (𝟙 (op P)) f) := by
  let _ := S.monoidal
  unfold ringedSiteDualEvaluation WeilConjectures.CoefficientClosedStructure.transpose
  apply (S.adjunction P).homEquiv_naturality_left_square
  dsimp [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [Category.assoc]
  simp only [tensorHom_id, id_tensorHom,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

private theorem ringedSiteTranspose_left {T T' P Q : D} (f : T' ⟶ T)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T' P Q (S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ g) =
      f ≫ S.transpose T P Q g := by
  let _ := S.monoidal
  dsimp only [WeilConjectures.CoefficientClosedStructure.transpose,
    WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
  rw [tensorHom_id]
  exact (S.adjunction P).homEquiv_naturality_left f g

private theorem ringedSiteTranspose_source (T : D) {P P' Q : D} (f : P' ⟶ P)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P' Q (S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g) =
      S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q)) := by
  let _ := S.monoidal
  apply (S.transpose T P' Q).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (tensorRight P').map
    (S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q))) ≫ S.evaluation P' Q
  rw [Functor.map_comp, Category.assoc]
  change _ = (S.transpose T P Q g ▷ P') ≫
    (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q
  rw [show (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q =
    (H.obj (op P, Q) ◁ f) ≫ S.evaluation P Q from S.evaluation_naturality P P' Q f]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change _ = (T ◁ f) ≫ (S.transpose T P Q).symm (S.transpose T P Q g)
  rw [Equiv.symm_apply_apply]
  simp only [WeilConjectures.CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom]

/-- Naturality of signed bidual evaluation in the source complex.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose, apply naturality of braiding, and then evaluation_naturality.
Adjunction naturality turns this identity back into the displayed equation. -/
theorem ringedSiteBidual_naturality {P P' : D} (f : P ⟶ P') :
    f ≫ ringedSiteBidual S s O P' =
      ringedSiteBidual S s O P ≫ H.map
        (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 O))).op (𝟙 O)) := by
  let _ := S.monoidal
  let _ := s
  unfold ringedSiteBidual
  rw [← ringedSiteTranspose_left]
  rw [← ringedSiteTranspose_source]
  congr 1
  dsimp [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [id_tensorHom, tensorHom_id,
    BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_right_assoc]
  congr 1
  exact (S.evaluation_naturality P' P O f).symm

/-- Evaluation is contravariantly natural in the first argument too.
Source: Stacks 08JD, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose and use evaluation_naturality, then associator naturality. -/
theorem ringedSiteDualEvaluation_source_naturality {P P' : D} (f : P' ⟶ P) (N : D) :
    S.tensor.map (Prod.mkHom (𝟙 N) (H.map (Prod.mkHom f.op (𝟙 O)))) ≫
        ringedSiteDualEvaluation S O u P' N =
      ringedSiteDualEvaluation S O u P N ≫ H.map (Prod.mkHom f.op (𝟙 N)) := by
  let _ := S.monoidal
  unfold ringedSiteDualEvaluation
  rw [← ringedSiteTranspose_left]
  rw [← ringedSiteTranspose_source]
  congr 1
  dsimp [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [id_tensorHom, tensorHom_id,
    associator_naturality_middle_assoc, associator_naturality_right_assoc]
  have ev : (H.map (Prod.mkHom f.op (𝟙 O)) ▷ P') ≫ S.evaluation P' O =
      (H.obj (op P, O) ◁ f) ≫ S.evaluation P O := S.evaluation_naturality P P' O f
  rw [← whiskerLeft_comp_assoc, ev]
  simp only [whiskerLeft_comp, Category.assoc]

/-- The canonical comparison with dual tensor the target, in the node's order.
Source: Stacks 08JE, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluationLeft (P N : D) :
    S.tensor.obj (H.obj (op P, O), N) ⟶ H.obj (op P, N) :=
  (s.braiding (H.obj (op P, O)) N).hom ≫ ringedSiteDualEvaluation S O u P N

/-- Naturality after the Koszul symmetry that interchanges the two tensor factors.
Source: Stacks 08JE (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: use braiding naturality, then ringedSiteDualEvaluation_naturality. -/
theorem ringedSiteDualEvaluationLeft_naturality (P : D) {N N' : D} (f : N ⟶ N') :
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, O))) f) ≫
        ringedSiteDualEvaluationLeft S s O u P N' =
      ringedSiteDualEvaluationLeft S s O u P N ≫ H.map (Prod.mkHom (𝟙 (op P)) f) := by
  let _ := S.monoidal
  let _ := s
  change (𝟙 _ ⊗ₘ f) ≫ (β_ _ _).hom ≫ _ = ((β_ _ _).hom ≫ _) ≫ _
  rw [BraidedCategory.braiding_naturality_assoc]
  simpa only [WeilConjectures.CoefficientClosedStructure.tensor, tensor_map,
    Category.assoc] using
    congrArg ((β_ (H.obj (op P, O)) N).hom ≫ ·)
      (ringedSiteDualEvaluation_naturality S O u P f)

/-- The node's actual canonical comparison as a natural transformation.
Source: Stacks 08JE, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluationLeftNatTrans (P : D) :
    Prod.sectR (H.obj (op P, O)) D ⋙ S.tensor ⟶ Prod.sectR (op P) D ⋙ H where
  app N := ringedSiteDualEvaluationLeft S s O u P N
  naturality _ _ f := ringedSiteDualEvaluationLeft_naturality S s O u P f

end Closed

section RestrictionAssembly
variable {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
  {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E}
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  (s : @SymmetricCategory D _ S.monoidal)
  (sU : @SymmetricCategory E _ SU.monoidal)

private theorem ringedSiteTranspose_target (T P : D) {Q Q' : D} (f : Q ⟶ Q')
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P Q' (g ≫ f) =
      S.transpose T P Q g ≫ H.map (𝟙 (op P), f) :=
  (S.adjunction P).homEquiv_naturality_right g f

private theorem ringedSiteEvaluation_target (P : D) {Q Q' : D} (f : Q ⟶ Q') :
    S.tensor.map (H.map (𝟙 (op P), f), 𝟙 P) ≫ S.evaluation P Q' =
      S.evaluation P Q ≫ f := by
  let := S.monoidal
  simpa only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id,
    CoefficientClosedStructure.evaluation, Functor.comp_map, Prod.sectR,
    tensorRight, curriedTensor, Functor.flip, Functor.id_map] using
    (S.adjunction P).counit.naturality f

private theorem ringedSiteBidual_coefficient (P O O' : D) (u : O ≅ O') :
    ringedSiteBidual S s O P ≫ H.map (X := (op (H.obj (op P, O)), O))
      (Y := (op (H.obj (op P, O)), O')) (𝟙 _, u.hom) ≫
      H.map (X := (op (H.obj (op P, O)), O'))
        (Y := (op (H.obj (op P, O')), O'))
        ((H.map (X := (op P, O')) (Y := (op P, O)) (𝟙 (op P), u.inv)).op, 𝟙 O') =
        ringedSiteBidual S s O' P := by
  let := S.monoidal
  let := s
  unfold ringedSiteBidual
  rw [← Category.assoc, ← ringedSiteTranspose_target S, ← ringedSiteTranspose_source S]
  congr 1
  simp only [Category.assoc]
  change (𝟙 P ⊗ₘ H.map (X := (op P, O')) (Y := (op P, O)) (𝟙 (op P), u.inv)) ≫
      ((β_ P (H.obj (op P, O))).hom ≫ S.evaluation P O ≫ u.hom) = _
  simp only [id_tensorHom]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  have hev := ringedSiteEvaluation_target S P u.inv
  simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id] at hev
  rw [← Category.assoc _ (S.evaluation P O), hev]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {r : D ⥤ E} {K : Prop}

/-- The natural tensor comparison, constructed from its given components. -/
private def ringedSiteRestrictionTensorIso
    (d : RingedSliceEvaluationComparisons H HU r S SU K) :
    S.tensor ⋙ r ≅ (r.prod r) ⋙ SU.tensor :=
  NatIso.ofComponents (fun X ↦ d.rho X.1 X.2)
    (fun {X Y} f ↦ d.rho_naturality X.1 X.2 Y.1 Y.2 f.1 f.2)

/-- The natural Hom comparison, constructed from its given components. -/
private def ringedSiteRestrictionHomIso
    (d : RingedSliceEvaluationComparisons H HU r S SU K) :
    H ⋙ r ≅ (r.op.prod r) ⋙ HU :=
  NatIso.ofComponents (fun X ↦ d.eta X.1.unop X.2)
    (fun {X Y} f ↦ d.eta_naturality X.1.unop X.2 Y.1.unop Y.2 f.1.unop f.2)

private theorem ringedSiteRestrictionTensorIso_hom_app
    (d : RingedSliceEvaluationComparisons H HU r S SU K) (L M : D) :
    (ringedSiteRestrictionTensorIso S SU d).hom.app (L, M) = (d.rho L M).hom := by
  rfl

private theorem ringedSiteRestrictionHomIso_hom_app
    (d : RingedSliceEvaluationComparisons H HU r S SU K) (L M : D) :
    (ringedSiteRestrictionHomIso S SU d).hom.app (op L, M) = (d.eta L M).hom := by
  rfl

private theorem ringedSiteRestrictionHomIso_inv_app
    (d : RingedSliceEvaluationComparisons H HU r S SU K) (L M : D) :
    (ringedSiteRestrictionHomIso S SU d).inv.app (op L, M) = (d.eta L M).inv := by
  rfl

private theorem ringedSiteBidual_restriction
    (d : RingedSliceEvaluationComparisons H HU r S SU K)
    (he : ∀ L M, (d.rho (H.obj (op L, M)) L).inv ≫ r.map (S.evaluation L M) =
      SU.tensor.map ((d.eta L M).hom, 𝟙 (r.obj L)) ≫
        SU.evaluation (r.obj L) (r.obj M))
    (ht : ∀ V L M (f : S.tensor.obj (V, L) ⟶ M),
      SU.transpose _ _ _ ((d.rho V L).inv ≫ r.map f) =
        r.map (S.transpose V L M f) ≫ (d.eta L M).hom)
    (hs : ∀ L M, r.map (s.braiding L M).hom ≫ (d.rho M L).hom =
      (d.rho L M).hom ≫ (sU.braiding (r.obj L) (r.obj M)).hom)
    (O P : D) :
    r.map (ringedSiteBidual S s O P) ≫ (d.eta (H.obj (op P, O)) O).hom ≫
      HU.map (X := (op (r.obj (H.obj (op P, O))), r.obj O))
        (Y := (op (HU.obj (op (r.obj P), r.obj O)), r.obj O))
        ((d.eta P O).inv.op, 𝟙 _) =
      ringedSiteBidual SU sU (r.obj O) (r.obj P) := by
  let := S.monoidal
  let := SU.monoidal
  let := s
  let := sU
  unfold ringedSiteBidual
  rw [← Category.assoc, ← ht, ← ringedSiteTranspose_source SU]
  congr 1
  rw [Functor.map_comp]
  have hb : (d.rho P (H.obj (op P, O))).inv ≫
      r.map (β_ P (H.obj (op P, O))).hom =
    (β_ (r.obj P) (r.obj (H.obj (op P, O)))).hom ≫
      (d.rho (H.obj (op P, O)) P).inv := by
    apply (cancel_mono (d.rho (H.obj (op P, O)) P).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hs, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ (r.map _) (r.map _), hb, Category.assoc, he]
  simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom,
    tensorHom_id]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

private theorem ringedSiteDualEvaluation_restriction
    (d : RingedSliceEvaluationComparisons H HU r S SU K)
    (he : ∀ L M, (d.rho (H.obj (op L, M)) L).inv ≫ r.map (S.evaluation L M) =
      SU.tensor.map (X := (r.obj (H.obj (op L, M)), r.obj L))
        (Y := (HU.obj (op (r.obj L), r.obj M), r.obj L))
        ((d.eta L M).hom, 𝟙 _) ≫ SU.evaluation (r.obj L) (r.obj M))
    (ht : ∀ V L M (f : S.tensor.obj (V, L) ⟶ M),
      SU.transpose _ _ _ ((d.rho V L).inv ≫ r.map f) =
        r.map (S.transpose V L M f) ≫ (d.eta L M).hom)
    (ha : ∀ X Y Z,
      r.map (S.monoidal.associator X Y Z).hom ≫
        (d.rho X (S.tensor.obj (Y, Z))).hom ≫
        SU.tensor.map
          (X := (r.obj X, r.obj (S.tensor.obj (Y, Z))))
          (Y := (r.obj X, SU.tensor.obj (r.obj Y, r.obj Z)))
          (𝟙 (r.obj X), (d.rho Y Z).hom) =
      (d.rho (S.tensor.obj (X, Y)) Z).hom ≫
        SU.tensor.map
          (X := (r.obj (S.tensor.obj (X, Y)), r.obj Z))
          (Y := (SU.tensor.obj (r.obj X, r.obj Y), r.obj Z))
          ((d.rho X Y).hom, 𝟙 (r.obj Z)) ≫
        (SU.monoidal.associator (r.obj X) (r.obj Y) (r.obj Z)).hom)
    (O : D) (OU : E) (u : S.monoidal.tensorUnit ≅ O)
    (uU : SU.monoidal.tensorUnit ≅ OU) (o : r.obj O ≅ OU)
    (hr : ∀ N,
      r.map (S.tensor.map (X := (N, O)) (Y := (N, S.monoidal.tensorUnit))
        (𝟙 N, u.inv) ≫ (S.monoidal.rightUnitor N).hom) =
        (d.rho N O).hom ≫ SU.tensor.map (X := (r.obj N, r.obj O))
          (Y := (r.obj N, OU)) (𝟙 (r.obj N), o.hom) ≫
          SU.tensor.map (X := (r.obj N, OU))
          (Y := (r.obj N, SU.monoidal.tensorUnit)) (𝟙 (r.obj N), uU.inv) ≫
            (SU.monoidal.rightUnitor (r.obj N)).hom)
    (P N : D) :
    r.map (ringedSiteDualEvaluation S O u P N) ≫ (d.eta P N).hom =
      (d.rho N (H.obj (op P, O))).hom ≫
        SU.tensor.map (X := (r.obj N, r.obj (H.obj (op P, O))))
          (Y := (r.obj N, HU.obj (op (r.obj P), r.obj O)))
          (𝟙 (r.obj N), (d.eta P O).hom) ≫
        SU.tensor.map
          (X := (r.obj N, HU.obj (op (r.obj P), r.obj O)))
          (Y := (r.obj N, HU.obj (op (r.obj P), OU)))
          (𝟙 (r.obj N), HU.map (X := (op (r.obj P), r.obj O))
            (Y := (op (r.obj P), OU)) (𝟙 (op (r.obj P)), o.hom)) ≫
        ringedSiteDualEvaluation SU OU uU (r.obj P) (r.obj N) := by
  let := S.monoidal
  let := SU.monoidal
  let D := H.obj (op P, O)
  let DU := HU.obj (op (r.obj P), OU)
  unfold ringedSiteDualEvaluation
  rw [← ht]
  rw [← ringedSiteTranspose_left SU, ← ringedSiteTranspose_left SU,
    ← ringedSiteTranspose_left SU]
  congr 1
  -- Compare the two composite evaluations before transposition.
  let V := S.tensor.obj (N, D)
  let action : S.tensor.obj (N, O) ⟶ N :=
    S.tensor.map (X := (N, O)) (Y := (N, S.monoidal.tensorUnit)) (𝟙 N, u.inv) ≫
      (ρ_ N).hom
  have hn := d.rho_naturality N (S.tensor.obj (D, P)) N O (𝟙 N)
    (S.evaluation P O)
  have ha' := ha N D P
  have hEv := he P O
  have hr' := hr N
  simp only [Functor.map_comp] at hr'
  simp only [Functor.map_comp]
  have htarg := ringedSiteEvaluation_target SU (r.obj P) o.hom
  simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom, tensorHom_id]
    at hn ha' hEv hr' htarg ⊢
  -- Work after the invertible tensor restriction map on the triple tensor.
  apply (cancel_epi (d.rho V P).hom).mp
  dsimp only [V]
  erw [Iso.hom_inv_id_assoc]
  change r.map (α_ N D P).hom ≫ r.map (N ◁ S.evaluation P O) ≫
      r.map (N ◁ u.inv) ≫ r.map (ρ_ N).hom = _
  rw [hr']
  simp only [Functor.map_id, id_tensorHom] at hn
  have hEv' : r.map (S.evaluation P O) = (d.rho D P).hom ≫
      (d.eta P O).hom ▷ r.obj P ≫ SU.evaluation (r.obj P) (r.obj O) := by
    rw [← hEv, Iso.hom_inv_id_assoc]
  erw [reassoc_of% hn, hEv']
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  erw [reassoc_of% ha']
  rw [← MonoidalCategory.whiskerLeft_comp_assoc _ (SU.evaluation _ _) o.hom]
  erw [← htarg]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [MonoidalCategory.associator_naturality_middle_assoc,
    MonoidalCategory.associator_naturality_middle_assoc]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Closed tensor comparisons preserve the actual duality maps after coefficient transport. -/
private theorem ringedSiteRestriction_assembly
    (d : RingedSliceEvaluationComparisons H HU r S SU K)
    (he : ∀ L M, (d.rho (H.obj (op L, M)) L).inv ≫ r.map (S.evaluation L M) =
      SU.tensor.map (X := (r.obj (H.obj (op L, M)), r.obj L))
        (Y := (HU.obj (op (r.obj L), r.obj M), r.obj L))
        ((d.eta L M).hom, 𝟙 _) ≫ SU.evaluation (r.obj L) (r.obj M))
    (ht : ∀ V L M (f : S.tensor.obj (V, L) ⟶ M),
      SU.transpose _ _ _ ((d.rho V L).inv ≫ r.map f) =
        r.map (S.transpose V L M f) ≫ (d.eta L M).hom)
    (hs : ∀ L M, r.map (s.braiding L M).hom ≫ (d.rho M L).hom =
      (d.rho L M).hom ≫ (sU.braiding (r.obj L) (r.obj M)).hom)
    (ha : ∀ X Y Z,
      r.map (S.monoidal.associator X Y Z).hom ≫
        (d.rho X (S.tensor.obj (Y, Z))).hom ≫
        SU.tensor.map
          (X := (r.obj X, r.obj (S.tensor.obj (Y, Z))))
          (Y := (r.obj X, SU.tensor.obj (r.obj Y, r.obj Z)))
          (𝟙 (r.obj X), (d.rho Y Z).hom) =
      (d.rho (S.tensor.obj (X, Y)) Z).hom ≫
        SU.tensor.map
          (X := (r.obj (S.tensor.obj (X, Y)), r.obj Z))
          (Y := (SU.tensor.obj (r.obj X, r.obj Y), r.obj Z))
          ((d.rho X Y).hom, 𝟙 (r.obj Z)) ≫
        (SU.monoidal.associator (r.obj X) (r.obj Y) (r.obj Z)).hom)
    (O : D) (OU : E) (u : S.monoidal.tensorUnit ≅ O)
    (uU : SU.monoidal.tensorUnit ≅ OU) (o : r.obj O ≅ OU)
    (hr : ∀ N,
      r.map (S.tensor.map (X := (N, O)) (Y := (N, S.monoidal.tensorUnit))
        (𝟙 N, u.inv) ≫ (S.monoidal.rightUnitor N).hom) =
        (d.rho N O).hom ≫ SU.tensor.map (X := (r.obj N, r.obj O))
          (Y := (r.obj N, OU)) (𝟙 (r.obj N), o.hom) ≫
          SU.tensor.map (X := (r.obj N, OU))
          (Y := (r.obj N, SU.monoidal.tensorUnit)) (𝟙 (r.obj N), uU.inv) ≫
            (SU.monoidal.rightUnitor (r.obj N)).hom)
    :
    let t := ringedSiteRestrictionTensorIso S SU d;
    let h := ringedSiteRestrictionHomIso S SU d;
      (∀ P N, r.map (S.evaluation P N) =
        t.hom.app (H.obj (op P, N), P) ≫
          SU.tensor.map (Prod.mkHom (h.hom.app (op P, N)) (𝟙 _)) ≫
            SU.evaluation (r.obj P) (r.obj N)) ∧
      (∀ P, r.map (ringedSiteBidual S s O P) ≫
        h.hom.app (op (H.obj (op P, O)), O) ≫
          HU.map (Prod.mkHom (h.inv.app (op P, O)).op o.hom) ≫
          HU.map (Prod.mkHom
            (HU.map (Prod.mkHom (𝟙 (op (r.obj P))) o.inv)).op (𝟙 _)) =
        ringedSiteBidual SU sU OU (r.obj P)) ∧
      (∀ P N, r.map (ringedSiteDualEvaluation S O u P N) ≫ h.hom.app (op P, N) =
        t.hom.app (N, H.obj (op P, O)) ≫
          SU.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app (op P, O))) ≫
          SU.tensor.map (Prod.mkHom (𝟙 _)
            (HU.map (Prod.mkHom (𝟙 (op (r.obj P))) o.hom))) ≫
          ringedSiteDualEvaluation SU OU uU (r.obj P) (r.obj N)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro P N
    have hh := congrArg ((d.rho _ P).hom ≫ ·) (he P N)
    simpa only [ringedSiteRestrictionTensorIso_hom_app,
      ringedSiteRestrictionHomIso_hom_app, Category.assoc, Iso.hom_inv_id_assoc] using hh
  · intro P
    have hb := ringedSiteBidual_restriction S SU s sU
      d he ht hs O P
    have hc := ringedSiteBidual_coefficient SU sU (r.obj P)
      (r.obj O) OU o
    have hm : HU.map (X := (op (r.obj (H.obj (op P, O))), r.obj O))
        (Y := (op (HU.obj (op (r.obj P), r.obj O)), OU))
        ((d.eta P O).inv.op, o.hom) =
      HU.map (X := (op (r.obj (H.obj (op P, O))), r.obj O))
        (Y := (op (HU.obj (op (r.obj P), r.obj O)), r.obj O))
        ((d.eta P O).inv.op, 𝟙 _) ≫
      HU.map (X := (op (HU.obj (op (r.obj P), r.obj O)), r.obj O))
        (Y := (op (HU.obj (op (r.obj P), r.obj O)), OU)) (𝟙 _, o.hom) := by
      rw [← HU.map_comp]
      congr 1
      apply Prod.ext
      · exact (Category.comp_id _).symm
      · exact (Category.id_comp _).symm
    simp only [ringedSiteRestrictionHomIso_hom_app,
      ringedSiteRestrictionHomIso_inv_app]
    change r.map (ringedSiteBidual S s O P) ≫
      (d.eta (H.obj (op P, O)) O).hom ≫
        HU.map (X := (op (r.obj (H.obj (op P, O))), r.obj O))
          (Y := (op (HU.obj (op (r.obj P), r.obj O)), OU))
          ((d.eta P O).inv.op, o.hom) ≫ _ = _
    rewrite [hm]
    simp only [Category.assoc]
    rewrite [reassoc_of% hb]
    exact hc
  · intro P N
    simp only [ringedSiteRestrictionTensorIso_hom_app,
      ringedSiteRestrictionHomIso_hom_app]
    exact ringedSiteDualEvaluation_restriction S SU
      d he ht ha O OU u uU o hr P N

end RestrictionAssembly

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The coefficient sheaf regarded as a complex in degree zero.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityUnitComplex :=
  (HomologicalComplex.single (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
      (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))

/-- The coefficient object in the unbounded derived category.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityUnit
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :=
  DerivedCategory.Q.obj (ringedSiteDualityUnitComplex.{c, v, r} J R)

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]

noncomputable local instance ringedSiteUnitSMul
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (U : Cᵒᵖ) :
    SMul (((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule.toSMul

noncomputable local instance ringedSiteRestrictedUnitSMul
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    {U V : Cᵒᵖ} (W : (Over U.unop)ᵒᵖ) (f : V ⟶ op W.unop.left) :
    SMul (((PresheafOfModules.restrictOver R.obj U.unop).obj
      ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val).obj W)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj.map
          f).hom).obj (M.val.obj (op W.unop.left))) :=
  (M.val.obj (op W.unop.left)).isModule.toSMul

-- These unused generated lemmas expand the native derived coefficient category.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A presentation of the existing derived tensor and Hom, normalized on K-flats.
The symmetry uses the Koszul sign. The right unitor is scalar multiplication;
the associator reassociates pure tensors. Together with models.uncurry_model these
conditions specify the evaluation constructions of 08JD and 0A97 on representatives.
Source: Stacks 06YN, 08JD, 0A97, 0A98
(blueprint: lem-sfb-ringed-site-duality-maps). -/
structure RingedSiteDualityModel where
  /-- The existing closed tensor-Hom structure. -/
  closed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The existing pure-tensor normalization of its adjunction. -/
  models : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R closed
  /-- Symmetry of this same tensor structure. -/
  symmetric : @SymmetricCategory _ _ closed.monoidal
  /-- Identification of its tensor unit with the coefficient in degree zero. -/
  unitIso : closed.monoidal.tensorUnit ≅ ringedSiteDualityUnit.{c, v, r, w} J R
  /-- The ordinary coefficient complex is K-flat. -/
  unitKFlat : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
  /-- The symmetry descends the actual signed interchange of total-complex summands. -/
  symmetry_model : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P) (hQ :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
    ∃ σ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (σ.f k).val.app U (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x
      y) =
          (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q P q p k h'
      U y x) ∧
      (models.iso J R closed P Q hP hQ).hom ≫
          (symmetric.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map σ ≫ (models.iso J R closed Q P hQ hP).hom
  /-- The right unit constraint is induced by the actual scalar multiplication map. -/
  unit_model : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P),
    ∃ ρ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      ringedSiteDualityUnitComplex.{c, v, r} J R) ⟶ P,
      (∀ (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
        (a : ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val.obj U),
        (ρ.f p).val.app U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
              p 0 p (Int.add_zero p) U x a) = a • x) ∧
      (models.iso J R closed P (ringedSiteDualityUnitComplex.{c, v, r} J R)
          hP unitKFlat).hom ≫ closed.tensor.map (Prod.mkHom (𝟙 _) unitIso.inv) ≫
          (closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map ρ
  /-- The associator descends the actual reassociation of total-complex summands. -/
  associator_model : ∀ (P Q V : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
      (hV : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) V),
    ∃ α : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q), V) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)),
      (∀ (p q t i j k : ℤ) (hpq : p + q = i) (hit : i + t = k)
        (hqt : q + t = j) (hpj : p + j = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (V.X t).val.obj U),
        (α.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V i t k hit U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)) p j k hpj U x
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q V q t j hqt U y z)) ∧
      (models.iso J R closed ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV).hom ≫
        closed.tensor.map (Prod.mkHom (models.iso J R closed P Q hP hQ).hom (𝟙 _)) ≫
        (closed.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj V)).hom =
      DerivedCategory.Q.map α ≫
        (models.iso J R closed P ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q,
      V)) hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (models.iso J R closed Q V hQ hV).hom)

set_option Elab.async false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Canonical evaluation data exist without any perfectness hypothesis.
Source: Stacks 08JD, 0A97, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: descend total tensor on K-flats by site-derived-tensor descent, and derive the
ordinary componentwise tensor-Hom adjunction with a K-injective target. Its counit
has exactly the representative formula of CoefficientTensorModels. Descend the
ordinary scalar unit, reassociation, and signed interchange; their coherence
identities hold on pure tensor generators and hence after localization. The unit
is flat in degree zero. The formulas ringedSiteBidual and ringedSiteDualEvaluation
are respectively transposed signed evaluation and composition after the Hom-unit
identification. On ordinary Hom-computable representatives their components are
x ↦ (φ ↦ (-1)^{|x||φ|} φ(x)) and y tensor φ ↦ (x ↦ y φ(x)). These formulas commute
with slice restriction: restriction is exact, retains sections and the displayed
formulas, and commutes with K-flat tensor and K-injective Hom under the canonical
restriction comparisons. Naturality follows by transposing composite evaluations.
No isomorphism of either of these two maps is used or asserted. -/
theorem ringedSiteDualityMaps_exists : Nonempty (RingedSiteDualityModel.{c, v, r, w} J R) := by
  obtain ⟨S, T, β, ⟨K⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  have hunit : CochainComplex.IsKFlatIndependentCoefficients
      (J := J) (R := R) (ringedSiteDualityUnitComplex.{c, v, r} J R) := by
    intro F hF n
    exact (hF n).of_iso (HomologicalComplex.rightUnitor F).symm
  refine ⟨⟨S, T, β, K.unitIso, hunit, ?_, ?_, ?_⟩⟩
  · intro P Q hP hQ
    obtain ⟨s, hs, he⟩ := K.symmetry_model P Q hP hQ
    exact ⟨s.hom, hs, he⟩
  · intro P hP
    obtain ⟨ρ, hρ, he⟩ := K.rightUnitor_model P hP
    refine ⟨ρ.hom, ?_, ?_⟩
    · intro p U x a
      exact hρ p (Int.add_zero p) U a x
    · rw [K.tensorIso_both P (ringedTensorUnitComplex.{c, v, r} J R) hP hunit] at he
      exact he
  · intro P Q V hP hQ hV
    obtain ⟨α, hα, he⟩ := K.associator_model P Q V hP hQ hV
    refine ⟨α.hom, ?_, ?_⟩
    · intro p q t i j k hpq hit hqt hpj U x y z
      exact hα p q t i j k hpq hqt hit hpj U x y z
    · rw [K.tensorIso_both _ V
        (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV,
        K.tensorIso_both P _ hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)] at he
      exact he

attribute [local irreducible] homComplexFunctor homComplexπ
  derivedInternalHomOfUniverses

/-- Signed coefficient evaluation, specified on every localized Hom-product section.
Source: Stacks 0A97, 0A8X (blueprint: lem-sfb-ringed-site-duality-maps). -/
def RingedSiteBidualFormula (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (β : E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R) (homComplex.{c, v, max c v r, max c v
      r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) (ringedSiteDualityUnitComplex.{c,
      v, r} J R)) : Prop :=
  ∀ (i q : ℤ) (h : i + q = 0) (h' : q + i = 0) (U : Cᵒᵖ)
    (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)).X q).val.obj (op W.unop.left)),
    (((WeilConjectures.coefficientHomComponent.{r, c, v} J R (homComplex.{c, v, max c v r, max c v
      r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) (ringedSiteDualityUnitComplex.{c,
      v, r} J R) i q 0 h').val.app U
      ((β.f i).val.app U x)).app W).hom φ =
      (i * q).negOnePow •
        (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E
      (ringedSiteDualityUnitComplex.{c, v, r} J R) q i 0 h).val.app (op W.unop.left) φ).app
          (op (Over.mk (𝟙 W.unop.left)))).hom
            ((E.X i).val.map W.unop.hom.op x)

section OrdinaryBidualComponents

attribute [local irreducible] ringedSiteDualityUnitComplex

set_option backward.isDefEq.respectTransparency false

@[no_expose] private def ringedSiteEvalSection
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _))
    {U : Cᵒᵖ} (x : A.obj U) :
    (PresheafOfModules.restrictOver 𝒜 U.unop).obj (PresheafOfModules.homObj (R := 𝒜) A B) ⟶
      (PresheafOfModules.restrictOver 𝒜 U.unop).obj B where
  app W := ModuleCat.ofHom
    { toFun := fun φ ↦ (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
        (A.map W.unop.hom.op x)
      map_add' := by intros; rfl
      map_smul' := by
        intro a φ
        refine (PresheafOfModules.restrictOver_smul_app_apply a φ _ _).trans ?_
        change 𝒜.map (𝟙 (op W.unop.left)) a •
          ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (A.map W.unop.hom.op x)) = a •
          ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (A.map W.unop.hom.op x))
        rw [𝒜.map_id]
        rfl }
  naturality {W W'} f := by
    ext φ
    change ((PresheafOfModules.restrictOverMap f.unop.left φ).app
        (op (Over.mk (𝟙 W'.unop.left)))).hom (A.map W'.unop.hom.op x) =
      B.map f.unop.left.op
        ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x))
    have hx : A.map f.unop.left.op (A.map W.unop.hom.op x) =
        A.map W'.unop.hom.op x := by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
    exact (PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp _) _).trans
      ((congrArg (fun z ↦ (φ.app (op (Over.mk f.unop.left))).hom z) hx.symm).trans
        (PresheafOfModules.naturality_apply φ
          (Over.homMk f.unop.left (Category.comp_id _) :
            Over.mk f.unop.left ⟶ Over.mk (𝟙 W.unop.left)).op
              (A.map W.unop.hom.op x)))

@[no_expose] private def ringedSitePresheafBidual
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _)) :
    A ⟶ PresheafOfModules.homObj (R := 𝒜)
      (PresheafOfModules.homObj (R := 𝒜) A B) B where
      app U := ModuleCat.ofHom (R := 𝒜.obj U) (X := A.obj U)
        (Y := (PresheafOfModules.homObj (R := 𝒜)
          (PresheafOfModules.homObj (R := 𝒜) A B) B).obj U)
        { toFun := ringedSiteEvalSection.{c, v, r} 𝒜 A B
          map_add' := by
            intro x y
            apply PresheafOfModules.hom_ext
            intro W
            ext φ
            change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (x + y)) =
              (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x) +
                (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op y)
            exact (congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
              ((A.map W.unop.hom.op).hom.map_add x y)).trans
              (map_add (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom _ _)
          map_smul' := by
            intro a x
            apply PresheafOfModules.hom_ext
            intro W
            ext φ
            change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (a • x)) =
              𝒜.map W.unop.hom.op a •
                (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x)
            exact (congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
              (A.map_smul W.unop.hom.op a x)).trans
              ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom.map_smul _ _) }
      naturality := by
        intro U V f
        ext x : 2
        apply PresheafOfModules.hom_ext
        intro W
        ext φ
        change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (A.map f x)) =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map (W.unop.hom ≫ f.unop).op x)
        exact congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
          (A.map_comp_apply f W.unop.hom.op x).symm

@[no_expose] private def ringedSiteSheafBidual
    (A B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    A ⟶ SheafOfModules.homObj (R := R) (SheafOfModules.homObj (R := R) A B) B where
  val := ringedSitePresheafBidual.{c, v, r} R.obj A.val B.val

@[no_expose] private abbrev RingedSiteComplex := CochainComplex (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ


end OrdinaryBidualComponents

/-- The ordinary signed evaluation chain map is uniquely determined by its section formula.
Source: Stacks 0A97, 0A8X (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: the existing signed-bidual localization theorem constructs an ordinary family
with precisely this formula on all slice sections and proves uniqueness for that formula.
Choose any of the existing normalized closed tensor models, apply that theorem, and
retain the existence and uniqueness clauses for E. The coefficient complexes and
product projections in the two formulas are definitionally the same. -/
theorem ringedSiteOrdinaryBidual_existsUnique (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ∃! β : E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R) (homComplex.{c, v, max c v r, max c
      v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
      (ringedSiteDualityUnitComplex.{c, v, r} J R),
      RingedSiteBidualFormula.{c, v, r} J R E β := by
  obtain ⟨S, T, β, ⟨K⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  obtain ⟨b, hb⟩ := ringed_signed_bidual_localization J R S T β K
  obtain ⟨hformula, huniq, _, _, _⟩ := hb E
  exact ⟨b E, hformula, huniq⟩

/-- The actual ordinary signed bidual map, chosen from its unique section characterization.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryBidual (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :=
  (ringedSiteOrdinaryBidual_existsUnique.{c, v, r} J R E).exists.choose

/-- Graded tensor-Hom evaluation, including its zero components.
Source: Stacks 08JE, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def RingedSiteEvaluationFormula (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (ε : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (F, homComplex.{c, v, max c v
      r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) ⟶ homComplex.{c, v,
      max c v r, max c v r} (R := R) E F) : Prop :=
  (∀ (p q k a : ℤ) (hpq : p + q = k) (haq : a + q = 0) (hak : a + k = p)
    (U : Cᵒᵖ) (y : (F.X p).val.obj U)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)).X q).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E.X a).val.obj (op W.unop.left)),
    (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a p hak).val.app U
        ((ε.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F (homComplex.{c, v, max c v r,
      max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) p q k hpq U y φ))).app
      W).hom x =
      (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E (ringedSiteDualityUnitComplex.{c,
      v, r} J R) q a 0 haq).val.app U φ).app W).hom x •
        (F.X p).val.map W.unop.hom.op y) ∧
  (∀ (p q k a b : ℤ) (hpq : p + q = k) (hab : a + k = b) (_haq : a + q ≠ 0)
    (U : Cᵒᵖ) (y : (F.X p).val.obj U)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)).X q).val.obj U),
    (WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a b hab).val.app U
      ((ε.f k).val.app U
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F (homComplex.{c, v, max c v r,
      max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) p q k hpq U y φ)) = 0)

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem ringedSiteTensorGenerator_restrict
    (P Q : RingedSiteComplex.{c, v, r} J R) (p q k : ℤ) (h : p + q = k)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k).val.map f
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x y) =
      WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h V
        ((P.X p).val.map f x) ((Q.X q).val.map f y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let η := (PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R).obj)).unit.app ((P.X p).val ⊗ (Q.X q).val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X p) (Q.X q)).inv.val ≫
    (HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ) p q k h).val
  exact (PresheafOfModules.naturality_apply η f (x ⊗ₜ[R.obj.obj U] y)).symm

attribute [local irreducible] coefficientTotalTensor

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem ringedSiteHomValue_restrict
    (A B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (U : Cᵒᵖ) (φ : (SheafOfModules.homObj (R := R) A B).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A.val.obj (op W.unop.left)) :
    (((SheafOfModules.homObj (R := R) A B).val.map W.unop.hom.op φ).app
      (op (Over.mk (𝟙 W.unop.left)))).hom x = (φ.app W).hom x := by
  change (φ.app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))).hom x = _
  exact PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp _) x

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem ringedSiteEvaluationFormula_iff
    (E F : RingedSiteComplex.{c, v, r} J R)
    (ε : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      (F, homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) ⟶
        homComplex (R := R) E F) :
    RingedSiteEvaluationFormula.{c, v, r} J R E F ε ↔
      RingedOrdinaryEvaluationFormula.{c, v, r} J R E F ε := by
  constructor
  · intro h p q k a b hpq hab U y φ x
    constructor
    · intro haq hp
      rcases hp with rfl
      have he := h.1 p q k a hpq haq hab U y φ (op (Over.mk (𝟙 U.unop))) x
      change _ = ringedOrdinaryDualValue.{c, v, r} J R E q a haq U φ x •
        (show (F.X p).val.obj U from (F.X p).val.map (𝟙 U) y) at he
      have hid : (F.X p).val.map (𝟙 U) y = y := by
        rw [PresheafOfModules.map_id]; rfl
      exact he.trans (congrArg (fun z : (F.X p).val.obj U ↦
        (ringedOrdinaryDualValue.{c, v, r} J R E q a haq U φ x : R.obj.obj U) • z) hid)
    · intro haq
      have hz := h.2 p q k a b hpq hab haq U y φ
      exact congrArg (fun z ↦ (z.app (op (Over.mk (𝟙 U.unop)))).hom x) hz
  · intro h
    constructor
    · intro p q k a hpq haq hak U y φ W x
      let : SMul
          (((PresheafOfModules.restrictOver R.obj (op W.unop.left).unop).obj
            ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val).obj
              (op (Over.mk (𝟙 W.unop.left))))
          ((ModuleCat.restrictScalars
            (((sheafCompose J (forget₂ CommRingCat.{max c v r}
              RingCat.{max c v r})).obj R).obj.map W.unop.hom.op).hom).obj
                ((F.X p).val.obj (op W.unop.left))) :=
        ((F.X p).val.obj (op W.unop.left)).isModule.toSMul
      have hlocal := (h p q k a p hpq hak (op W.unop.left)
        ((F.X p).val.map W.unop.hom.op y)
        (((homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)).X q).val.map
          W.unop.hom.op φ) x).1 haq rfl
      have hn := PresheafOfModules.naturality_apply
        ((ε.f k) ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a p hak).val
        W.unop.hom.op
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F
          (homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
          p q k hpq U y φ)
      rw [ringedSiteTensorGenerator_restrict.{c, v, r} J R] at hn
      have hn' := congrArg
        (fun z ↦ (z.app (op (Over.mk (𝟙 W.unop.left)))).hom x) hn
      have hr := ringedSiteHomValue_restrict.{c, v, r} J R
        (E.X a) (F.X p) U
        (((ε.f k) ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a p hak).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F
            (homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
            p q k hpq U y φ)) W x
      rw [hr] at hn'
      change _ = _ at hn'
      change (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E F
        k a p hak).val.app (op W.unop.left)
          ((ε.f k).val.app (op W.unop.left)
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F
              (homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
              p q k hpq (op W.unop.left)
              ((F.X p).val.map W.unop.hom.op y)
              (((homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)).X q).val.map
                W.unop.hom.op φ)))).app (op (Over.mk (𝟙 W.unop.left)))).hom x =
          (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E
            (ringedSiteDualityUnitComplex.{c, v, r} J R) q a 0 haq).val.app
              (op W.unop.left)
              (((homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)).X q).val.map
                W.unop.hom.op φ)).app (op (Over.mk (𝟙 W.unop.left)))).hom x •
            (F.X p).val.map W.unop.hom.op y at hlocal
      have hd := PresheafOfModules.naturality_apply
        (WeilConjectures.coefficientHomComponent.{r, c, v} J R E
          (ringedSiteDualityUnitComplex.{c, v, r} J R) q a 0 haq).val W.unop.hom.op φ
      have hd' := congrArg
        (fun z ↦ (z.app (op (Over.mk (𝟙 W.unop.left)))).hom x) hd
      have hrd := ringedSiteHomValue_restrict.{c, v, r} J R (E.X a)
        ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0) U
        ((WeilConjectures.coefficientHomComponent.{r, c, v} J R E
          (ringedSiteDualityUnitComplex.{c, v, r} J R) q a 0 haq).val.app U φ) W x
      rw [hrd] at hd'
      exact hn'.symm.trans (hlocal.trans (congrArg
        (fun z ↦ z • (F.X p).val.map W.unop.hom.op y) hd'))
    · intro p q k a b hpq hab haq U y φ
      apply PresheafOfModules.hom_ext
      intro W
      ext x
      have hlocal := (h p q k a b hpq hab (op W.unop.left)
        ((F.X p).val.map W.unop.hom.op y)
        (((homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)).X q).val.map
          W.unop.hom.op φ) x).2 haq
      have hn := PresheafOfModules.naturality_apply
        ((ε.f k) ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a b hab).val
        W.unop.hom.op
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F
          (homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
          p q k hpq U y φ)
      rw [ringedSiteTensorGenerator_restrict.{c, v, r} J R] at hn
      have hn' := congrArg
        (fun z ↦ (z.app (op (Over.mk (𝟙 W.unop.left)))).hom x) hn
      have hr := ringedSiteHomValue_restrict.{c, v, r} J R
        (E.X a) (F.X b) U
        (((ε.f k) ≫ WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a b hab).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F
            (homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
            p q k hpq U y φ)) W x
      rw [hr] at hn'
      exact hn'.symm.trans hlocal

/-- The ordinary evaluation chain map, uniquely specified on the actual tensor generators.
Source: Stacks 08JE, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: define every Hom-product projection on a total-tensor summand by the
specified sheaf-bilinear evaluation. Sheafification and the coproduct universal
property supply each degree map. The tensor and Hom differentials give the same
two terms, with the second sign (-1)^(p+q+1). Thus these are chain maps. Pure tensor
generators, Hom-product projections and sheaf separation give uniqueness. -/
theorem ringedSiteOrdinaryEvaluation_existsUnique (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ∃! ε : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (F, homComplex.{c, v, max c v
      r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) ⟶ homComplex.{c, v,
      max c v r, max c v r} (R := R) E F,
      RingedSiteEvaluationFormula.{c, v, r} J R E F ε := by
  obtain ⟨S, T, β, ⟨K⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  obtain ⟨ε, hε, hu, _⟩ := ringedOrdinaryEvaluation_localization J R S T β K E F
  exact ⟨ε, (ringedSiteEvaluationFormula_iff J R E F ε).2 hε,
    fun γ hγ ↦ hu γ ((ringedSiteEvaluationFormula_iff J R E F γ).1 hγ)⟩

/-- Ordinary tensor-Hom evaluation, with real data fixed by its unique pure-tensor formula.
Source: Stacks 08JE (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryEvaluation (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :=
  (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R E F).exists.choose

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)] in
private theorem ringedSiteAugmentationMap_eq
    (E F : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) :
    ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E) ((ringedSiteHomAugmentation.{c, v, r} J R).app F) =
      ((homComplexFunctor (R := R)).obj (op E)).map
        ((SfbHomFilteredColimit.resolutionUnit.{c, v, r} J R).app F) := by
  simp only [ringedSiteHomComplexMap, op_id, Functor.map_id, NatTrans.id_app]
  rfl

private theorem ringedSiteHomComparison_eq
    (E F : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) :
    ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F =
      ringedOrdinaryHomComparison.{c, v, r, w} J R E F := by
  unfold ringedSiteOrdinaryHomComparison ringedOrdinaryHomComparison
  rw [ringedSiteAugmentationMap_eq]
  rfl

section NormalizedSymmetry
private theorem ringedSiteNormalizedSymmetry_eq
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (T : CoefficientTensorModels.{r, c, v, w} J R S)
  (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ S.monoidal)
  (K : RingedDerivedTensorCoherence.{c, v, r, w} J R S T s)
    (σ : ∀ L N, S.tensor.obj (L, N) ≅ S.tensor.obj (N, L))
    (hnat : ∀ L N L' N' f g, S.tensor.map (X := (L, N)) (Y := (L', N')) (f, g) ≫
      (σ L' N').hom = (σ L N).hom ≫ S.tensor.map (g, f))
    (hmodel : ∀ P Q hP hQ,
      ∃ β : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ≅
          (coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
        (∀ p q k h h' V x y,
          (β.hom.f k).val.app V
            (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y) =
          (p * q).negOnePow •
            coefficientTensorGenerator.{r, c, v} J R Q P q p k h' V y x) ∧
        (T.iso J R S P Q hP hQ).hom ≫
          (σ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map β.hom ≫ (T.iso J R S Q P hQ hP).hom)
    (L N : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    (σ L N).hom = (s.braiding L N).hom := by
  have base (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
      (σ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom := by
    obtain ⟨β, hβ, heβ⟩ := hmodel P Q hP hQ
    obtain ⟨γ, hγ, heγ⟩ := K.symmetry_model P Q hP hQ
    have hh : β.hom = γ.hom := by
      apply tensorGenerator_ext.{c, v, r} J R
      intro p q k hpq V x y
      exact (hβ p q k hpq (by omega) V x y).trans
        (hγ p q k hpq (by omega) V x y).symm
    apply (cancel_epi (T.iso J R S P Q hP hQ).hom).mp
    rw [heβ, heγ, hh]
  classical
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage L)
  obtain ⟨Q, g, hQ, _, hg, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage N)
  have : QuasiIso f := hf
  have : QuasiIso g := hg
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hg
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  let e' := asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  have : IsIso (Prod.mkHom e.hom e'.hom) :=
    (CategoryTheory.isIso_prod_iff (f := Prod.mkHom e.hom e'.hom)).mpr
      ⟨inferInstanceAs (IsIso e.hom), inferInstanceAs (IsIso e'.hom)⟩
  apply (cancel_epi (S.tensor.map
    (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (Y := (L, N)) (e.hom, e'.hom))).mp
  rw [hnat]
  let := S.monoidal
  let := s
  rw [show S.tensor.map
    (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    (Y := (L, N)) (e.hom, e'.hom) ≫ (β_ L N).hom =
    (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      S.tensor.map
      (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
      (Y := (N, L)) (e'.hom, e.hom) from
    BraidedCategory.braiding_naturality e.hom e'.hom]
  rw [base P Q hP hQ]

end NormalizedSymmetry

attribute [local semireducible] coefficientTotalTensor

private theorem ringedSiteTensorSymmetryModel
    (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    RingedDerivedTensorSymmetryModel.{c, v, r, w} J R M.closed M.models M.symmetric := by
  intro P Q hP hQ
  obtain ⟨σ, hσ, he⟩ := M.symmetry_model P Q hP hQ
  have hs : σ = (β_ P Q).hom := by
    apply tensorGenerator_ext.{c, v, r} J R
    intro p q k hpq U x y
    have hqp : q + p = k := (add_comm q p).trans hpq
    exact (hσ p q k hpq hqp U x y).trans
      ((RingedDerivedNative.complexConstraints.{c, v, r} J R).symmetry
        P Q p q k hpq hqp U x y).symm
  exact ⟨β_ P Q, (RingedDerivedNative.complexConstraints.{c, v, r} J R).symmetry P Q,
    hs ▸ he⟩

private theorem ringedSiteTensorAssociatorModel
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (t : RingedDerivedTensorComparison.{c, v, r, w} J R M.closed)
    (ht : RingedDerivedTensorBothModel.{c, v, r, w} J R M.closed M.models t) :
    RingedDerivedTensorAssociatorModel.{c, v, r, w} J R M.closed M.models t := by
  intro P Q N hP hQ hN
  obtain ⟨a, ha, he⟩ := M.associator_model P Q N hP hQ hN
  have heq : a = (α_ P Q N).hom := by
    apply tensorGenerator_ext₃.{c, v, r} J R
    intro p q t i k hpq hit U x y z
    have hpj : p + (q + t) = k := by omega
    exact (ha p q t i (q + t) k hpq hit rfl hpj U x y z).trans
      ((RingedDerivedNative.complexConstraints.{c, v, r} J R).associator
        P Q N p q t i (q + t) k hpq rfl hit hpj U x y z).symm
  refine ⟨α_ P Q N,
    (RingedDerivedNative.complexConstraints.{c, v, r} J R).associator P Q N, ?_⟩
  rw [ht _ N (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hN,
    ht P _ hP (coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN)]
  exact heq ▸ he

private theorem ringedSiteTensorRightUnitorModel
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (t : RingedDerivedTensorComparison.{c, v, r, w} J R M.closed)
    (ht : RingedDerivedTensorBothModel.{c, v, r, w} J R M.closed M.models t) :
    RingedDerivedTensorRightUnitorModel.{c, v, r, w} J R M.closed t M.unitIso := by
  intro P hP
  obtain ⟨ρ, hρ, he⟩ := M.unit_model P hP
  have heq : ρ = (ρ_ P).hom := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P) (K₂ := ringedTensorUnitComplex.{c, v, r} J R)
      (F := curriedTensor (RingedTensorModules.{c, v, r} J R)) (c := .up ℤ)
    intro p q hpq
    change p + q = k at hpq
    by_cases hq : q = 0
    · subst q
      have hk : k = p := by omega
      subst hk
      apply pure_ext.{c, v, r} J R (P.X k)
        ((ringedTensorUnitComplex.{c, v, r} J R).X 0) (P.X k)
      intro U x a
      exact (hρ k U x a).trans
        ((RingedDerivedNative.complexConstraints.{c, v, r} J R).rightUnitor
          P k (Int.add_zero k) U a x).symm
    · apply IsZero.eq_of_src
      exact (tensorLeft (P.X p)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq)
  refine ⟨ρ_ P, (RingedDerivedNative.complexConstraints.{c, v, r} J R).rightUnitor P, ?_⟩
  rw [ht P (ringedTensorUnitComplex.{c, v, r} J R) hP M.unitKFlat]
  exact heq ▸ he

private theorem ringedSiteTensorLeftUnitorModel
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (t : RingedDerivedTensorComparison.{c, v, r, w} J R M.closed)
    (ht : RingedDerivedTensorBothModel.{c, v, r, w} J R M.closed M.models t) :
    RingedDerivedTensorLeftUnitorModel.{c, v, r, w} J R M.closed t M.unitIso := by
  let S := M.closed
  let s := M.symmetric
  let u := M.unitIso
  have hs := ringedSiteTensorSymmetryModel J R M
  have hr := ringedSiteTensorRightUnitorModel J R M t ht
  intro P hP
  obtain ⟨σ, hσ, heσ⟩ := hs
    (ringedTensorUnitComplex.{c, v, r} J R) P M.unitKFlat hP
  obtain ⟨ρ, hρ, heρ⟩ := hr P hP
  refine ⟨σ ≪≫ ρ, ?_, ?_⟩
  · intro n hn U a x
    change (ρ.hom.f n).val.app U ((σ.hom.f n).val.app U
      (coefficientTensorGenerator.{r, c, v} J R
        (ringedTensorUnitComplex.{c, v, r} J R) P 0 n n hn U
        (ringedTensorUnitSection.{c, v, r} J R U a) x)) = _
    rw [hσ 0 n n hn (Int.add_zero n) U _ x]
    simpa only [zero_mul, Int.negOnePow_zero, one_smul] using hρ n (Int.add_zero n) U a x
  · let := S.monoidal
    let := s
    rw [ht (ringedTensorUnitComplex.{c, v, r} J R) P M.unitKFlat hP]
    have hu : S.tensor.map
        (X := (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R),
          DerivedCategory.Q.obj P))
        (Y := (S.monoidal.tensorUnit, DerivedCategory.Q.obj P))
        (u.inv, 𝟙 (DerivedCategory.Q.obj P)) ≫
        (λ_ (DerivedCategory.Q.obj P)).hom =
      (s.braiding (DerivedCategory.Q.obj
        (ringedTensorUnitComplex.{c, v, r} J R)) (DerivedCategory.Q.obj P)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj P,
            DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, r} J R)))
          (Y := (DerivedCategory.Q.obj P, S.monoidal.tensorUnit))
          (𝟙 (DerivedCategory.Q.obj P), u.inv) ≫
          (ρ_ (DerivedCategory.Q.obj P)).hom := by
      change (u.inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom =
        (β_ _ _).hom ≫ (𝟙 _ ⊗ₘ u.inv) ≫ (ρ_ _).hom
      rw [← braiding_rightUnitor,
        BraidedCategory.braiding_naturality_assoc]
    rw [hu, ← Category.assoc, heσ]
    simp only [Category.assoc]
    rw [← ht P (ringedTensorUnitComplex.{c, v, r} J R) hP M.unitKFlat,
      heρ, ← Functor.map_comp]
    rfl

private theorem ringedSiteTensorCoherence
    (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    ∃ K : RingedDerivedTensorCoherence.{c, v, r, w} J R M.closed M.models M.symmetric,
      K.unitIso = M.unitIso := by
  obtain ⟨t, ht, hn⟩ := ringedTensorComparison_extension.{c, v, r, w} J R M.closed M.models
  exact ⟨⟨t, ht, hn, M.unitIso, ringedSiteTensorSymmetryModel J R M,
    ringedSiteTensorAssociatorModel J R M t ht, ringedSiteTensorLeftUnitorModel J R M t ht,
    ringedSiteTensorRightUnitorModel J R M t ht⟩, rfl⟩

/-- Biduality is the signed ordinary map under the two specified Hom comparisons.
Source: Stacks 0A97, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: the closed transposition is pinned by models.uncurry_model. The normalized
symmetry supplies precisely the interchange sign. Apply this twice and use the
specified scalar unit. Localize the resulting ordinary chain map and its two
augmentation comparisons. The tensor-Hom adjunction identifies it with the
transpose that defines ringedSiteBidual; no K-flatness is needed for E or its dual. -/
theorem ringedSiteBidual_normalization (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app (ringedSiteDualityUnitComplex.{c, v, r} J R))))
    (hD : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 (homComplex.{c, v, max c v r, max c v
      r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)))
      ((ringedSiteHomAugmentation.{c, v, r} J R).app (ringedSiteDualityUnitComplex.{c, v, r} J
      R)))) :
    ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R)
        (DerivedCategory.Q.obj E) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E (ringedSiteDualityUnitComplex.{c,
      v, r} J R) hE).hom.op (𝟙 _)) =
    DerivedCategory.Q.map (ringedSiteOrdinaryBidual.{c, v, r} J R E) ≫
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R (homComplex.{c, v, max c v r, max c v r} (R := R)
      E (ringedSiteDualityUnitComplex.{c, v, r} J R)) (ringedSiteDualityUnitComplex.{c, v, r} J R)
      hD).hom := by
  obtain ⟨K, _⟩ := ringedSiteTensorCoherence J R M
  obtain ⟨β, hβ⟩ := ringed_signed_bidual_localization J R M.closed M.models M.symmetric K
  obtain ⟨hβE, hu, _, _, hc⟩ := hβ E
  have hβeq : ringedSiteOrdinaryBidual.{c, v, r} J R E = β E :=
    hu _ (ringedSiteOrdinaryBidual_existsUnique.{c, v, r} J R E).exists.choose_spec
  have hE' := hE
  have hD' := hD
  rw [ringedSiteAugmentationMap_eq] at hE' hD'
  obtain ⟨γE, γD, he, hd, hn⟩ := hc hE' hD'
  have he' : γE.hom = (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E
      (ringedSiteDualityUnitComplex.{c, v, r} J R) hE).hom := by
    change _ = ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E _
    rw [ringedSiteOrdinaryHomComparison, ringedSiteAugmentationMap_eq]
    exact he
  have hd' : γD.hom = (ringedSiteOrdinaryHomIso.{c, v, r, w} J R
      (homComplex (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
      (ringedSiteDualityUnitComplex.{c, v, r} J R) hD).hom := by
    change _ = ringedSiteOrdinaryHomComparison.{c, v, r, w} J R _ _
    rw [ringedSiteOrdinaryHomComparison, ringedSiteAugmentationMap_eq]
    exact hd
  -- Transport the morphisms separately, without rewriting the dependent comparison data.
  have hemap := congrArg (fun f ↦
    (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom f.op (𝟙 (ringedSiteDualityUnit.{c, v, r, w} J R)))) he'
  exact (congrArg
    (ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R)
      (DerivedCategory.Q.obj E) ≫ ·) hemap).symm.trans
    (hn.trans (congrArg₂ (· ≫ ·) (congrArg DerivedCategory.Q.map hβeq.symm) hd'))

/-- Evaluation is the unsigned ordinary map under the specified tensor and Hom comparisons.
Source: Stacks 08JE, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose the comparison using the normalized tensor-Hom adjunction.
Associator normalization identifies its summand maps with ordinary composite
evaluation. Unit normalization gives y*phi(x), with no extra sign. Both tensor
arguments are K-flat, so models.iso is the specified tensor comparison. Localizing
the unique ordinary evaluation map gives the equation. The hypotheses are exactly
those required for the two augmentation comparisons to be invertible. -/
theorem ringedSiteDualEvaluation_normalization
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hF : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) F) (hD
      : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J
      R)))
    (hE : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app (ringedSiteDualityUnitComplex.{c, v, r} J R))))
    (hEF : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :
    (M.models.iso J R M.closed F (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)) hF hD).hom ≫
      M.closed.tensor.map (Prod.mkHom (𝟙 _)
        (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E (ringedSiteDualityUnitComplex.{c, v, r} J R)
      hE).hom) ≫
      ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R)
        M.unitIso (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
    DerivedCategory.Q.map (ringedSiteOrdinaryEvaluation.{c, v, r} J R E F) ≫
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E F hEF).hom := by
  obtain ⟨K, hK⟩ := ringedSiteTensorCoherence J R M
  obtain ⟨ε, hε, hu, hc⟩ := ringedOrdinaryEvaluation_localization
    J R M.closed M.models M.symmetric K E F
  have hεeq : ringedSiteOrdinaryEvaluation.{c, v, r} J R E F = ε :=
    hu _ ((ringedSiteEvaluationFormula_iff.{c, v, r} J R E F _).1
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R E F).exists.choose_spec)
  have hE' : QuasiIso (ringedHomAugmentationMap.{c, v, r} J R E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)) := by
    rw [ringedSiteAugmentationMap_eq] at hE
    exact hE
  have hEF' : QuasiIso (ringedHomAugmentationMap.{c, v, r} J R E F) := by
    rw [ringedSiteAugmentationMap_eq] at hEF
    exact hEF
  obtain ⟨_, _, hn⟩ := hc hF hD hE' hEF'
  rw [hK, ← hεeq, ← ringedSiteHomComparison_eq, ← ringedSiteHomComparison_eq] at hn
  change _ = _ at hn
  simpa only [ringedSiteOrdinaryHomIso, asIso_hom,
    ringedDualTensorHom, ringedSiteDualEvaluation,
    CoefficientClosedStructure.tensor, tensor_map, id_tensorHom, tensorLeft, curriedTensor,
    ringedSiteDualityUnit, ringedSiteDualityUnitComplex, ringedTensorUnitComplex] using hn

/-- Slice restriction sends zero maps to zero, by its sectionwise construction.
Source: Stacks 03DJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: overFunctor keeps the components of a module morphism and only restricts
its index category. Each component of a zero morphism remains zero. -/
theorem ringedSiteDualityRestriction_preservesZero (U : C) :
    (SheafOfModules.overFunctor.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
        U).PreservesZeroMorphisms := by
  classical
  have hSheaf : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  have hW : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  constructor
  intro X Y
  ext V x
  rfl

/-- Forgetting commutativity commutes with slice restriction as sheaves of rings.
Source: Stacks 03DJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: both sides have the section ring R(V), and the same ring restriction map,
on an object V to U of the slice. Extensionality of ring sheaves gives equality;
the sheaf-condition proofs are propositionally irrelevant. -/
theorem ringedSiteDualityRestrictionCoefficient_eq (U : C) :
    (sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U) =
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U := by
  have hSheaf : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  have hW : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  rfl

/-- The actual termwise restriction functor on complexes.
Source: Stacks 03DJ, 08FI (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityRestrictionComplex (U : C) :=
  letI := ringedSiteDualityRestriction_preservesZero.{c, v, r} J R U
  ((SheafOfModules.overFunctor.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U) ⋙
      SheafOfModules.restrictScalars (eqToHom
        (ringedSiteDualityRestrictionCoefficient_eq.{c, v, r} J R U))).mapHomologicalComplex
          (ComplexShape.up ℤ)

/-- Scalar transport along the definitional slice coefficient equality is the identity. -/
private theorem ringedSiteRestrictionComplex_eq (U : C) :
    ringedSiteDualityRestrictionComplex.{c, v, r} J R U =
      ringedSliceComplexRestriction.{c, v, r} J R U := by
  rfl

attribute [local irreducible] ringedSliceDerivedRestriction

attribute [local irreducible] DerivedCategory.Q ringedSliceComplexRestriction
attribute [local irreducible] ringedSiteDualityRestrictionComplex
attribute [local irreducible] ringedSiteRestrictionTensorIso ringedSiteRestrictionHomIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The natural comparison maps retain dependent localization and coefficient types.
/-- Canonical maps commute with exact slice restriction. The functor F is specified
by termwise restriction and localization. Its tensor and Hom comparisons are the
closed evaluation-compatible comparisons, not separate choices of bidual/evaluation
maps. The two equations state compatibility for the actual previously defined maps.
Source: Stacks 08JB, 08JD, 0A97, 0A98, 03DJ
(blueprint: lem-sfb-ringed-site-duality-maps).
Proof: exact module restriction inverts quasi-isomorphisms on complexes, hence
factors through Q with the displayed comparison. It preserves the ordinary unit
and sheafified tensor generators, so K-flat descent gives the tensor comparison.
Restriction preserves K-injectives and the actual Hom-product projections; the
fixed augmentation comparisons give the Hom comparison. These comparisons commute
with componentwise evaluation. Transpose this evaluation square, first after
signed interchange and then after composite evaluation, to obtain the bidual
and tensor-Hom squares. This proof does not assume perfectness. -/
theorem ringedSiteDualityMaps_restriction
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v r}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj (R.over U)))]
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U)) :
    ∃ F : DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
      DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj (R.over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        ringedSiteDualityRestrictionComplex.{c, v, r} J R U ⋙ DerivedCategory.Q.{w'}) ∧
      ∃ (t : M.closed.tensor ⋙ F ≅ (F.prod F) ⋙ MU.closed.tensor)
        (h : (derivedInternalHomOfUniverses.{c, v, r, w} J R) ⋙ F ≅ (F.op.prod F) ⋙
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)))
        (o : F.obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅ ringedSiteDualityUnit.{max c v, v, r,
      w'} (J.over U) (R.over U)),
      (∀ P N,
        F.map (M.closed.evaluation P N) =
          t.hom.app ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, N), P) ≫
            MU.closed.tensor.map (Prod.mkHom (h.hom.app (op P, N)) (𝟙 _)) ≫
              MU.closed.evaluation (F.obj P) (F.obj N)) ∧
      (∀ P,
        F.map (ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R) P) ≫
          h.hom.app (op ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P,
      ringedSiteDualityUnit.{c, v, r, w} J R)), ringedSiteDualityUnit.{c, v, r, w} J R) ≫
          (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map (Prod.mkHom
            (h.inv.app (op P, ringedSiteDualityUnit.{c, v, r, w} J R)).op o.hom) ≫
          (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map (Prod.mkHom
            ((derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map
      (Prod.mkHom (𝟙 (op (F.obj P))) o.inv)).op (𝟙 _)) =
        ringedSiteBidual MU.closed MU.symmetric (ringedSiteDualityUnit.{max c v, v, r, w'} (J.over
      U) (R.over U)) (F.obj P)) ∧
      (∀ P N,
        F.map (ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso
      P N) ≫
          h.hom.app (op P, N) =
        t.hom.app (N, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P,
      ringedSiteDualityUnit.{c, v, r, w} J R)) ≫
          MU.closed.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app (op P, ringedSiteDualityUnit.{c, v, r,
      w} J R))) ≫
          MU.closed.tensor.map (Prod.mkHom (𝟙 _)
            ((derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map
      (Prod.mkHom (𝟙 (op (F.obj P))) o.hom))) ≫
          ringedSiteDualEvaluation MU.closed (ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U)
      (R.over U)) MU.unitIso (F.obj P) (F.obj N)) := by
  classical
  exact
    let coherence := ringedSiteTensorCoherence.{c, v, r, w} J R M
    let K := coherence.choose
    have hK : K.unitIso = M.unitIso := coherence.choose_spec
    let coherenceU :=
      ringedSiteTensorCoherence.{max c v, v, r, w'} (J.over U) (R.over U) MU
    let KU := coherenceU.choose
    have hKU : KU.unitIso = MU.unitIso := coherenceU.choose_spec
    let F := ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U
    let A := ringedSliceLocalizationIso.{c, v, r, w, w'} J R U
    have comparisons := ringedSlice_evaluation_transpose.{c, v, r, w, w'}
      J R U M.closed M.models MU.closed MU.models
    let normalized := Classical.choice comparisons.1
    let d := normalized.val
    have hd := normalized.property
    have hrules := comparisons.2
    have he (L N) :=
      (hrules d hd ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op L, N))
        L N (M.closed.evaluation L N)).1
    have ht (V L N) (f : M.closed.tensor.obj (V, L) ⟶ N) :=
      (hrules d hd V L N f).2.1
    have hs (L N) : F.map (M.symmetric.braiding L N).hom ≫ (d.rho N L).hom =
        (d.rho L N).hom ≫ (MU.symmetric.braiding (F.obj L) (F.obj N)).hom := by
      have hσ := ringedSiteNormalizedSymmetry_eq J R M.closed M.models M.symmetric K
        d.sigma d.sigma_naturality hd.2.2.1
      have hσU := ringedSiteNormalizedSymmetry_eq.{max c v, v, r, w'}
        (J.over U) (R.over U) MU.closed MU.models MU.symmetric KU
        d.sigmaU d.sigmaU_naturality hd.2.2.2
      rw [← hσ L N, ← hσU (F.obj L) (F.obj N)]
      exact (hrules d hd _ L N (M.closed.evaluation L N)).2.2
    have ha := ringedSlice_tensor_associator.{c, v, r, w, w'}
      J R U M.closed M.models M.symmetric K MU.closed MU.models MU.symmetric KU d hd
    have hunit := ringedSlice_scalar_unit.{c, v, r, w, w'}
      J R U M.closed M.models M.symmetric K MU.closed MU.models MU.symmetric KU d hd
    let o : F.obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅
        ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U) := hunit.choose
    let t := ringedSiteRestrictionTensorIso M.closed MU.closed d
    let h := ringedSiteRestrictionHomIso M.closed MU.closed d
    have result := ringedSiteRestriction_assembly M.closed MU.closed M.symmetric MU.symmetric
      d he ht hs ha _ _ M.unitIso MU.unitIso o (by
        have hr := hunit.choose_spec
        dsimp only [ringedTensorUnitComplex] at hr
        set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
         simpa only [o, hK, hKU, ringedSiteDualityUnit,
          ringedSiteDualityUnitComplex, RingedTensorModules] using hr)
    ⟨F, ⟨by simpa only [F, ringedSiteRestrictionComplex_eq] using A⟩,
      t, h, o, result⟩

end Site
end CategoryTheory
