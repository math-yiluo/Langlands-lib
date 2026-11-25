/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorTransport
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Finite exterior and tensor-dual Koszul comparison

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison).

The site and coefficient transports are publicly re-exported from the lower site module.
The termwise-limit comparison is constructed here. The finite comparison is assembled
from coefficient comparison and tensor transport, including transitions and augmentation.
Products, cones and derived transport are proved by consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison between limits of complexes and termwise limits.
Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison). -/
def completedKoszulTermwiseLimitIso {B : Type*} [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ≅
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.coneOfHasLimitEval_π_app_f,
      HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)

private theorem tensorComparison_transition
    {D E V : Type*} [Category* D] [Category* E] [Category* V]
    (L : D ⥤ V) (H : D ⥤ E) (U : E ⥤ V) (s : L ≅ H ⋙ U)
    {x y : D} (f : x ⟶ y) {a b : E} (α : H.obj y ⟶ a) (β : H.obj x ⟶ b)
    (g : b ⟶ a) (h : H.map f ≫ α = β ≫ g) :
    L.map f ≫ (s.hom.app y ≫ U.map α) =
      (s.hom.app x ≫ U.map β) ≫ U.map g := by
  rw [← Category.assoc, s.hom.naturality, Functor.comp_map, Category.assoc,
    ← U.map_comp, h, U.map_comp, Category.assoc]

private theorem towerComplex_map_eq
    {S : Type*} [SmallCategory S] {J : GrothendieckTopology S}
    (O : Sheaf J CommRingCat) (r : ℕ)
    (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (N : ringedSiteComplex O) {m n : ℕᵒᵖ} (f : m ⟶ n) (q : ℤ) :
    ((ringedKoszulTensorTowerComplex O r b N).asFunctor.map f).f q =
      (((ringedKoszulTensor O).obj N).map ((ringedKoszulDualTower O r b).map f)).f q := rfl

private def towerTransposeIso
    {S : Type*} [SmallCategory S] {J : GrothendieckTopology S}
    (O : Sheaf J CommRingCat) (r : ℕ)
    (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (N : ringedSiteComplex O) (m : ℕ) :
    ((ringedKoszulTensor O).obj N).obj ((ringedKoszulDualTower O r b).obj (op m)) ≅
      (ringedKoszulTensorTowerComplex O r b N).asFunctor.obj (op m) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro p q hpq
    have h : p + 1 = q := hpq
    subst q
    simp only [ringedKoszulTensorTowerComplex, HomologicalComplex.asFunctor_obj_d,
      CochainComplex.of_d, Iso.refl_hom]
    rfl)

private theorem towerTransposeIso_hom_f
    {S : Type*} [SmallCategory S] {J : GrothendieckTopology S}
    (O : Sheaf J CommRingCat) (r : ℕ)
    (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (N : ringedSiteComplex O) (m : ℕ) (q : ℤ) :
    ((towerTransposeIso O r b N m).hom).f q = 𝟙 _ := rfl

private theorem towerTranspose_transition
    {S : Type*} [SmallCategory S] {J : GrothendieckTopology S}
    (O : Sheaf J CommRingCat) (r : ℕ)
    (b : Fin r → (O.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (N : ringedSiteComplex O) {m n : ℕ} (f : op m ⟶ op n)
    {P Q : ringedSiteComplex O} (g : P ⟶ Q)
    (α : Q ⟶ ((ringedKoszulTensor O).obj N).obj
      ((ringedKoszulDualTower O r b).obj (op n)))
    (β : P ⟶ ((ringedKoszulTensor O).obj N).obj
      ((ringedKoszulDualTower O r b).obj (op m)))
    (h : g ≫ α = β ≫ ((ringedKoszulTensor O).obj N).map
      ((ringedKoszulDualTower O r b).map f)) :
    g ≫ α ≫ (towerTransposeIso O r b N n).hom =
      (β ≫ (towerTransposeIso O r b N m).hom) ≫
        (ringedKoszulTensorTowerComplex O r b N).asFunctor.map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  simpa only [HomologicalComplex.comp_f, towerTransposeIso_hom_f,
    Category.comp_id, towerComplex_map_eq] using
    congrArg (fun k ↦ HomologicalComplex.Hom.f k q) h

private theorem tensor_unit_component
    {V : Type*} [Category* V] [Preadditive V] [HasZeroObject V]
    [MonoidalCategory V] [MonoidalPreadditive V]
    [∀ (K L : CochainComplex V ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor V) (.up ℤ)]
    (N K Q : CochainComplex V ℤ) (f : K ⟶ Q)
    (v : (HomologicalComplex.single V (.up ℤ) 0).obj (𝟙_ V) ⟶ Q)
    (u : 𝟙_ V ⟶ K.X 0)
    (h : u ≫ f.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ v.f 0) (q : ℤ) :
    ((ρ_ (N.X q)).inv ≫ N.X q ◁ u ≫
      HomologicalComplex.ιMapBifunctor N K (curriedTensor V) (.up ℤ)
        q 0 q (add_zero q)) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 N) f (curriedTensor V) (.up ℤ)).f q =
    (HomologicalComplex.rightUnitor N).inv.f q ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 N) v (curriedTensor V) (.up ℤ)).f q := by
  rw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map]
  erw [Category.id_comp, ← whiskerLeft_comp_assoc, h]
  change _ = (HomologicalComplex.rightUnitor' N).inv q ≫ _
  rw [HomologicalComplex.rightUnitor'_inv, Category.assoc, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map, whiskerLeft_comp, Category.assoc]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringedTensor_unit_component
    {S : Type*} [SmallCategory S] {J : GrothendieckTopology S}
    (O : Sheaf J CommRingCat) (N K Q : ringedSiteComplex O)
    (f : K ⟶ Q) (v : ringedSiteRingComplex O ⟶ Q)
    (u : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶ K.X 0)
    (h : u ≫ f.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ v.f 0) (q : ℤ) :
    letI := SheafOfModules.monoidalCategory O
    ((ρ_ (N.X q)).inv ≫ N.X q ◁ u ≫
      HomologicalComplex.ιMapBifunctor N K (curriedTensor _) (.up ℤ)
        q 0 q (add_zero q)) ≫ (((ringedKoszulTensor O).obj N).map f).f q =
      ((ringedKoszulRightUnitIso O N).inv ≫ ((ringedKoszulTensor O).obj N).map v).f q := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.tensorPreadditive O
  exact tensor_unit_component N K Q f v u h q

attribute [local irreducible] towerTransposeIso
attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
attribute [local irreducible] completedCechModulesEquiv
attribute [local irreducible] completedKoszulConstant completedKoszulPower
attribute [local irreducible] ringedKoszulDualTower ringedKoszulDiagram

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The finite exterior Koszul tower agrees with the ordered tensor-dual tower.

Source: Stacks Project, more-algebra.tex Tag 0664, Lemma 15.29.12
(tensor decomposition), and algebraization.tex Tag 0A0E,
proof of lemma-derived-completion-koszul (finite-free duality identification).
(blueprint: lem-weil-pbc-completed-fiber-roos-comparison).

Proof: on the free module with ordered basis Fin r, use the sorted subset basis of
its exterior powers. A k-subset indexes degree -k. Identify its basis vector with the
dual tensor coordinate, multiplied by (-1)^(k*(k-1)/2). The ratio in adjacent degrees
is the sign in the Hom-complex differential, so the exterior contraction differential
agrees with the dual of the ordered positive tensor differential. This gives inverse
chain maps, identity in degree zero. The same calculation can be organized by induction
on r, splitting off the last exterior generator and the last two-term tensor factor.
Apply the actual constant-module construction and its completed coefficient extension.
The coefficient comparison is an isomorphism and the site change is an equivalence;
their tensor and finite-sum comparisons therefore carry this finite chain isomorphism
through the displayed functor H. Tensor with the arbitrary complex C: in each total
degree the Koszul coordinate has finite support, so the same coordinates give an
isomorphism on the total complexes. Use the identity-on-sections round trip to identify
the transported input with N. For a transition, both subset coordinates are multiplied
by the product of the corresponding generators, hence the chain isomorphisms commute
with the power transitions. In degree zero the empty subset has sign +1, giving exactly
the displayed augmentation equation. No products, inverse limits or cones occur here.

For r=0 both finite complexes are the tensor unit and the comparison is the unit
isomorphism. The formulas allow zero or invertible generators, a zero coefficient ring,
and an empty site; no regularity or generation hypothesis is used. -/
theorem completedKoszulFiniteComparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let G := (completedCechModulesEquiv X d).functor
    let H := (intrinsicPresentationModulesBack X d ⋙ G).mapHomologicalComplex (.up ℤ)
    let P := (intrinsicPresentationComplex X d).obj C
    let O := completedCechRing X d
    let b := fun i ↦ completedCechScalar X d (a i)
    let N := (G.mapHomologicalComplex (.up ℤ)).obj C
    let T := ringedKoszulTensorTowerComplex O r b N
    ∃ e : ∀ m : ℕ, H.obj
        (completedKoszulTensor X (intrinsicPresentationDatum d) r a P m) ≅
          T.asFunctor.obj (op m),
      (∀ m, H.map
          (completedKoszulTensorTransition X (intrinsicPresentationDatum d) r a P m) ≫
            (e m).hom = (e (m + 1)).hom ≫
              T.asFunctor.map (homOfLE (Nat.le_succ m)).op) ∧
      (∀ (m : ℕ) (q : ℤ),
        G.map ((intrinsicPresentationRoundTrip X d).hom.app (C.X q) ≫
          (intrinsicPresentationModulesBack X d).map
            ((completedKoszulTensorUnit X (intrinsicPresentationDatum d) r a P m).f q)) ≫
              (e m).hom.f q = (ringedKoszulTensorUnitComponent O r b N (op m)).f q)  := by
  let G := (completedCechModulesEquiv X d).functor
  let F := intrinsicPresentationModulesBack X d ⋙ G
  let H := F.mapHomologicalComplex (.up ℤ)
  let P := (intrinsicPresentationComplex X d).obj C
  let O := completedCechRing X d
  let b := fun i ↦ completedCechScalar X d (a i)
  let N := (G.mapHomologicalComplex (.up ℤ)).obj C
  let K := completedKoszulPowerSheaf X (intrinsicPresentationDatum d) r a
  let τ := fun m ↦ ((completedKoszulConstant X (intrinsicPresentationDatum d)
    ).mapHomologicalComplex (.up ℤ)).map (completedKoszulTransition (A := A) r a m)
  let U := (ringedKoszulTensor O).obj N
  obtain ⟨k, hk, hku⟩ := completedKoszulCoefficientComparison X d r a
  obtain ⟨s, hs⟩ := completedCechTensorTransport X d C
  let T := ringedKoszulTensorTowerComplex O r b N
  let j := towerTransposeIso O r b N
  let e := fun m ↦ (s.app (K m) ≪≫ U.mapIso (k m)) ≪≫ j m
  refine ⟨e, ?_, ?_⟩
  · intro m
    have ht : H.map (completedKoszulTensorTransition X (intrinsicPresentationDatum d) r a P m) ≫
      (s.hom.app (K m) ≫ U.map (k m).hom) =
        (s.hom.app (K (m + 1)) ≫ U.map (k (m + 1)).hom) ≫
          U.map ((ringedKoszulDualTower O r b).map (homOfLE (Nat.le_succ m)).op) := by
      exact tensorComparison_transition _ H U s (τ m) (k m).hom (k (m + 1)).hom
        ((ringedKoszulDualTower O r b).map (homOfLE (Nat.le_succ m)).op) (hk m)
    exact towerTranspose_transition O r b N (homOfLE (Nat.le_succ m)).op
      (H.map (completedKoszulTensorTransition X (intrinsicPresentationDatum d) r a P m))
      (s.hom.app (K m) ≫ U.map (k m).hom)
      (s.hom.app (K (m + 1)) ≫ U.map (k (m + 1)).hom) ht
  · intro m q
    let := SheafOfModules.monoidalCategory O
    dsimp only [e, j]
    erw [Iso.trans_hom, HomologicalComplex.comp_f, towerTransposeIso_hom_f,
      Category.comp_id]
    erw [Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom,
      ← Category.assoc]
    have hu := hs r a m q
    have hv := ringedTensor_unit_component (completedCechRing X d)
      ((G.mapHomologicalComplex (.up ℤ)).obj C)
      (((intrinsicPresentationModulesBack X d ⋙ G).mapHomologicalComplex (.up ℤ)).obj
        (completedKoszulPowerSheaf X (intrinsicPresentationDatum d) r a m)) _ (k m).hom
      (ringedKoszulDualUnit (completedCechRing X d) r
        (fun i ↦ completedCechScalar X d (a i)) m)
      (completedCechCoefficientUnit X d ≫ F.map
        (completedKoszulSheafUnitZero X (intrinsicPresentationDatum d) r a m))
      ((Category.assoc _ _ _).trans (hku m)) q
    dsimp only [F, G] at hv
    have hw := congrArg (fun f ↦ f ≫ (U.map (k m).hom).f q) hu
    exact hw.trans hv

end AlgebraicGeometry.Scheme
