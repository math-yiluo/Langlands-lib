/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Pullback and scalar extension on entire algebra diagrams

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E,
with the scalar/unit refinement on diagram sites in proof steps 1--6
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence).

The presentation records below specify the existing functors and their normalized
comparison maps. They impose no flatness condition on the coefficient algebra.
The interface is recorded by def-pur-algebra-diagram-pullback-data
(blueprint: def-pur-algebra-diagram-pullback-data).

## Main declarations

* `ScalarDerivedPresentation` fixes scalar extension and its representative unit.
* `Coherence` records the two normalized comparisons and their coherence equations.
* `algebraDiagramPullbackExtensionCoherence` supplies these for entire diagram sites.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.PullbackTensorCanonical.canonicalDerivedTensor
attribute [local irreducible] SheafOfModules.PullbackTensorCanonical.canonicalRepresentativeIso
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
attribute [local irreducible] CategoryTheory.Functor.curry
attribute [local irreducible] CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.mapBifunctorHomologicalComplex
attribute [local irreducible] HomologicalComplex₂.total
attribute [local irreducible] HomologicalComplex.single
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback
open SheafOfModules.KFlatFixedTensor hiding Modules
open SheafOfModules.PullbackTensorCanonical

namespace CategoryTheory.AlgebraDiagramPullback

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  {R B : Sheaf K CommRingCat.{u}}

/-- The regular algebra as a module over its base, with the actual restriction maps.
Source: Stacks 03CY, proof step 3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
abbrev coefficient (a : R ⟶ B) : Modules.{u, u, u} R :=
  (restrictionFunctor.{u, u, u, u} a).obj
    (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))

/-- The coefficient module placed in degree zero.
Source: Stacks 07A4, proof step 3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
abbrev coefficientComplex (a : R ⟶ B) : Complex.{u, u, u} R :=
  (HomologicalComplex.single (Modules.{u, u, u} R) (.up ℤ) 0).obj (coefficient a)

/-- Presentation of the ordinary tensor/scalar identification, normalized on the
sheafification images of local tensors. Its naturality includes horizontal arrows
when K is a diagram-site topology.
Source: Stacks 03EK, 03CY, proof steps 2--3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
structure ScalarTensorPresentation (a : R ⟶ B) where
  iso : (curriedTensor (Modules.{u, u, u} R)).flip.obj (coefficient a) ≅
    extensionFunctor.{u, u, u} a ⋙ restrictionFunctor.{u, u, u, u} a
  pure : ∀ (M : Modules.{u, u, u} R) (V : Cᵒᵖ) (m : M.val.obj V) (b : B.obj.obj V),
    (iso.hom.app M).val.app V
      ((SheafOfModules.tensorObjIsoSheafification M (coefficient a)).inv.val.app V
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
            (M.val ⊗ (coefficient a).val)).app V (m ⊗ₜ[R.obj.obj V] b))) =
      extensionTmul.{u, u, u} a M V b m

/-- The corresponding actual chain isomorphism, using the single-factor total
identification and the termwise lift of the specified ordinary tensor comparison.
Source: Stacks 07A4, proof steps 2--3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def ScalarTensorPresentation.total {a : R ⟶ B} (t : ScalarTensorPresentation a)
    (P : Complex.{u, u, u} R) : P ⊗ coefficientComplex a ≅
      (restrictComplex.{u, u, u, u} a).obj ((extend.{u, u, u} a).obj P) :=
  CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules.{u, u, u} R)) (coefficient a) P ≪≫
    (Functor.mapHomologicalComplexCompIso t.iso.symm (.up ℤ)).symm.app P

/-- Exactness facts needed to write the termwise-localized restriction functor.
They are conclusions of the main theorem, rather than extra algebra hypotheses.
Source: Stacks 03CY, proof step 1
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
class ExactRestriction (a : R ⟶ B) where
  [limits : PreservesFiniteLimits (restrictionFunctor.{u, u, u, u} a)]
  [colimits : PreservesFiniteColimits (restrictionFunctor.{u, u, u, u} a)]

attribute [instance] ExactRestriction.limits ExactRestriction.colimits

variable [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} B)]

/-- Tensoring by the actual underlying coefficient complex in the published derived tensor.
Source: Stacks 06YY and 07A4, proof step 3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def scalarTensorFunctor (a : R ⟶ B) :
    DerivedCategory (Modules.{u, u, u} R) ⥤ DerivedCategory (Modules.{u, u, u} R) :=
  (canonicalDerivedTensor.{u, u, u, w} R).flip.obj
    (DerivedCategory.Q.{w}.obj (coefficientComplex a))

/-- The identity identification of the fixed-coefficient tensor with its bifunctor value.
Source: Stacks 06YY and 07A4, proof step 3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def scalarTensorComparison (a : R ⟶ B) : scalarTensorFunctor.{u, w} a ≅
    (canonicalDerivedTensor.{u, u, u, w} R).flip.obj
      (DerivedCategory.Q.{w}.obj (coefficientComplex a)) := Iso.refl _

attribute [local irreducible] scalarTensorFunctor scalarTensorComparison

/-- The ordinary scalar-extension unit lifted to actual complexes, with the canonical
identity and composition identifications made explicit.
Source: Stacks 03CY and 06YY, proof step 5
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def scalarCochainUnit (a : R ⟶ B) : 𝟭 (Complex.{u, u, u} R) ⟶
    extend.{u, u, u} a ⋙ restrictComplex.{u, u, u, u} a :=
  (Functor.mapHomologicalComplexIdIso (Modules.{u, u, u} R) (.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex (extensionAdjunction.{u, u, u} a).unit (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      (extensionFunctor.{u, u, u} a ⋙ restrictionFunctor.{u, u, u, u} a)) (.up ℤ)).inv

attribute [local irreducible] scalarCochainUnit

/-- Representative normalization of the derived scalar-extension unit.
Source: Stacks 03CY and 06YY, proof step 5
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def IsNormalizedScalarUnit
    (a : R ⟶ B) [e : ExactRestriction a]
    (model : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (ordinary : model.E ≅ extensionFunctor.{u, u, u} a)
    (adj : model.T ⊣ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}) :
    Prop :=
  ∀ (P : Complex.{u, u, u} R), P.IsKFlatIndependentCoefficients →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (J := K) (R := R) (P.X n)) →
  adj.unit.app (DerivedCategory.Q.{w}.obj P) ≫
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}.map (model.ε.app P) ≫
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategoryFactors.{w, w}.hom.app
        ((model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.{w}.map ((restrictComplex.{u, u, u, u} a).map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)) =
    DerivedCategory.Q.{w}.map
      ((scalarCochainUnit a).app P)

/-- Two-resolving-factor normalization of underlying derived scalar extension.
Source: Stacks 06YY and 07A4, proof step 3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def IsNormalizedScalarTensor
    (a : R ⟶ B) [e : ExactRestriction a]
    (model : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (ordinary : model.E ≅ extensionFunctor.{u, u, u} a)
    (tensor : ScalarTensorPresentation a)
    (underlyingIso : model.T ⋙ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w} ≅
      scalarTensorFunctor.{u, w} a) : Prop :=
  ∀ (P Q : Complex.{u, u, u} R) (hp : P.IsKFlatIndependentCoefficients)
  (hq : Q.IsKFlatIndependentCoefficients)
  (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (J := K) (R := R) (P.X n))
  (hg : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (J := K) (R := R) (Q.X n))
  (q : Q ⟶ coefficientComplex a), QuasiIso q →
    (canonicalRepresentativeIso.{u, u, u, w} R P Q hp hq hf hg).hom ≫
        (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} R)).map
          (Prod.mkHom (𝟙 (DerivedCategory.Q.{w}.obj P)) (DerivedCategory.Q.{w}.map q)) ≫
        (scalarTensorComparison a).inv.app (DerivedCategory.Q.{w}.obj P) ≫
        underlyingIso.inv.app (DerivedCategory.Q.{w}.obj P) ≫
        (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}.map (model.ε.app P) ≫
        (restrictionFunctor.{u, u, u, u} a).mapDerivedCategoryFactors.{w, w}.hom.app
          ((model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.{w}.map ((restrictComplex.{u, u, u, u} a).map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)) =
      DerivedCategory.Q.{w}.map
        ((((totalTensor R).obj P).map q) ≫ (tensor.total P).hom)

attribute [local irreducible] IsNormalizedScalarUnit IsNormalizedScalarTensor

/-- A normalized presentation of scalar extension, its unit and its underlying
derived tensor. All ordinary and derived categories here are the dependencies'
existing categories; the counit fixes the derived extension on K-flat models.
Source: Stacks 06YY and 07A4, proof steps 2--3 and 5
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
structure ScalarDerivedPresentation (a : R ⟶ B) [e : ExactRestriction a] where
  model : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a
  ordinary : model.E ≅ extensionFunctor.{u, u, u} a
  ordinary_hom : ∀ M : Modules.{u, u, u} R, ordinary.hom.app M = eqToHom (model.obj_eq M)
  adj : model.T ⊣ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}
  tensor : ScalarTensorPresentation a
  underlyingIso : model.T ⋙ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w} ≅
    scalarTensorFunctor.{u, w} a
  unit_model : IsNormalizedScalarUnit a model ordinary adj
  tensor_model : IsNormalizedScalarTensor a model ordinary tensor underlyingIso

variable {D : Type u} [SmallCategory D] {L : GrothendieckTopology D}
  {S : Sheaf L CommRingCat.{u}}

/-- Exactness of an inverse image whose structural coefficient map is invertible.
This is output data, not a flatness assumption on the algebra extension.
Source: Stacks 03D2 and 0G7E, proof step 1
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
class ExactPullback (f : RingedPullback.{u, u, u, u, u} R S) where
  [limits : PreservesFiniteLimits f.L]
  [colimits : PreservesFiniteColimits f.L]

attribute [instance] ExactPullback.limits ExactPullback.colimits

variable (f : RingedPullback.{u, u, u, u, u} R S)
  (k : Comparison.{u, u, u, u, u} f) (d : CoefficientSquare.{u, u, u, u, u} f)
  (k' : Comparison.{u, u, u, u, u} (changed f d))
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
  [ef : ExactPullback f] [eg : ExactPullback (changed f d)]
  [ey : ExactRestriction d.sourceMap] [ex : ExactRestriction d.targetMap]

/-- The degree-zero coefficient identification after exact derived pullback.
It uses the existing exact factorization and single-complex functoriality.
Source: Stacks 07A4, proof step 3
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def derivedCoefficientIso
    (beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap) :
    f.L.mapDerivedCategory.{w, w}.obj (DerivedCategory.Q.{w}.obj (coefficientComplex d.sourceMap)) ≅
      DerivedCategory.Q.{w}.obj (coefficientComplex d.targetMap) :=
  f.L.mapDerivedCategoryFactors.{w, w}.app (coefficientComplex d.sourceMap) ≪≫
    DerivedCategory.Q.{w}.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex f.L (.up ℤ) 0).app
          (coefficient d.sourceMap) ≪≫
        (HomologicalComplex.single (Modules.{u, u, u} S) (.up ℤ) 0).mapIso beta)

/-- The exact source and target of the scalar-association comparison on derived objects.
Source: Stacks 03EL and 07A4, proof step 2
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def ExtensionComparison
    (source : ScalarDerivedPresentation.{u, w} d.sourceMap)
    (target : ScalarDerivedPresentation.{u, w} d.targetMap) : Type (max (u + 1) w) :=
  (source.model.T ⋙ (changed f d).L.mapDerivedCategory.{w, w} :
    DerivedCategory (Modules.{u, u, u} R) ⥤ DerivedCategory (Modules.{u, u, u} d.S')) ≅
  (f.L.mapDerivedCategory.{w, w} ⋙ target.model.T :
    DerivedCategory (Modules.{u, u, u} R) ⥤ DerivedCategory (Modules.{u, u, u} d.S'))

/-- Localization of the specified balanced cochain association on resolving representatives.
Source: Stacks 03EL and 07A4, proof step 2
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def IsNormalizedExtension
    (source : ScalarDerivedPresentation.{u, w} d.sourceMap)
    (target : ScalarDerivedPresentation.{u, w} d.targetMap)
    (extension : ExtensionComparison f d source target) : Prop :=
  ∀ (P : Complex.{u, u, u} R), P.IsKFlatIndependentCoefficients →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (J := K) (R := R) (P.X n)) →
  (changed f d).L.mapDerivedCategory.{w, w}.map (source.model.ε.app P) ≫
      (changed f d).L.mapDerivedCategoryFactors.{w, w}.hom.app
        ((source.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.{w}.map
        ((pull.{u, u, u, u, u} (changed f d)).map
            ((NatIso.mapHomologicalComplex source.ordinary (.up ℤ)).hom.app P) ≫
          (kappa f k d k' P).hom ≫
          (NatIso.mapHomologicalComplex target.ordinary (.up ℤ)).inv.app
            ((pull.{u, u, u, u, u} f).obj P)) =
    extension.hom.app (DerivedCategory.Q.{w}.obj P) ≫
      target.model.T.map (f.L.mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
      target.model.ε.app ((pull.{u, u, u, u, u} f).obj P)

attribute [local irreducible] IsNormalizedExtension

/-- The complete comparison on the ringed diagram sites. Ordinary b is specified
on all generalized inverse-image generators; c is specified by the existing kappa
on every flat-term K-flat representative. The tensor comparison is independently
normalized on two resolving factors, before specializing its coefficient argument.
Source: Stacks 03EL, 07A4, 0G7E, proof steps 1--6
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
structure Coherence where
  source : ScalarDerivedPresentation.{u, w} d.sourceMap
  target : ScalarDerivedPresentation.{u, w} d.targetMap
  ordinaryRestriction : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
    (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap
  restriction_generators : ∀ (H : Modules.{u, u, u} d.R') (Z : Sheaf K (Type u))
    (x : Z ⟶ (underlying.{u, u, u} d.R').obj H),
    generator f k (M := (restrictionFunctor.{u, u, u, u} d.sourceMap).obj H) x ≫
        (underlying.{u, u, u} S).map (ordinaryRestriction.hom.app H) =
      generator (changed f d) k' (M := H) x
  restriction : (restrictionFunctor.{u, u, u, u} d.sourceMap).mapDerivedCategory.{w, w} ⋙
      f.L.mapDerivedCategory.{w, w} ≅
    (changed f d).L.mapDerivedCategory.{w, w} ⋙
      (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.{w, w}
  restriction_model : ∀ H : Complex.{u, u, u} d.R',
    f.L.mapDerivedCategory.{w, w}.map
        ((restrictionFunctor.{u, u, u, u} d.sourceMap).mapDerivedCategoryFactors.{w, w}.hom.app H) ≫
        f.L.mapDerivedCategoryFactors.{w, w}.hom.app ((restrictComplex.{u, u, u, u}
          d.sourceMap).obj H) ≫
        DerivedCategory.Q.{w}.map
          ((Functor.mapHomologicalComplexCompIso ordinaryRestriction (.up ℤ)).hom.app H ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl ((changed f d).L ⋙
              restrictionFunctor.{u, u, u, u} d.targetMap)) (.up ℤ)).inv.app H) =
      restriction.hom.app (DerivedCategory.Q.{w}.obj H) ≫
        (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.{w, w}.map
          ((changed f d).L.mapDerivedCategoryFactors.{w, w}.hom.app H) ≫
        (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategoryFactors.{w, w}.hom.app
          ((pull.{u, u, u, u, u} (changed f d)).obj H)
  extension : ExtensionComparison f d source target
  extension_model : IsNormalizedExtension f k d k' source target extension
  beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap
  beta_generators : ∀ (Z : Sheaf K (Type u))
    (x : Z ⟶ (underlying.{u, u, u} R).obj (coefficient d.sourceMap)),
    generator f k (M := coefficient d.sourceMap) x ≫ (underlying.{u, u, u} S).map beta.hom =
      f.uInv.map x ≫ d.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u})).map d.coefficient'
  ambient : Phi f.L.mapDerivedCategory.{w, w} ≅ Psi f.L.mapDerivedCategory.{w, w}
  ambient_model : IsNormalized f k f.L.mapDerivedCategory.{w, w}
    f.L.mapDerivedCategoryFactors.{w, w}.hom ambient.hom
  theta : (source.model.T ⋙ (restrictionFunctor.{u, u, u, u}
      d.sourceMap).mapDerivedCategory) ⋙ f.L.mapDerivedCategory.{w, w} ≅
    f.L.mapDerivedCategory.{w, w} ⋙ target.model.T ⋙
      (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.{w, w}
  theta_ambient : ∀ M : DerivedCategory (Modules.{u, u, u} R),
    theta.hom.app M =
      f.L.mapDerivedCategory.{w, w}.map (source.underlyingIso.hom.app M) ≫
        f.L.mapDerivedCategory.{w, w}.map
          ((scalarTensorComparison d.sourceMap).hom.app M) ≫
        ambient.hom.app (M, DerivedCategory.Q.{w}.obj (coefficientComplex d.sourceMap)) ≫
        (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} S)).map
          (Prod.mkHom (𝟙 (f.L.mapDerivedCategory.{w, w}.obj M))
            (derivedCoefficientIso f d beta).hom) ≫
        (scalarTensorComparison d.targetMap).inv.app (f.L.mapDerivedCategory.{w, w}.obj M) ≫
        target.underlyingIso.inv.app (f.L.mapDerivedCategory.{w, w}.obj M)
  tensor_coherence : ∀ M : DerivedCategory (Modules.{u, u, u} R),
    restriction.hom.app (source.model.T.obj M) ≫
        (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.{w, w}.map
          (extension.hom.app M) = theta.hom.app M
  unit_coherence : ∀ M : DerivedCategory (Modules.{u, u, u} R),
    f.L.mapDerivedCategory.{w, w}.map (source.adj.unit.app M) ≫ theta.hom.app M =
      target.adj.unit.app (f.L.mapDerivedCategory.{w, w}.obj M)

/-- The actual scalar-extension map induced by a map of coefficient modules,
transported through the normalized underlying tensor presentations. Thus its data
comes from the existing derived tensor functor, not from an arbitrary chosen map.
Source: Stacks 07A4, proof step 6
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def scalarUnderlyingMap {B' : Sheaf K CommRingCat.{u}} {a : R ⟶ B} {a' : R ⟶ B'}
    [HasDerivedCategory.{w} (Modules.{u, u, u} B')]
    [e : ExactRestriction a] [e' : ExactRestriction a']
    (s : ScalarDerivedPresentation.{u, w} a) (t : ScalarDerivedPresentation.{u, w} a')
    (h : coefficient a ⟶ coefficient a') :
    s.model.T ⋙ (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w} ⟶
      t.model.T ⋙ (restrictionFunctor.{u, u, u, u} a').mapDerivedCategory.{w, w} :=
  s.underlyingIso.hom ≫ (scalarTensorComparison a).hom ≫
    (canonicalDerivedTensor.{u, u, u, w} R).flip.map
      (DerivedCategory.Q.{w}.map ((HomologicalComplex.single
        (Modules.{u, u, u} R) (.up ℤ) 0).map h)) ≫
    (scalarTensorComparison a').inv ≫ t.underlyingIso.inv

/-- Compatibility with every compatible map of algebra diagrams. The supplied
module maps hY and hX are fixed sectionwise to the ring maps, so quantify over
presentations of those canonical maps only. Both equations live in the derived
category of the whole diagram site.
Source: Stacks 03EL and 07A4, proof step 6
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
def Coherence.CoefficientNaturality (q : Coherence f k d k') : Prop :=
  ∀ (d' : CoefficientSquare.{u, u, u, u, u} f)
    (k'' : Comparison.{u, u, u, u, u} (changed f d'))
    [HasDerivedCategory.{w} (Modules.{u, u, u} d'.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d'.S')]
    [_eg' : ExactPullback (changed f d')]
    [_ey' : ExactRestriction d'.sourceMap] [_ex' : ExactRestriction d'.targetMap]
    (q' : Coherence f k d' k'') (psiY : d.R' ⟶ d'.R') (psiX : d.S' ⟶ d'.S'),
    d.sourceMap ≫ psiY = d'.sourceMap → d.targetMap ≫ psiX = d'.targetMap →
    f.uInv.map ((sheafCompose K (forget CommRingCat.{u})).map psiY) ≫
        d'.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u})).map d'.coefficient' =
      d.I'.ringUnderlying.hom ≫
        (sheafCompose L (forget CommRingCat.{u})).map d.coefficient' ≫
        (sheafCompose L (forget CommRingCat.{u})).map psiX →
    ∀ (hY : coefficient d.sourceMap ⟶ coefficient d'.sourceMap)
      (hX : coefficient d.targetMap ⟶ coefficient d'.targetMap),
      (∀ (V : Cᵒᵖ) (b : d.R'.obj.obj V), hY.val.app V b = psiY.hom.app V b) →
      (∀ (V : Dᵒᵖ) (b : d.S'.obj.obj V), hX.val.app V b = psiX.hom.app V b) →
      ∀ M : DerivedCategory (Modules.{u, u, u} R),
        f.L.mapDerivedCategory.{w, w}.map
            ((scalarUnderlyingMap q.source q'.source hY).app M) ≫ q'.theta.hom.app M =
          q.theta.hom.app M ≫
            (scalarUnderlyingMap q.target q'.target hX).app
              (f.L.mapDerivedCategory.{w, w}.obj M) ∧
        q.source.adj.unit.app M ≫ (scalarUnderlyingMap q.source q'.source hY).app M =
          q'.source.adj.unit.app M ∧
        q.target.adj.unit.app (f.L.mapDerivedCategory.{w, w}.obj M) ≫
            (scalarUnderlyingMap q.target q'.target hX).app
              (f.L.mapDerivedCategory.{w, w}.obj M) =
          q'.target.adj.unit.app (f.L.mapDerivedCategory.{w, w}.obj M)

end CategoryTheory.AlgebraDiagramPullback

namespace CategoryTheory.AlgebraDiagramPullback

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
  (f : RingedPullback.{u, u, u, u, u} R S)
  (k : Comparison.{u, u, u, u, u} f) (d : CoefficientSquare.{u, u, u, u, u} f)
  (k' : Comparison.{u, u, u, u, u} (changed f d))
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]

/-- All conclusions, including exactness, so no exactness assumption is imposed
on input scalar extension or its coefficient algebra.
Source: Stacks 03D2, 03CY, 07A4 and 0G7E, proof steps 1--6
(blueprint: lem-pur-algebra-diagram-pullback-extension-coherence). -/
structure Result where
  [base_exact : ExactPullback f]
  [algebra_exact : ExactPullback (changed f d)]
  [source_restriction_exact : ExactRestriction d.sourceMap]
  [target_restriction_exact : ExactRestriction d.targetMap]
  comparison : Coherence f k d k'
  coefficient_naturality : comparison.CoefficientNaturality f k d k'

end CategoryTheory.AlgebraDiagramPullback

namespace CategoryTheory.AlgebraDiagramPullback

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (K : GrothendieckTopology C) (L : GrothendieckTopology D) (A : Type u) [CommRing A]
  (f : RingedPullback.{u, u, u, u, u}
    ((constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A))
    ((constantSheaf L CommRingCat.{u}).obj (CommRingCat.of A)))

end CategoryTheory.AlgebraDiagramPullback
