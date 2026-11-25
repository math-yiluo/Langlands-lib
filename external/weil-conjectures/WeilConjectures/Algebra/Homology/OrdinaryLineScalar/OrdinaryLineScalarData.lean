/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Data for ordinary signed-line scalar comparison

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint Tate-twist local freeness,
proof (3).
(blueprint: def-pur-ordinary-line-scalar-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

/-- The existing module category on the small pro-etale site.
Source: Stacks 03DA (blueprint: def-pur-ordinary-line-scalar-data). -/
abbrev Modules (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}) :=
  LineUnbounded.Modules.{t, a} X R

/-- Cache the existing category instance without changing its data.
(blueprint: def-pur-ordinary-line-scalar-data). -/
local instance modulesCategory (R : Sheaf (Scheme.ProEt.topology X)
    CommRingCat.{max a (t + 1)}) : Category (Modules.{t, a} X R) := inferInstance
/-- Cache the existing abelian instance without changing its data.
(blueprint: def-pur-ordinary-line-scalar-data). -/
local instance modulesAbelian (R : Sheaf (Scheme.ProEt.topology X)
    CommRingCat.{max a (t + 1)}) : Abelian (Modules.{t, a} X R) := inferInstance
/-- Cache the existing monoidal instance without changing its data.
(blueprint: def-pur-ordinary-line-scalar-data). -/
local instance modulesMonoidal (R : Sheaf (Scheme.ProEt.topology X)
    CommRingCat.{max a (t + 1)}) : MonoidalCategory (Modules.{t, a} X R) := inferInstance

attribute [-instance] modulesMonoidal
attribute [local instance] monoidalCategory
attribute [local implicit_reducible] monoidalCategory

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]

local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))

/-- The recorded signed powers, with no new choice of dual.
Source: blueprint proof (3) (blueprint: def-pur-ordinary-line-scalar-data). -/
abbrev power {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) (m : ℤ) := signedLinePower.{t + 1, t, a} L m

/-- The ordinary additive line-tensor functor.
Source: Stacks 03EK (blueprint: def-pur-ordinary-line-scalar-data). -/
abbrev tensor {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) (m : ℤ) := LineUnbounded.tensor.{t, a} X R (power.{t, a} L m)

/-- The published K-flat derived tensor with the signed power in degree zero.
Source: Stacks 06YU (blueprint: def-pur-ordinary-line-scalar-data). -/
abbrev twist {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) (m : ℤ) := LineUnbounded.derived.{t, a, w} X R (power.{t, a} L m)

/-- Flat-term K-flat is the conjunction of the two recorded predicates.
Source: Stacks 06YN (blueprint: def-pur-ordinary-line-scalar-data). -/
def FlatModel {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (P : CochainComplex (Modules.{t, a} X R) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
    ∀ n : ℤ, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) (R := R) (P.X n)

/-- The canonical cochain computation map of a universal homotopy-category presentation.
Only the published quotient comparison is inserted; no map is chosen.
Source: Stacks 06YY (blueprint: def-pur-ordinary-line-scalar-data). -/
def compute {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    {α : R ⟶ S} (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (P : CochainComplex (Modules.{t, a} X R) ℤ) :
    p.derived.obj (𝒬[R].obj P) ⟶
      𝒬[S].obj ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) :=
  p.derived.map ((DerivedCategory.quotientCompQhIso (Modules.{t, a} X R)).inv.app P) ≫
    p.counit.app ((HomotopyCategory.quotient (Modules.{t, a} X R) (.up ℤ)).obj P) ≫
    (DerivedCategory.Qh (C := Modules.{t, a} X S)).map
      ((p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (Modules.{t, a} X S)).hom.app
      ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)

/-- Pure scalar tensor in the ordinary presentation, transported by its fixed object equation.
Source: Stacks 03EK (blueprint: def-pur-ordinary-line-scalar-data). -/
def scalar {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    {α : R ⟶ S} (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (p.ordinary.obj M).val.obj U :=
  (eqToHom (p.obj_eq M).symm).val.app U (scalarExtensionSection α M U s x)

attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  KFlatFixedTensor.representativeIso compute signedLinePower scalarTensorPower
  LineUnbounded.cancellation LineUnbounded.pureTensor

/-- Fixed exact termwise and derived line tensors, with actual signed evaluation.
The evaluation is characterized on every local signed basis, hence is not a freely
chosen equivalence counit. Source: blueprint proof (3), Stacks 03EK and 06YU
(blueprint: def-pur-ordinary-line-scalar-data). -/
structure LineData {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (L : Modules.{t, a} X R) where
  rank : ∀ m : ℤ, (power.{t, a} L m).IsFiniteLocallyFreeOfRank 1
  exact : ∀ m : ℤ, PreservesFiniteLimits (tensor.{t, a} L m) ∧
    PreservesFiniteColimits (tensor.{t, a} L m)
  single_flat : ∀ m : ℤ, FlatModel (LineUnbounded.single.{t, a} X R (power.{t, a} L m))
  factors : ∀ m : ℤ, 𝒬[R] ⋙ twist.{t, a, w} L m ≅
    (tensor.{t, a} L m).mapHomologicalComplex (.up ℤ) ⋙ 𝒬[R]
  factors_normalized : ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ),
    LineUnbounded.normalization.{t, a, w} X R (power.{t, a} L m)
      (single_flat m).1 (single_flat m).2 (twist.{t, a, w} L m) rfl
      P ((factors m).app P)
  evaluation : ∀ m : ℤ, power.{t, a} L m ⊗ power.{t, a} L (-m) ≅ 𝟙_ (Modules.{t, a} X R)
  evaluation_basis : ∀ (m : ℤ) (U : X.ProEtᵒᵖ)
    (e : ∀ n : ℤ, (power.{t, a} L n).val.obj U),
    SignedLineBasisPowers.{t + 1, t, a} L U e →
    (evaluation m).hom.val.app U
      (LineUnbounded.pureTensor.{t, a} X R (power.{t, a} L m) (power.{t, a} L (-m)) U (e m) (e
        (-m))) = (1 : R.obj.obj U)
  epsilon : ∀ m : ℤ, twist.{t, a, w} L m ⋙ twist.{t, a, w} L (-m) ≅
    𝟭 (DerivedCategory (Modules.{t, a} X R))
  epsilon_computed : ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ),
    (epsilon m).hom.app (𝒬[R].obj P) =
      (twist.{t, a, w} L (-m)).map ((factors m).hom.app P) ≫
      (factors (-m)).hom.app (((tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)).obj P) ≫
      𝒬[R].map
        ((Functor.mapHomologicalComplexCompIso
          (LineUnbounded.cancellation.{t, a} X R (power.{t, a} L m) (power.{t, a} L (-m))
            (evaluation m))
          (.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso (Modules.{t, a} X R) (.up ℤ)).hom.app P)
  flat : ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ), FlatModel P →
    FlatModel (((tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)).obj P)

/-- Normalized comparison before and after localization. Source: Stacks 07A4 and 06YY
(blueprint: def-pur-ordinary-line-scalar-data). -/
structure Comparison {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    {α : R ⟶ S} (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S) (l : LineData L) (k : LineData K)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α (power.{t, a} L m) ≅ power.{t, a} K m) where
  ordinary : ∀ m : ℤ, tensor.{t, a} L m ⋙ p.ordinary ≅ p.ordinary ⋙ tensor.{t, a} K m
  hom_formula : ∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s : S.obj.obj U),
    ((ordinary m).hom.app M).val.app U
      (scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U s
        (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) =
    LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
      (scalar.{t, a, w} p M U s x)
      ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U 1 y))
  inv_formula : ∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s q : S.obj.obj U),
    ((ordinary m).inv.app M).val.app U
      (LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
        (scalar.{t, a, w} p M U s x)
        ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U q y))) =
    scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U (s * q)
      (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)
  derived : ∀ m : ℤ, twist.{t, a, w} L m ⋙ p.derived ≅ p.derived ⋙ twist.{t, a, w} K m
  extended_flat : ∀ P : CochainComplex (Modules.{t, a} X R) ℤ, FlatModel P →
    FlatModel ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  representative : ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ), FlatModel P →
    (derived m).hom.app (𝒬[R].obj P) ≫
      (twist.{t, a, w} K m).map (compute.{t, a, w} p P) ≫
      (k.factors m).hom.app ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
    p.derived.map ((l.factors m).hom.app P) ≫
      compute.{t, a, w} p (((tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)).obj P) ≫
      𝒬[S].map
        ((Functor.mapHomologicalComplexCompIso (ordinary m) (.up ℤ)).hom.app P)
  evaluation : ∀ (m : ℤ) (Y : DerivedCategory (Modules.{t, a} X R)),
    (derived (-m)).hom.app ((twist.{t, a, w} L m).obj Y) ≫
      (twist.{t, a, w} K (-m)).map ((derived m).hom.app Y) ≫
      (k.epsilon m).hom.app (p.derived.obj Y) = p.derived.map ((l.epsilon m).hom.app Y)

set_option backward.isDefEq.respectTransparency.types false

/-- Identity scalar extension with its multiplication normalization before and after Q.
Source: Stacks 03EK and 06YY (blueprint: def-pur-ordinary-line-scalar-data). -/
structure UnitData
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) α)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}) where
  ordinary : (p (𝟙 R)).ordinary ≅ 𝟭 (Modules.{t, a} X R)
  formula : ∀ (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
    (s : R.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U (scalar.{t, a, w} (p (𝟙 R)) M U s x) = s • x
  derived : (p (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (Modules.{t, a} X R))
  computed : ∀ P : CochainComplex (Modules.{t, a} X R) ℤ,
    derived.hom.app (𝒬[R].obj P) = compute.{t, a, w} (p (𝟙 R)) P ≫
      𝒬[R].map
        ((Functor.mapHomologicalComplexCompIso
          (Functor.isoWhiskerLeft (𝟭 _) ordinary ≪≫ Functor.leftUnitor _) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso (Modules.{t, a} X R) (.up ℤ)).hom.app P)

end SheafOfModules.OrdinaryLineScalar
