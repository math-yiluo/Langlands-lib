/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.AlgebraicGeometry.RingedProjectionRestrictionData

/-!
# Canonical localization comparisons for the projection mate

All model functors below carry natural representative comparisons. Ordinary operations
are Mathlib's module pullback and pushforward for the specified ring map. Tensor
comparisons are normalized on pure tensors and signed total complexes; derived
adjunctions are normalized by the ordinary counit on K-injectives. No operation or
projection arrow is selected from an unconstrained existence statement.

## Main definitions

* `ProjectionRestriction.Operation`: the canonical module and derived operations.
* `ProjectionRestriction.TensorModel`: derived tensor normalized on resolving pairs.
* `ProjectionRestriction.Local`: canonical slice comparisons and their normalizations.

The assembly theorem `ringedProjectionRestriction` is in
`WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction`.
This module contains its unchanged data
interfaces so the construction lemmas can be imported without a cycle.

## References

* Stacks Project, Cohomology on Sites, Tags 08FI, 0FN5, 07A4 and 0B56
* Modules on Sites, Tag 04J0
* Stacks 05RU
* Stacks 03EK
* Stacks 06YN
* Stacks 06YS
* Stacks 06YU
* Stacks 07A4, Mathlib BifunctorShift
* Stacks 0735
* Stacks 03D7
* Stacks 07A5
* Stacks 03EL
* Stacks 03DJ
* Stacks 07A4 and 07A6
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Ordinary unbounded localization of module complexes, without completion. -/
abbrev Der (R : Sheaf J CommRingCat.{u + 1}) := DerivedCategory (Mod R)

/-- The existing sheaf tensor, in its curried presentation. -/
abbrev tensor (R : Sheaf J CommRingCat.{u + 1}) : Mod R ⥤ Mod R ⥤ Mod R :=
  @curriedTensor (Mod R) _ (SheafOfModules.monoidalCategory R)

/-- The direct-sum total tensor, with Mathlib's sign on its second differential. -/
abbrev total (R : Sheaf J CommRingCat.{u + 1}) :
    CochainComplex (Mod R) ℤ × CochainComplex (Mod R) ℤ ⥤ CochainComplex (Mod R) ℤ :=
  Functor.uncurry.obj ((tensor R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

/-- The resolving full subcategory uses exactly the recorded K-flat and flat-term predicates. -/
def resolving (R : Sheaf J CommRingCat.{u + 1}) : ObjectProperty (CochainComplex (Mod R) ℤ) :=
  fun P ↦ CochainComplex.IsAcyclicTensorKFlat (R := R) P ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := J) (R := R) (P.X n)

/-- A model of derived tensor, identified naturally on the resolving subcategory.
The identification makes the functor the localization of the existing total tensor. -/
structure TensorModel (R : Sheaf J CommRingCat.{u + 1}) where
  preadditive : @MonoidalPreadditive (Mod R) _ _ (SheafOfModules.monoidalCategory R)
  functor : Der R × Der R ⥤ Der R
  representative : ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q ≅
    (((resolving R).ι ⋙ DerivedCategory.Q).prod
      ((resolving R).ι ⋙ DerivedCategory.Q)) ⋙ functor
  /-- Natural transformations are determined on all flat K-flat representatives. -/
  descent : ∀ (F G : Der R × Der R ⥤ Der R), Function.Bijective
    (fun t : F ⟶ G ↦ Functor.whiskerLeft
      (((resolving R).ι ⋙ DerivedCategory.Q).prod
        ((resolving R).ι ⋙ DerivedCategory.Q)) t)

/-- The first normalized tensor shift on flat K-flat representatives. -/
def tensorShiftFirst {R : Sheaf J CommRingCat.{u + 1}} (a : TensorModel R)
    [(Functor.curry.obj a.functor).CommShift₂Int] [(tensor R).Additive]
    [∀ M : Mod R, ((tensor R).obj M).Additive] : Prop :=
  ∀ (P Q : CochainComplex (Mod R) ℤ)
      (hp : resolving R P) (hq : resolving R Q) (n : ℤ),
    ∃ hpn : resolving R (P⟦n⟧),
      a.representative.hom.app (⟨P⟦n⟧, hpn⟩, ⟨Q, hq⟩) ≫
        a.functor.map (CategoryTheory.Prod.mkHom
          ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 _)) ≫
        (((Functor.curry.obj a.functor).flip.obj (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P) ≫
        (shiftFunctor (Der R) n).map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) =
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso P Q (tensor R) n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app ((total R).obj (P, Q))

/-- The second normalized tensor shift, with the total-complex Koszul sign. -/
def tensorShiftSecond {R : Sheaf J CommRingCat.{u + 1}} (a : TensorModel R)
    [(Functor.curry.obj a.functor).CommShift₂Int] [(tensor R).Additive]
    [∀ M : Mod R, ((tensor R).obj M).Additive] : Prop :=
  ∀ (P Q : CochainComplex (Mod R) ℤ)
      (hp : resolving R P) (hq : resolving R Q) (n : ℤ),
    ∃ hqn : resolving R (Q⟦n⟧),
      a.representative.hom.app (⟨P, hp⟩, ⟨Q⟦n⟧, hqn⟩) ≫
        a.functor.map (CategoryTheory.Prod.mkHom (𝟙 _)
          ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curry.obj a.functor).obj (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (shiftFunctor (Der R) n).map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) =
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso P Q (tensor R) n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app ((total R).obj (P, Q))

/-- The two canonical tensor shifts, including the Koszul sign in the second variable.
Their normalization is stated on the existing total-complex shift maps. -/
class TensorShifts {R : Sheaf J CommRingCat.{u + 1}} (a : TensorModel R) where
  [shifts : (Functor.curry.obj a.functor).CommShift₂Int]
  [tensorAdditive : (tensor R).Additive]
  [tensorObjAdditive : ∀ M : Mod R, ((tensor R).obj M).Additive]
  first : tensorShiftFirst a
  second : tensorShiftSecond a

/-- A pure tensor section, using the actual presheaf tensor and sheafification unit. -/
def pure (R : Sheaf J CommRingCat.{u + 1}) (M N : Mod R) (W : Cᵒᵖ)
    (x : M.val.obj W) (y : N.val.obj W) : ((tensor R).obj M |>.obj N).val.obj W :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (M.val ⊗ N.val)).app W (x ⊗ₜ[R.obj.obj W] y))

/-- An exact derived functor is specified on every complex and every cochain map.
This is the localization universal property, not an arbitrary functor of the right type. -/
structure ExactModel {R : Sheaf J CommRingCat.{u + 1}}
    {S : Sheaf K CommRingCat.{u + 1}} (L : Mod R ⥤ Mod S) where
  additive : L.Additive
  functor : Der R ⥤ Der S
  factors : letI := additive
    DerivedCategory.Q ⋙ functor ≅ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

attribute [instance_reducible, instance] TensorShifts.shifts

attribute [instance] Operation.rightAdjoint Operation.pullbackAdditive
  Operation.pushforwardAdditive Operation.pullbackLimits Operation.pullbackColimits

namespace Operation

variable {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
  {S : Sheaf K CommRingCat.{u + 1}} (o : Operation F R S)

/-- The canonical module left adjoint, constructed by module Kan extension and sheafification. -/
abbrev pullback : Mod R ⥤ Mod S :=
  letI := o.continuous
  SheafOfModules.pullback.{u + 1} o.coefficient

/-- Sectionwise direct image with the specified scalar action. -/
abbrev pushforward : Mod S ⥤ Mod R :=
  letI := o.continuous
  SheafOfModules.pushforward.{u + 1} o.coefficient

/-- Exact termwise pullback descended through localization. -/
def left : Der R ⥤ Der S := o.pullback.mapDerivedCategory

/-- The ordinary uncompleted K-injective right derived functor. -/
def right : Der S ⥤ Der R :=
  letI := o.kInjectives
  o.pushforward.rightDerivedFunctor

/-- The standard exact-functor shift on the constructed derived pullback. -/
instance leftShift : o.left.CommShift ℤ :=
  inferInstanceAs (o.pullback.mapDerivedCategory.CommShift ℤ)

/-- Its actual termwise pullback comparison. -/
abbrev leftModel : ExactModel o.pullback where
  additive := o.pullbackAdditive
  functor := o.left
  factors := o.pullback.mapDerivedCategoryFactors

/-- The fixed exact-pullback shift on the constructed representative model. -/
instance leftModelShift : o.leftModel.functor.CommShift ℤ :=
  inferInstanceAs (o.left.CommShift ℤ)

/-- The standard K-injective shift structure, without a further choice. -/
instance rightShift : o.right.CommShift ℤ :=
  letI := o.kInjectives
  inferInstanceAs (o.pushforward.rightDerivedFunctor.CommShift ℤ)

/-- The existing right-derived unit, expressed on complexes. -/
def rightComparison (I : CochainComplex (Mod S) ℤ) :
    DerivedCategory.Q.obj ((o.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      o.right.obj (DerivedCategory.Q.obj I) :=
  letI := o.kInjectives
  derivedPushforwardComplexComparison o.pushforward o.right o.pushforward.rightDerivedFunctorUnit I

/-- The constructed module adjunction, with its canonical unit and counit. -/
def moduleAdjunction : o.pullback ⊣ o.pushforward :=
  letI := o.continuous
  SheafOfModules.pullbackPushforwardAdjunction o.coefficient

/-- The canonical derived adjunction is induced from the constructed module adjunction. -/
def derivedAdjunction : o.left ⊣ o.right :=
  letI := o.kInjectives
  o.moduleAdjunction.mapDerivedCategoryRightDerivedAdjunction

/-- The counit of the actual derived adjunction, exposed with its fixed functor type. -/
def derivedCounit : o.right ⋙ o.left ⟶ 𝟭 (Der S) := o.derivedAdjunction.counit

/-- Proofs identifying the constructed derived counit on K-injective representatives. -/
structure DerivedAdjunction : Prop where
  counit_shift : NatTrans.CommShift o.derivedCounit ℤ
  counit : ∀ (I : CochainComplex (Mod S) ℤ), I.IsKInjective →
    o.left.map (o.rightComparison I) ≫ o.derivedCounit.app (DerivedCategory.Q.obj I) =
      o.leftModel.factors.hom.app ((o.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((o.moduleAdjunction.mapHomologicalComplex
            (.up ℤ)).counit.app I)

end Operation

namespace Operation
/-- Canonical pullback/tensor comparison, fixed on pure sections. -/
structure OrdinaryTensor {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    {F : C ⥤ D} (o : Operation F R S) where
  iso : ∀ M N : Mod R, o.pullback.obj (((tensor R).obj M).obj N) ≅
    ((tensor S).obj (o.pullback.obj M)).obj (o.pullback.obj N)
  pure_unit : ∀ (M N : Mod R) (W : Cᵒᵖ) (x : M.val.obj W) (y : N.val.obj W),
    ((o.pushforward.map (iso M N).hom).val.app W)
      (((o.moduleAdjunction.unit.app (((tensor R).obj M).obj N)).val.app W)
        (pure R M N W x y)) =
      pure S (o.pullback.obj M) (o.pullback.obj N) (F.op.obj W)
        (((o.moduleAdjunction.unit.app M).val.app W) x)
        (((o.moduleAdjunction.unit.app N).val.app W) y)

end Operation

/-- Canonical signed total-tensor map on representatives. -/
noncomputable def totalComponent {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (a : TensorModel R) (b : TensorModel S) (L : Mod R ⥤ Mod S) [L.Additive]
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (P Q : CochainComplex (Mod R) ℤ) (n : ℤ) :
    ((total S).obj ((L.mapHomologicalComplex (.up ℤ)).obj P,
      (L.mapHomologicalComplex (.up ℤ)).obj Q)).X n ⟶ L.obj (((total R).obj (P, Q)).X n) :=
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  letI := a.preadditive
  letI := b.preadditive
  tensorPullbackTotalComponent L mu P Q n

/-- The signed degree maps assemble to the canonical chain comparison. -/
def totalMap {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (a : TensorModel R) (b : TensorModel S) (L : Mod R ⥤ Mod S) [L.Additive]
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (comm : ∀ (P Q : CochainComplex (Mod R) ℤ) (n m : ℤ),
      totalComponent a b L mu P Q n ≫ L.map (((total R).obj (P, Q)).d n m) =
        ((total S).obj ((L.mapHomologicalComplex (.up ℤ)).obj P,
          (L.mapHomologicalComplex (.up ℤ)).obj Q)).d n m ≫
            totalComponent a b L mu P Q m)
    (P Q : CochainComplex (Mod R) ℤ) :
    (total S).obj ((L.mapHomologicalComplex (.up ℤ)).obj P,
      (L.mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj ((total R).obj (P, Q)) where
  f := totalComponent a b L mu P Q
  comm' := fun n m _ ↦ comm P Q n m

/-- A derived comparison agrees with the signed total map on every resolving pair. -/
structure TensorComparisonCore {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (L : Mod R ⥤ Mod S) [L.Additive] (d : ExactModel L)
    (a : TensorModel R) (b : TensorModel S)
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N)) where
  preserves : ∀ P, resolving R P → resolving S ((L.mapHomologicalComplex (.up ℤ)).obj P)
  comparison : a.functor ⋙ d.functor ≅ (d.functor.prod d.functor) ⋙ b.functor
  comm : ∀ (P Q : CochainComplex (Mod R) ℤ) (n m : ℤ),
    totalComponent a b L mu P Q n ≫ L.map (((total R).obj (P, Q)).d n m) =
      ((total S).obj ((L.mapHomologicalComplex (.up ℤ)).obj P,
        (L.mapHomologicalComplex (.up ℤ)).obj Q)).d n m ≫ totalComponent a b L mu P Q m

/-- Equality with the signed total comparison on every flat K-flat representative. -/
def TensorComparisonCore.Representative {R : Sheaf J CommRingCat.{u + 1}}
    {S : Sheaf K CommRingCat.{u + 1}}
    {L : Mod R ⥤ Mod S} [L.Additive] {d : ExactModel L}
    {a : TensorModel R} {b : TensorModel S}
    {mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N)}
    (t : TensorComparisonCore L d a b mu) : Prop :=
  ∀ (P Q : CochainComplex (Mod R) ℤ)
      (hp : resolving R P) (hq : resolving R Q),
    d.functor.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      t.comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.functor.map (CategoryTheory.Prod.mkHom (d.factors.hom.app P) (d.factors.hom.app Q)) ≫
      b.representative.inv.app
        (⟨(L.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(L.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩) ≫
      DerivedCategory.Q.map (totalMap a b L mu t.comm P Q) =
      d.factors.hom.app ((total R).obj (P, Q))

/-- A canonical derived tensor comparison, determined on all resolving pairs. -/
structure TensorComparison {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (L : Mod R ⥤ Mod S) [L.Additive] (d : ExactModel L)
    (a : TensorModel R) (b : TensorModel S)
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N)) extends TensorComparisonCore L d a b mu where
  representative : toTensorComparisonCore.Representative

/-- The two tensor-comparison squares for the normalized integer shifts. -/
structure TensorComparisonShifts {R : Sheaf J CommRingCat.{u + 1}}
    {S : Sheaf K CommRingCat.{u + 1}} {L : Mod R ⥤ Mod S} [L.Additive]
    {d : ExactModel L} {a : TensorModel R} {b : TensorModel S}
    {mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N)}
    (t : TensorComparison L d a b mu)
    [sa : TensorShifts a] [sb : TensorShifts b] [sd : d.functor.CommShift ℤ] : Prop where
  first : ∀ (M N : Der R) (n : ℤ),
    t.comparison.hom.app (M⟦n⟧, N) ≫
      b.functor.map (CategoryTheory.Prod.mkHom
        ((d.functor.commShiftIso n).hom.app M) (𝟙 _)) ≫
      (((Functor.curry.obj b.functor).flip.obj (d.functor.obj N)).commShiftIso n).hom.app
        (d.functor.obj M) =
    d.functor.map ((((Functor.curry.obj a.functor).flip.obj N).commShiftIso n).hom.app M) ≫
      (d.functor.commShiftIso n).hom.app (a.functor.obj (M, N)) ≫
      (shiftFunctor (Der S) n).map (t.comparison.hom.app (M, N))
  second : ∀ (M N : Der R) (n : ℤ),
    t.comparison.hom.app (M, N⟦n⟧) ≫
      b.functor.map (CategoryTheory.Prod.mkHom (𝟙 _)
        ((d.functor.commShiftIso n).hom.app N)) ≫
      (((Functor.curry.obj b.functor).obj (d.functor.obj M)).commShiftIso n).hom.app
        (d.functor.obj N) =
    d.functor.map ((((Functor.curry.obj a.functor).obj M).commShiftIso n).hom.app N) ≫
      (d.functor.commShiftIso n).hom.app (a.functor.obj (M, N)) ≫
      (shiftFunctor (Der S) n).map (t.comparison.hom.app (M, N))

/-- Exact localization restriction, using Mathlib's `overFunctor`. -/
structure Restriction (R : Sheaf J CommRingCat.{u + 1}) (V : C) where
  [limits : PreservesFiniteLimits (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V)]
  [colimits : PreservesFiniteColimits (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V)]
  [additive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V).Additive]
  ordinaryTensor : ∀ M N : Mod R,
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V).obj
        (((tensor R).obj M).obj N) ≅
      ((tensor (R.over V)).obj (M.over V)).obj (N.over V)
  pure_sections : ∀ (M N : Mod R) (W : (Over V)ᵒᵖ)
      (x : M.val.obj (op W.unop.left)) (y : N.val.obj (op W.unop.left)),
    ((ordinaryTensor M N).hom.val.app W) (pure R M N (op W.unop.left) x y) =
      pure (R.over V) (M.over V) (N.over V) W x y

set_option backward.isDefEq.respectTransparency false in
/-- Actual exact descent of restriction, with its fixed localization comparison. -/
abbrev Restriction.model {R : Sheaf J CommRingCat.{u + 1}} {V : C} (r : Restriction R V)
    : ExactModel (R := R) (S := R.over V)
      (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V) :=
  letI := r.additive
  letI := r.limits
  letI := r.colimits
  letI := SheafOfModules.monoidalCategory R
  { additive := r.additive
    functor := (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V).mapDerivedCategory
    factors := Functor.mapDerivedCategoryFactors _
    }

set_option backward.isDefEq.respectTransparency false in
/-- The fixed termwise-restriction shift on its exact derived model. -/
instance Restriction.modelShift {R : Sheaf J CommRingCat.{u + 1}} {V : C}
    (r : Restriction R V) : r.model.functor.CommShift ℤ :=
  letI := r.additive
  letI := r.limits
  letI := r.colimits
  inferInstanceAs (Functor.CommShift
    (Functor.mapDerivedCategory (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) V)) ℤ)

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme.ProjectionRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)

/-- Canonically normalized operations and tensor on the original sites. -/
structure Global where
  operation : Operation (proEtaleBaseChange f) R_Y R_X
  coefficient_eq : operation.coefficient =
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R_Y R_X c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  recordedDirectImage : operation.pushforward = proEtaleRingModuleDirectImage f R_Y R_X c
  adjunction : operation.DerivedAdjunction
  tensorY : TensorModel R_Y
  tensorX : TensorModel R_X
  tensorYShifts : TensorShifts tensorY
  tensorXShifts : TensorShifts tensorX
  ordinaryTensor : operation.OrdinaryTensor
  tensorComparison : TensorComparison operation.pullback operation.leftModel tensorY tensorX
    ordinaryTensor.iso
  tensorComparison_shifts : TensorComparisonShifts tensorComparison
    (sa := tensorYShifts) (sb := tensorXShifts) (sd := inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- The actual slice restrictions and their normalized derived comparisons. -/
structure Local (g : Global f R_Y R_X c) (V : Y.ProEt) where
  [restrictionYAdditive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V).Additive]
  [restrictionXAdditive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V)).Additive]
  restrictionY : Restriction R_Y V
  restrictionX : Restriction R_X ((proEtaleBaseChange f).obj V)
  operation : Operation (Over.post (X := V) (proEtaleBaseChange f)) (R_Y.over V)
    (R_X.over ((proEtaleBaseChange f).obj V))
  coefficient_sections : ∀ T : Over V, operation.coefficient.hom.app (op T) =
    g.operation.coefficient.hom.app (op T.left)
  adjunction : operation.DerivedAdjunction
  tensorY : TensorModel (R_Y.over V)
  tensorX : TensorModel (R_X.over ((proEtaleBaseChange f).obj V))
  tensorYShifts : TensorShifts tensorY
  tensorXShifts : TensorShifts tensorX
  ordinaryTensor : operation.OrdinaryTensor
  tensorComparison : TensorComparison operation.pullback operation.leftModel tensorY tensorX
    ordinaryTensor.iso
  tensorComparison_shifts : TensorComparisonShifts tensorComparison
    (sa := tensorYShifts) (sb := tensorXShifts) (sd := inferInstance)
  restrictionTensorY : TensorComparison
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V)
    restrictionY.model g.tensorY tensorY restrictionY.ordinaryTensor
  restrictionTensorX : TensorComparison
    (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
        ((proEtaleBaseChange f).obj V))
    restrictionX.model g.tensorX tensorX restrictionX.ordinaryTensor
  restrictionTensorY_shifts :
    TensorComparisonShifts restrictionTensorY
      (sa := g.tensorYShifts) (sb := tensorYShifts) (sd := inferInstance)
  restrictionTensorX_shifts :
    TensorComparisonShifts restrictionTensorX
      (sa := g.tensorXShifts) (sb := tensorXShifts) (sd := inferInstance)
  [leftRouteZero : (g.operation.pushforward ⋙
    SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V).PreservesZeroMorphisms]
  [rightRouteZero : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V) ⋙ operation.pushforward).PreservesZeroMorphisms]
  ordinaryDirectImage : g.operation.pushforward ⋙
      SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V ≅
    SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
        ((proEtaleBaseChange f).obj V) ⋙ operation.pushforward
  ordinaryDirectImage_sections : ∀ (M : Mod R_X) (T : (Over V)ᵒᵖ)
      (x : M.val.obj (op ((proEtaleBaseChange f).obj T.unop.left))),
    ((ordinaryDirectImage.hom.app M).val.app T) x = x
  restrictsKInjective : ∀ I : CochainComplex (Mod R_X) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective ((SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V)).mapHomologicalComplex (.up ℤ) |>.obj I)
  directImage : g.operation.right ⋙ (restrictionY.model).functor ≅
    (restrictionX.model).functor ⋙ operation.right
  directImage_shift : NatTrans.CommShift directImage.hom ℤ
  directImage_representative : ∀ (I : CochainComplex (Mod R_X) ℤ), I.IsKInjective →
    restrictionY.model.functor.map (g.operation.rightComparison I) ≫
      directImage.hom.app (DerivedCategory.Q.obj I) =
    restrictionY.model.factors.hom.app
        ((g.operation.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinaryDirectImage (.up ℤ)).hom.app I) ≫
      operation.rightComparison ((SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((proEtaleBaseChange f).obj V)).mapHomologicalComplex (.up ℤ) |>.obj I) ≫
      operation.right.map (restrictionX.model.factors.inv.app I)
  pullback : g.operation.left ⋙ (restrictionX.model).functor ≅
    (restrictionY.model).functor ⋙ operation.left
  pullback_shift : NatTrans.CommShift pullback.hom ℤ
  mate_counit : ∀ E : Der R_X,
    operation.left.map (directImage.hom.app E) ≫
      operation.derivedCounit.app (restrictionX.model.functor.obj E) =
    pullback.inv.app (g.operation.right.obj E) ≫
      restrictionX.model.functor.map (g.operation.derivedCounit.app E)

set_option backward.isDefEq.respectTransparency false in
/-- The source identification is tensor restriction followed by direct-image restriction. -/
def Local.sourceIso {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt} (l : Local f R_Y R_X c g V)
    (E : Der R_X) (P : Der R_Y) :
    l.restrictionY.model.functor.obj
      (g.tensorY.functor.obj (g.operation.right.obj E, P)) ≅
    l.tensorY.functor.obj
      (l.operation.right.obj (l.restrictionX.model.functor.obj E),
        l.restrictionY.model.functor.obj P) :=
  letI := l.restrictionYAdditive
  letI := l.restrictionXAdditive
  l.restrictionTensorY.comparison.app (g.operation.right.obj E, P) ≪≫
    l.tensorY.functor.mapIso (CategoryTheory.Iso.prod (l.directImage.app E) (Iso.refl _))

set_option backward.isDefEq.respectTransparency false in
/-- The target identification is direct-image restriction, tensor restriction and pullback. -/
def Local.targetIso {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt} (l : Local f R_Y R_X c g V)
    (E : Der R_X) (P : Der R_Y) :
    l.restrictionY.model.functor.obj
      (g.operation.right.obj (g.tensorX.functor.obj (E, g.operation.left.obj P))) ≅
    l.operation.right.obj (l.tensorX.functor.obj
      (l.restrictionX.model.functor.obj E,
        l.operation.left.obj (l.restrictionY.model.functor.obj P))) :=
  letI := l.restrictionYAdditive
  letI := l.restrictionXAdditive
  l.directImage.app (g.tensorX.functor.obj (E, g.operation.left.obj P)) ≪≫
    l.operation.right.mapIso
      (l.restrictionTensorX.comparison.app (E, g.operation.left.obj P) ≪≫
        l.tensorX.functor.mapIso
          (CategoryTheory.Iso.prod (Iso.refl _) (l.pullback.app P)))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the actual adjoint-of-counit projection mate, under the constructed isos. -/
def Local.ProjectionCompatible {f : X ⟶ Y} {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt} (l : Local f R_Y R_X c g V) : Prop :=
  letI := l.restrictionYAdditive
  letI := l.restrictionXAdditive
  ∀ (E : Der R_X) (P : Der R_Y),
    l.restrictionY.model.functor.map
      (derivedProjectionFormulaMate g.operation.left g.operation.right g.operation.derivedAdjunction
        g.tensorY.functor g.tensorX.functor g.tensorComparison.comparison E P) ≫
      (l.targetIso E P).hom = (l.sourceIso E P).hom ≫
      derivedProjectionFormulaMate l.operation.left l.operation.right l.operation.derivedAdjunction
        l.tensorY.functor l.tensorX.functor l.tensorComparison.comparison
          (l.restrictionX.model.functor.obj E) (l.restrictionY.model.functor.obj P)

end AlgebraicGeometry.Scheme.ProjectionRestriction
