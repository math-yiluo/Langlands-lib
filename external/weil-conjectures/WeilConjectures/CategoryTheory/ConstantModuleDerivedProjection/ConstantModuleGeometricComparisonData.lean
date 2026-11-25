/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.DerivedProjectionComparisonSquares
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarGeometricAdjunctions
public import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Constant modules, derived adjunctions and projection maps

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6;
Modules on Sites, Tag 03EL
(blueprint: def-sfb-constant-module-geometric-comparison-data).

The ordinary data below specify geometric inverse image and scalar extension on generalized
sections. Derived comparisons retain their localization squares, Hom bijections and counits.
The site object and morphism universes remain independent, including for small etale sites.
The ringed datum uses the landed independent-universe interface
`RingedToposMorphismOfUniverses` (blueprint: def-pur-ringed-topos-morphism-of-universes).
The two fixed-scalar OfUniverses helpers extend the imported constant-scalar interface
here; its landed declarations and DAG binding remain intact.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u v w a b c e ha hb hc he wa wb

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open SheafOfModules
open SheafOfModules.CanonicalTensorPullbackOfUniverses

namespace CategoryTheory

/-- The induced geometric adjunction on fixed-ring module sheaves. The direct-image
comparison and generalized-element equation specify the transported addition and every
scalar endomorphism. The inverse image is its specified left adjoint; hence uniqueness
of left adjoints identifies it with the induced geometric inverse image.
Source: Stacks Project, Sites, Tag 00YV (6), proof by scalar endomorphisms
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
structure FixedScalarGeometricAdjunctionOfUniverses
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type (max u v)) [CommRing B]
    (L : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v)))
    (V : Sheaf K (Type (max u v)) ⥤ Sheaf J (Type (max u v)))
    (a : L ⊣ V) (hL : PreservesFiniteLimits L) where
  /-- Induced inverse image of fixed-scalar module sheaves. -/
  inverse : Sheaf J (ModuleCat.{max u v} B) ⥤ Sheaf K (ModuleCat.{max u v} B)
  /-- Induced direct image of fixed-scalar module sheaves. -/
  direct : Sheaf K (ModuleCat.{max u v} B) ⥤ Sheaf J (ModuleCat.{max u v} B)
  /-- The specified module adjunction. -/
  adj : inverse ⊣ direct
  /-- Identification with the given direct image on underlying sheaves. -/
  underlying : direct ⋙ sheafCompose J (forget (ModuleCat.{max u v} B)) ≅
    sheafCompose K (forget (ModuleCat.{max u v} B)) ⋙ V
  /-- The direct-image action and addition under the given sheaf adjunction.
  This also determines zero and negation by the abelian group laws. -/
  linear : ∀ (N : Sheaf K (ModuleCat.{max u v} B)) (T : Sheaf J (Type (max u v))) (b : B)
    (x y z : T ⟶ (sheafCompose J (forget (ModuleCat.{max u v} B))).obj (direct.obj N)),
    (∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((direct.obj N).obj.obj U) inferInstance
        (@SMul.smul B ((direct.obj N).obj.obj U) inferInstance b (x.hom.app U t))
        (y.hom.app U t)) →
    ∀ (U : Dᵒᵖ) (t : (L.obj T).obj.obj U),
      ((a.homEquiv T _).symm (z ≫ underlying.hom.app N)).hom.app U t =
        @Add.add (N.obj.obj U) inferInstance
          (@SMul.smul B (N.obj.obj U) inferInstance b
            (((a.homEquiv T _).symm (x ≫ underlying.hom.app N)).hom.app U t))
          (((a.homEquiv T _).symm (y ≫ underlying.hom.app N)).hom.app U t)

private def constantScalar
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (b : B) :
    (constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1} ⟶
      (sheafCompose J (forget RingCat.{max u v})).obj
        ((constantSheaf J RingCat.{max u v}).obj (RingCat.of B)) :=
  (constantSheaf J (Type (max u v))).map (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget RingCat.{max u v})).inv.app (RingCat.of B)

private theorem constantScalar_apply
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (b : B) (U : Cᵒᵖ)
    (t : ((constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1}).obj.obj U) :
    (constantScalar J B b).hom.app U t =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U b := by
  let P := (Functor.const Cᵒᵖ).obj PUnit.{max u v + 1}
  let : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective _).mp
    (inferInstance : IsIso ((toSheafify J P).app U))).2 t
  subst t
  have hn := congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
      (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b))))
  change _ = ((constantSheaf J (Type (max u v))).map
    (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b))).hom.app U
      ((toSheafify J P).app U x) at hn
  change ((constantCommuteCompose J (forget RingCat.{max u v})).inv.app
    (RingCat.of B)).hom.app U _ = _
  have hn' : ((constantSheaf J (Type (max u v))).map
      (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ b))).hom.app U
        ((toSheafify J P).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b := hn.symm
  apply Eq.trans (congrArg
    (fun z ↦ ((constantCommuteCompose J (forget RingCat.{max u v})).inv.app
      (RingCat.of B)).hom.app U z) hn')
  have hf := congrArg (fun f ↦ f.app U b)
    (sheafComposeIso_hom_fac J (forget RingCat.{max u v})
      ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
  have hconst := toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget RingCat.{max u v})).hom.app (RingCat.of B))
  have hp := congrArg (fun f ↦ f.app U b) hconst
  dsimp at hp
  change ((sheafifyComposeIso J (forget RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (RingCat.of B))).hom.app U)
      ((((presheafToSheaf J (Type (max u v))).map
        ((Functor.compConstIso Cᵒᵖ (forget RingCat.{max u v})).hom.app
          (RingCat.of B))).hom.app U)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b)) = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget RingCat.{max u v})
    ((Functor.const Cᵒᵖ).obj (RingCat.of B))).hom.app U) z) hp.symm).trans hf

private def toConstantUnit
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (T : Sheaf J (Type (max u v))) :
    T ⟶ (constantSheaf J (Type (max u v))).obj PUnit.{max u v + 1} where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun _ ↦
      (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{max u v + 1})).app U PUnit.unit)
      naturality := by
        intro U V f
        ext t
        exact congrArg (fun g ↦ g PUnit.unit)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{max u v + 1})).naturality f) }

private def scalarAdd
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : Type (max u v)} [CommRing B] (N : Sheaf J (ModuleCat.{max u v} B))
    (T : Sheaf J (Type (max u v))) (b : B)
    (x y : T ⟶ (sheafCompose J (forget (ModuleCat.{max u v} B))).obj N) :
    T ⟶ (sheafCompose J (forget (ModuleCat.{max u v} B))).obj N where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun t ↦
        @Add.add (N.obj.obj U) inferInstance
          (@SMul.smul B (N.obj.obj U) inferInstance b (x.hom.app U t)) (y.hom.app U t))
      naturality := by
        intro U V f
        ext t
        change @Add.add (N.obj.obj V) inferInstance
          (@SMul.smul B (N.obj.obj V) inferInstance b (x.hom.app V (T.obj.map f t)))
          (y.hom.app V (T.obj.map f t)) = N.obj.map f
            (@Add.add (N.obj.obj U) inferInstance
              (@SMul.smul B (N.obj.obj U) inferInstance b (x.hom.app U t)) (y.hom.app U t))
        erw [map_add, map_smul]
        congr 1
        · exact congrArg (fun g ↦ @SMul.smul B (N.obj.obj V) inferInstance b (g t))
            (x.hom.naturality f)
        · exact congrArg (fun g ↦ g t) (y.hom.naturality f) }

end CategoryTheory

namespace CategoryTheory.ConstantModuleDerivedProjection

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type (max u v)) [CommRing A]
set_option maxHeartbeats 70000 in
-- Bound the dependent ordinary-data elaboration.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The geometric morphism and its two ordinary module adjunctions.
The Hom equations normalize the adjunctions on the underlying sheaves; the fixed-ring
action is the induced one, as specified by the scalar equation for its direct image.
Source: Stacks Tags 03EL, 07A4 and 07A6
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
structure GeometricData where
  inverse : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v))
  direct : Sheaf K (Type (max u v)) ⥤ Sheaf J (Type (max u v))
  geometric : inverse ⊣ direct
  [leftExact : PreservesFiniteLimits inverse]
  inverseRing : Sheaf K CommRingCat.{max u v}
  algebraic : AlgebraicInverseImage inverse (ring J A) inverseRing
  scalarIso : inverseRing ≅ ring K A
  terminalIso : inverse.obj ((constantSheaf J (Type (max u v))).obj
    PUnit.{max u v + 1}) ≅ (constantSheaf K (Type (max u v))).obj PUnit.{max u v + 1}
  constants : ∀ a : A,
    inverse.map ((constantSheaf J (Type (max u v))).map
      (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ a)) ≫
        (constantCommuteCompose J (CategoryTheory.forget CommRingCat.{max u v})).inv.app
          (CommRingCat.of A)) ≫ algebraic.ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{max u v})).map scalarIso.hom =
      terminalIso.hom ≫ (constantSheaf K (Type (max u v))).map
        (TypeCat.ofHom (fun _ : PUnit.{max u v + 1} ↦ a)) ≫
        (constantCommuteCompose K (CategoryTheory.forget CommRingCat.{max u v})).inv.app
          (CommRingCat.of A)
  pullR : Modules J A ⥤ Modules K A
  object_eq : ∀ M : Modules J A,
    pullR.obj M = changeOfRings scalarIso.hom (algebraic.modules.obj M)
  map_eq : ∀ {M N : Modules J A} (f : M ⟶ N),
    pullR.map f = eqToHom (object_eq M) ≫
      changeOfRingsHom scalarIso.hom (algebraic.modules.obj M) (algebraic.modules.map f) ≫
      eqToHom (object_eq N).symm
  [pullR_additive : pullR.Additive]
  ringTensor : CanonicalRingedTensorComparison
    (ring J A) (ring K A) inverseRing inverse algebraic scalarIso.hom pullR object_eq
  pushR : Modules K A ⥤ Modules J A
  [pushR_additive : pushR.Additive]
  ringAdj : pullR ⊣ pushR
  pushUnderlying : pushR ⋙ toSheaf _ ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v}) ≅
      (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v})) ⋙ direct
  ringHom : ∀ (M : Modules J A) (N : Modules K A) (f : pullR.obj M ⟶ N),
    (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v})).map
        (ringAdj.homEquiv M N f) ≫ pushUnderlying.hom.app N =
      geometric.homEquiv _ _ (algebraic.moduleUnderlying.inv.app M ≫ ringTensor.q M ≫
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v})).map f)
  fixed : FixedScalarGeometricAdjunctionOfUniverses J K A inverse direct geometric leftExact
  ringed : @RingedToposMorphismOfUniverses D C _ _
    (essentiallySmallSelf.{v} D) (essentiallySmallSelf.{v} C) K J
    ((sheafCompose K (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring K A))
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J A))
  ringed_inverse : ringed.inverse = inverse
  ringed_direct : ringed.direct = direct
  ringed_adj : HEq ringed.adj geometric
  ringed_map : HEq ringed.ringMap
    (algebraic.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{max u v})).map scalarIso.hom)
  ringed_modules : ringed.modules = pushR
  ringed_underlying : HEq ringed.underlying pushUnderlying

attribute [instance] GeometricData.leftExact GeometricData.pullR_additive
  GeometricData.pushR_additive

/-- Projection of the recorded fixed-scalar geometric adjunction.
Source: Stacks Tag 00YV
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
abbrev GeometricData.pullA (d : GeometricData J K A) := d.fixed.inverse

/-- Projection of the recorded fixed-scalar geometric adjunction.
Source: Stacks Tag 00YV
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
abbrev GeometricData.pushA (d : GeometricData J K A) := d.fixed.direct

/-- Projection of the recorded fixed-scalar geometric adjunction.
Source: Stacks Tag 00YV
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
abbrev GeometricData.fixedAdj (d : GeometricData J K A) := d.fixed.adj

/-- Projection of the recorded fixed-scalar geometric adjunction.
Source: Stacks Tag 00YV
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
abbrev GeometricData.fixedPushUnderlying (d : GeometricData J K A) := d.fixed.underlying

variable {J K A}
/-- The exactness consequences needed to form the localized termwise pullbacks.
They are conclusions of the main theorem, rather than extra exactness hypotheses.
Source: Stacks Tags 03EL, 07A4 and 07A6
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
class ExactData (d : GeometricData J K A) where
  [pullA_additive : d.pullA.Additive]
  [pushA_additive : d.pushA.Additive]
  [pullA_limits : PreservesFiniteLimits d.pullA]
  [pullA_colimits : PreservesFiniteColimits d.pullA]
  [pullR_limits : PreservesFiniteLimits d.pullR]
  [pullR_colimits : PreservesFiniteColimits d.pullR]
  [pullA_allColimits : PreservesColimitsOfSize.{0, 0} d.pullA]
  [pullR_allColimits : PreservesColimitsOfSize.{0, 0} d.pullR]

attribute [instance] ExactData.pullA_additive ExactData.pushA_additive
  ExactData.pullA_limits ExactData.pullA_colimits ExactData.pullR_limits ExactData.pullR_colimits
  ExactData.pullA_allColimits
  ExactData.pullR_allColimits

variable [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (Fixed J A)] [HasDerivedCategory.{w} (Fixed K A)]
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Cache the recorded K-flat monoidal structure on the ringed derived category.
Source: Stacks Tag 07A4
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
instance ringDerivedMonoidal : MonoidalCategory (DerivedCategory (Modules J A)) :=
  inferInstance

/-- Cache the recorded K-flat monoidal structure on the fixed-scalar derived category.
Source: Stacks Tag 07A4
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
instance fixedDerivedMonoidal : MonoidalCategory (DerivedCategory (Fixed J A)) :=
  inferInstance

/-- The normalized ordinary comparison, including its full Hom equation.
Source: Stacks Tags 03EL, 07A4 and 07A6
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
structure OrdinaryIdentification (d : GeometricData J K A) where
  left : d.pullR ⋙ restriction K A ≅ restriction J A ⋙ d.pullA
  right : d.pushR ⋙ restriction J A ≅ restriction K A ⋙ d.pushA
  underlying : ∀ N : Modules K A,
    (sheafCompose J (CategoryTheory.forget (ModuleCat.{max u v} A))).map
        (right.hom.app N) ≫ d.fixedPushUnderlying.hom.app ((restriction K A).obj N) =
      d.pushUnderlying.hom.app N
  hom : ∀ (M : Modules J A) (N : Modules K A) (f : d.pullR.obj M ⟶ N),
    d.fixedAdj.homEquiv _ _ (left.inv.app M ≫ (restriction K A).map f) =
      (restriction J A).map (d.ringAdj.homEquiv M N f) ≫ right.hom.app N

/-- The canonical ordinary tensor comparison on the fixed-scalar side.
Its underlying inverse image, Hom equation and generalized pure-tensor equation fix
the comparison, including its normalization on sites with no points.
Source: Stacks Tags 03EL, 07A4 and 07A6
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
structure FixedTensorData (d : GeometricData J K A) where
  underlying : d.pullA ⋙ sheafCompose K (CategoryTheory.forget (ModuleCat.{max u v} A)) ≅
    sheafCompose J (CategoryTheory.forget (ModuleCat.{max u v} A)) ⋙ d.inverse
  hom : ∀ (M : Fixed J A) (N : Fixed K A) (f : d.pullA.obj M ⟶ N),
    (sheafCompose J (CategoryTheory.forget (ModuleCat.{max u v} A))).map
        (d.fixedAdj.homEquiv M N f) ≫ d.fixedPushUnderlying.hom.app N =
      d.geometric.homEquiv _ _ (underlying.inv.app M ≫
        (sheafCompose K (CategoryTheory.forget (ModuleCat.{max u v} A))).map f)
  monoidal : d.pullA.Monoidal
  pure : ∀ (M N : Fixed J A) (Z : Sheaf J (Type (max u v)))
    (x : Z ⟶ (sheafCompose J (CategoryTheory.forget (ModuleCat.{max u v} A))).obj M)
    (y : Z ⟶ (sheafCompose J (CategoryTheory.forget (ModuleCat.{max u v} A))).obj N)
    (z : Z ⟶ (sheafCompose J (CategoryTheory.forget (ModuleCat.{max u v} A))).obj (M ⊗ N)),
    (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
      fixedPure J A M N U (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Dᵒᵖ) (t : (d.inverse.obj Z).obj.obj U),
      (d.inverse.map z ≫ underlying.inv.app (M ⊗ N) ≫
        (sheafCompose K (CategoryTheory.forget (ModuleCat.{max u v} A))).map
          (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullA monoidal.toOplaxMonoidal M N)).hom.app
            U t = fixedPure K A (d.pullA.obj M) (d.pullA.obj N) U
        ((d.inverse.map x ≫ underlying.inv.app M).hom.app U t)
        ((d.inverse.map y ≫ underlying.inv.app N).hom.app U t)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 60000 in
-- Elaborate the dependent tensor and projection comparison squares.
/-- The tensor part of the scalar comparison, on representatives and all derived inputs.
Source: Stacks Tag 07A4
(blueprint: def-sfb-constant-module-geometric-comparison-data). -/
def DerivedTensorIdentification (d : GeometricData J K A) (x : ExactData d)
    (t : FixedTensorData d) :=
  { choices : d.pullR.mapDerivedCategory.Monoidal × d.pullR.Monoidal ×
      d.pullA.mapDerivedCategory.Monoidal //
    (∀ M N : Modules J A,
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullR
        choices.2.1.toOplaxMonoidal M N = (d.ringTensor.mu M N).hom) ∧
    TensorNormalization (Modules J A) (Modules K A) d.pullR choices.2.1 choices.1 ∧
    TensorNormalization (Fixed J A) (Fixed K A) d.pullA t.monoidal choices.2.2 }

end CategoryTheory.ConstantModuleDerivedProjection
