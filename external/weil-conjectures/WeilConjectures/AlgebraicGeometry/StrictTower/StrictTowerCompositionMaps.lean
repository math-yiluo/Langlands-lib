/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-!
# Canonical composition maps for strict constant-coefficient towers

Source: Stacks Project, Tags 0F7J, 0F7C, 0F7D and 0F7F, and the strict-tower adaptation
in the blueprint (blueprint: def-cbc-strict-tower-composition-maps).

`Compactification.Triangle` names the node's maps as follows: `cf.i = c`, `cf.g = p_Y`,
`cg.i = i`, `cg.g = q`, `cfg.i = a`, `q = b`, and `p = p`.
All maps below are constructed in the derived category of strict towers, before evaluation.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The supplied-compactification functor `R_p J_j`.
Source: Stacks, Tag 0F7J
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionF {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : Derived B X ⥤ Derived B Y := J B c.i ⋙ R B c.g

/-- The actual composition comparison `R_q gamma_Q J_c`, including both compositors.
Source: Stacks, Tag 0F7J
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionD {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF B T.cf ⋙ compositionF B T.cg ⟶ compositionF B T.cfg :=
  Functor.whiskerLeft (J B T.cf.i)
    (Functor.whiskerRight (gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (R B T.cg.g)) ≫
  Functor.whiskerRight
    ((jComp B T.cf.i T.q).hom ≫ (jCongr B T.i_q).hom)
    (R B T.p ⋙ R B T.cg.g) ≫
  Functor.whiskerLeft (J B T.cfg.i)
    ((rComp B T.p T.cg.g).hom ≫ (eqToIso (congrArg (R B) T.p_g)).hom)

/-- The refinement comparison is gamma for the identity-left square, followed by R.
Source: Stacks, Tag 0F7J, choice independence
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionC {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF B d ⟶ compositionF B c :=
  Functor.whiskerRight
    (Functor.whiskerRight (rId B X).inv (J B d.i) ≫
      gamma B c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
    (R B d.g) ≫
  Functor.whiskerLeft (J B c.i)
    ((rComp B r.hom d.g).hom ≫ (eqToIso (congrArg (R B) r.hom_g)).hom)

/-- The specified exchange: first the proper-square mate, then the open comparison.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionE {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    compositionF B c ⋙ G B y ⟶ G B x ⋙ compositionF B c' :=
  Functor.whiskerLeft (J B c.i) (exchange B s c'.g c.g y wp) ≫
  Functor.whiskerRight (beta B x c'.i c.i s wi si).hom (R B c'.g)

/-- A refinement of the supplied towers consists of the three existing compactification
refinements and the two remaining compatibility equations. No cartesian condition is imposed.
Source: Stacks, Tag 0F7J, refinement diagram; compatible-tower dependency
(blueprint: def-cbc-strict-tower-composition-maps). -/
structure CompositionRefinement {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T₁ T₂ : Compactification.Triangle f h) where
  rf : T₁.cf.Refinement T₂.cf
  rh : T₁.cg.Refinement T₂.cg
  rfh : T₁.cfg.Refinement T₂.cfg
  b_comm : T₁.q ≫ rfh.hom = rf.hom ≫ T₂.q
  p_comm : rfh.hom ≫ T₂.p = T₁.p ≫ rh.hom

/-- The horizontal refinement `(C_h F_f1)(F_h2 C_f)`.
Source: Stacks, Tag 0F7J
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionH {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    {T₁ T₂ : Compactification.Triangle f h}
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i]
    (r : CompositionRefinement T₁ T₂) :
    compositionF B T₂.cf ⋙ compositionF B T₂.cg ⟶
      compositionF B T₁.cf ⋙ compositionF B T₁.cg :=
  Functor.whiskerRight (compositionC B r.rf) (compositionF B T₂.cg) ≫
    Functor.whiskerLeft (compositionF B T₁.cf) (compositionC B r.rh)

/-- The cartesian faces of a base change of a supplied compatible tower. All arrows
are supplied projections; this does not choose a compactification or an arbitrary comparison.
Source: Stacks, Tags 0F7J and 0F7F; compatible-tower dependency
(blueprint: def-cbc-strict-tower-composition-maps). -/
structure CompositionBaseChange {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z) where
  d : T'.cf.Z ⟶ T.cf.Z
  t : T'.cg.Z ⟶ T.cg.Z
  s : T'.cfg.Z ⟶ T.cfg.Z
  cf_i : IsPullback x T'.cf.i T.cf.i d
  cf_g : IsPullback d T'.cf.g T.cf.g y
  cg_i : IsPullback y T'.cg.i T.cg.i t
  cg_g : IsPullback t T'.cg.g T.cg.g g
  cfg_i : IsPullback x T'.cfg.i T.cfg.i s
  cfg_g : IsPullback s T'.cfg.g T.cfg.g g
  b : IsPullback d T'.q T.q s
  p : IsPullback s T'.p T.p t

/-- Exchange for f on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionEf {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cf T'.cf x y A.d A.cf_i.w A.cf_g.w A.cf_i

/-- Exchange for h on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionEh {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cg T'.cg y g A.t A.cg_i.w A.cg_g.w A.cg_i

/-- Exchange for hf on the supplied pulled-back tower.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionEhf {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE B T.cfg T'.cfg x g A.s A.cfg_i.w A.cfg_g.w A.cfg_i

/-- The horizontal exchange `(F_h' e_f)(e_h F_f)` with explicit associators.
Source: Stacks, Tag 0F7F
(blueprint: def-cbc-strict-tower-composition-maps). -/
noncomputable def compositionHorizontalE {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    (compositionF B T.cf ⋙ compositionF B T.cg) ⋙ G B g ⟶
      G B x ⋙ (compositionF B T'.cf ⋙ compositionF B T'.cg) :=
  Functor.whiskerLeft (compositionF B T.cf) (compositionEh B A) ≫
  Functor.whiskerRight (compositionEf B A) (compositionF B T'.cg)

end AlgebraicGeometry.ProEtale.StrictTower
