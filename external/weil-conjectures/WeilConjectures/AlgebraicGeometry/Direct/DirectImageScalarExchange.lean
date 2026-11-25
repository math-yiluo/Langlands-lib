/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
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
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantScalarPullbackCube

/-!
# Scalar extension and direct-image geometric exchange

Source: literature/stacks-project/sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal` (blueprint: lem-fix-direct-image-scalar-exchange).

All functors and comparisons below specialize existing canonical constructions to
constant coefficients. No functor, adjunction, tensor comparison or square comparison
is supplied as an arbitrary parameter.
- `directImageScalarExtension` is the universal K-flat scalar extension.
- `directImageScalarPullbackIso` is its canonical tensor/inverse-image comparison.
- `directImageScalarComparison` is the mate defining chi.
- `directImageConstantExchange` is the existing ambient ringed exchange for constants.
- `directImageScalarExchange` is the equality of the two specified composites.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Replaying the categorical transport tactics for unused-tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_exchange_of_cube
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {a : C ⥤ D} {ar : D ⥤ C} {b : C' ⥤ D'} {br : D' ⥤ C'}
    {c : E ⥤ F} {cr : F ⥤ E} {d : E' ⥤ F'} {dr : F' ⥤ E'}
    (aa : a ⊣ ar) (ab : b ⊣ br) (ac : c ⊣ cr) (ad : d ⊣ dr)
    (s : C ⥤ C') (t : D ⥤ D') (v : E ⥤ E') (w : F ⥤ F')
    (g : C ⥤ E) (h : D ⥤ F) (g' : C' ⥤ E') (h' : D' ⥤ F')
    (la : s ⋙ b ⟶ a ⋙ t) (lc : v ⋙ d ⟶ c ⋙ w)
    (lg : s ⋙ g' ⟶ g ⋙ v) (lh : t ⋙ h' ⟶ h ⋙ w)
    (ta : g ⋙ c ⟶ a ⋙ h) (tb : g' ⋙ d ⟶ b ⋙ h')
    (cube : ∀ N : C,
      tb.app (s.obj N) ≫ h'.map (la.app N) ≫ lh.app (a.obj N) =
        d.map (lg.app N) ≫ lc.app (g.obj N) ≫ w.map (ta.app N))
    (M : D) :
    g'.map ((mateEquiv aa ab la).app M) ≫
        (mateEquiv ab ad tb).app (t.obj M) ≫ dr.map (lh.app M) =
      lg.app (ar.obj M) ≫ v.map ((mateEquiv aa ac ta).app M) ≫
        (mateEquiv ac ad lc).app (h.obj M) := by
  apply (ad.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show d.map (dr.map (lh.app M)) ≫ ad.counit.app _ =
    ad.counit.app _ ≫ lh.app M from ad.counit.naturality _]
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 =>
    exact tb.naturality ((mateEquiv aa ab la).app M)
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 =>
    rw [← h'.map_comp, mateEquiv_counit, h'.map_comp]
  slice_lhs 3 4 => exact lh.naturality (aa.counit.app M)
  slice_lhs 1 3 => exact cube (ar.obj M)
  slice_rhs 3 4 => exact mateEquiv_counit ac ad (TwoSquare.mk _ _ _ _ lc) (h.obj M)
  slice_rhs 2 3 => exact lc.naturality ((mateEquiv aa ac ta).app M)
  simp only [Functor.comp_map, Category.assoc]
  slice_rhs 3 4 => rw [← w.map_comp, mateEquiv_counit, w.map_comp]
  rfl

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] directImageConstantAdjunction
  Scheme.completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Scheme.proEtaleRingModulePullback
  Scheme.proEtaleConstantRingComparison
  Scheme.proEtaleRingDerivedAdjunction Scheme.proEtaleReductionPullbackIso
  Scheme.proEtaleAmbientRingedPullbackComparison

end AlgebraicGeometry.ProEtale
