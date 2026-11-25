/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Ring.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Order.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-! # Ordinary scalar extension and canonical locally closed extension

Source: blueprint integral-models-generators proof (1), rationalization of the extensions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

section MateIdentity

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {T : A ⥤ B} {S : B ⥤ A} {T' : A' ⥤ B'} {S' : B' ⥤ A'}
  {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}

private theorem push_eq_mate_pull_inv (a : T ⊣ S) (b : T' ⊣ S')
    (c : l ⊣ r) (d : l' ⊣ r') (e : r' ⋙ S' ≅ S ⋙ r) :
    Adjunction.pushHomOfComapIso a b e =
      (mateEquiv c d (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a b c d e).inv)) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm c d b a
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (mateEquiv c d).symm.injective
  change (mateEquiv c d).symm ((mateEquiv a b).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv c d).symm
      (mateEquiv c d (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a b c d e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

end MateIdentity

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriek

-- The closed-support mate argument also appears in QcqsLatticeTreeReconstruction.
private theorem closed_scalar_iso
    {A R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj R] [IsCommMonObj R]
    (a : A ⟶ R) [IsMonHom a] {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    [QuasiCompact j] (h : Set.range j = (Set.range i)ᶜ)
    (B : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj A Z)) :
    IsIso ((CondensedRing.pushHom a i).app B) := by
  have hiA := CondensedRing.moduleCounitOfAbelian A i
    (ProEtale.abelian_closed_support_counit_and_unit i j h).1
  have hiR := CondensedRing.moduleCounitOfAbelian R i
    (ProEtale.abelian_closed_support_counit_and_unit i j h).1
  let δ := (CondensedRing.pushHom a i).app B
  apply (CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl R i j
    (by rw [h]; exact isCompl_compl)).isIso_of_pairFunctor δ
  · have hzA := CondensedRing.openRestrictionPushforwardZero A i j h B
    have hzR := CondensedRing.openRestrictionPushforwardZero R i j h
      ((Mod.extendScalars (coefficientMap a Z)).obj B)
    have hz := ((Mod.extendScalars (coefficientMap a U)).map_isZero hzA).of_iso
      ((CondensedRing.pullIso a j).app ((CondensedRing.lowerStar A i).obj B)).symm
    exact hz.isIso hzR _
  · have hd : CondensedRing.pushHom a i =
        (mateEquiv (CondensedRing.upperStarLowerStarAdjunction A i)
          (CondensedRing.upperStarLowerStarAdjunction R i)
          (TwoSquare.mk _ _ _ _ (CondensedRing.pullIso a i).inv)) := by
      simpa only [CondensedRing.pushHom, CondensedRing.pullIso] using
        (push_eq_mate_pull_inv
        (Mod.extendRestrictAdjunction (coefficientMap a Z))
        (Mod.extendRestrictAdjunction (coefficientMap a X))
        (CondensedRing.upperStarLowerStarAdjunction A i)
        (CondensedRing.upperStarLowerStarAdjunction R i) (CondensedRing.comapLowerStarIso a i))
    have he : (CondensedRing.upperStar R i).map δ ≫
        (CondensedRing.upperStarLowerStarAdjunction R i).counit.app
          ((Mod.extendScalars (coefficientMap a Z)).obj B) =
        (CondensedRing.pullIso a i).inv.app ((CondensedRing.lowerStar A i).obj B) ≫
          (Mod.extendScalars (coefficientMap a Z)).map
            ((CondensedRing.upperStarLowerStarAdjunction A i).counit.app B) := by
      change (CondensedRing.upperStar R i).map ((CondensedRing.pushHom a i).app B) ≫ _ = _
      rw [hd]
      exact mateEquiv_counit (CondensedRing.upperStarLowerStarAdjunction A i)
        (CondensedRing.upperStarLowerStarAdjunction R i)
        (TwoSquare.mk _ _ _ _ (CondensedRing.pullIso a i).inv) B
    have : IsIso ((CondensedRing.upperStar R i).map δ ≫
        (CondensedRing.upperStarLowerStarAdjunction R i).counit.app
          ((Mod.extendScalars (coefficientMap a Z)).obj B)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right ((CondensedRing.upperStar R i).map δ)
      ((CondensedRing.upperStarLowerStarAdjunction R i).counit.app _)

/-- Ordinary change of condensed coefficients commutes with locally closed extension.
No flatness or lisseness is needed for this comparison.

Source: blueprint integral-models-generators proof (1), final scalar-extension identity;
Stacks Project, Tags 03DI, 03DJ and 09BM.
(blueprint: lem-sfb-condensed-locally-closed-scalar-extension).

Proof. For an open immersion use the scalar/open-extension adjunction comparison
`CondensedRing.openImmersionShriekIso`. For the closed factor, form the scalar/direct-image
comparison as the mate of the coefficient restriction square. Its restriction to the
closed subscheme is an isomorphism, since the closed counit and the scalar/pullback
comparison are isomorphisms. On the complementary open both modules vanish: closed
extension has zero restriction, scalar extension preserves zero, and scalar extension
commutes with pullback. Open/closed detection therefore makes this comparison invertible.
Apply this to the closed inclusion of the scheme-theoretic closure and compose with the
open comparison. This identifies the actual open-then-closed functors in the statement.
Zero modules and empty immersions are included by the same restriction argument. -/
theorem condensedLocallyClosedExtension_scalar
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c]
    {S X : Scheme.{u}} [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)) :
    Nonempty ((coefficientHeartLocallyClosedExtension B a inferInstance).obj
      ((Mod.extendScalars ((upperStarFromPoint S).map c)).obj M) ≅
        (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
          ((coefficientHeartLocallyClosedExtension A a inferInstance).obj M)) := by
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have : IsOpenImmersion a.toImage := inferInstance
  let U : X.Opens :=
    ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range U.ι = (Set.range a.imageι)ᶜ := U.range_ι
  have := closed_scalar_iso c U.ι a.imageι hU
    ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M)
  unfold coefficientHeartLocallyClosedExtension
  change Nonempty
    ((CondensedRing.lowerStar B a.imageι).obj
        ((CondensedRing.openImmersionLowerShriek B a.toImage).obj
          ((Mod.extendScalars ((upperStarFromPoint S).map c)).obj M)) ≅
      (Mod.extendScalars ((upperStarFromPoint X).map c)).obj
        ((CondensedRing.lowerStar A a.imageι).obj
          ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M)))
  exact ⟨((CondensedRing.lowerStar B a.imageι).mapIso
      ((CondensedRing.openImmersionShriekIso c a.toImage).symm.app M)) ≪≫
    (asIso ((CondensedRing.pushHom c a.imageι).app
      ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M))).symm⟩

end AlgebraicGeometry.ProEtale
