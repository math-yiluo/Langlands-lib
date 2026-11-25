/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution

import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.GradedObject.Trifunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.PresheafedSpace
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Topology.Category.CompHausLike.Basic
public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.ContinuousMap.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!
# Recollement with arbitrary condensed coefficients

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, (3.3), (3.4),
Lemma 3.4 and the proof of Lemma 5.3(2); Stacks, Tags 09AH, 09BM, 09AA, 09BN
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
private theorem openRestrictionPushforwardZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj M)) := by
  have hdisjoint : Set.range i.base ∩ Set.range j.base = ∅ := by
    rw [hij]
    exact Set.inter_compl_self _
  have hz : IsZero ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    let V := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
    have hempty : IsEmpty V.left := by
      refine ⟨fun z ↦ ?_⟩
      have hz : (pullback.fst (T.hom ≫ j) i ≫ T.hom ≫ j).base z ∈
          Set.range i.base ∩ Set.range j.base := by
        refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) i z), ?_⟩⟩
        · rw [pullback.condition]
          exact ⟨_, rfl⟩
        · rfl
      rw [hdisjoint] at hz
      exact hz
    exact (isZero_zero Ab.{u + 1}).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  have hz' : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj
      ((ProEtale.lowerStar Ab.{u + 1} i).obj M.X)) :=
    hz.of_iso ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  have hz'' := hz'.of_iso ((profinitePointModuleForgetPullbackIso Λ j).app
    ((lowerStar Λ i).obj M))
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ U)).map_injective
  exact hz''.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem openUnitIsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let a₀ := ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j
  have : IsIso a₀.unit :=
    (ProEtale.openImmersionAdjunctionTriple Ab.{u + 1} j).isIso_unit_iff_isIso_counit.mpr
      (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit Ab.{u + 1} j)
  have ff₀ := a₀.fullyFaithfulLOfIsIsoUnit
  have := ff₀.full
  have := ff₀.faithful
  have hu : IsIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hlin : IsIso (linearOpenImmersionLowerShriekAdjunction Λ j).unit := by
    have hlinapp (M) : IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M) := by
      have hh : IsIso ((Mod.forget _).map
          ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M)) := by
        dsimp [linearOpenImmersionLowerShriekAdjunction, Adjunction.mapModLeftAdjunction,
          Adjunction.mkOfHomEquiv, Adjunction.mk', Mod.forget, Mod.Hom.mk']
        rw [Adjunction.homEquiv_unit]
        simp only [Mod.id_hom']
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        infer_instance
      exact isIso_of_reflects_iso _ (Mod.forget _)
    exact NatIso.isIso_of_isIso_app _
  have ff := (linearOpenImmersionLowerShriekAdjunction Λ j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (Mod.comap (condensedPullbackHom Λ j)).Full :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.full
  have : (Mod.comap (condensedPullbackHom Λ j)).Faithful :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.faithful
  have : (openImmersionLowerShriek Λ j).Full :=
    inferInstanceAs ((Mod.comap (condensedPullbackHom Λ j)) ⋙
      linearOpenImmersionLowerShriek Λ j).Full
  have : (openImmersionLowerShriek Λ j).Faithful :=
    inferInstanceAs ((Mod.comap (condensedPullbackHom Λ j)) ⋙
      linearOpenImmersionLowerShriek Λ j).Faithful
  exact (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful

private theorem moduleCounitOfAbelian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (hAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit) :
    IsIso (upperStarLowerStarAdjunction Λ i).counit := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
    (condensedRingObj Λ X)
  have hε (N) : IsIso (adj.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      change IsIso (adj.counit.app N).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  have ff := adj.fullyFaithfulROfIsIsoCounit
  have he := (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulFunctor
  have hcomp := he.comp ff
  have hfull := hcomp.ofIso (comapPullbackHomCompIso Λ i)
  have := hfull.full
  have := hfull.faithful
  exact (upperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful

set_option backward.isDefEq.respectTransparency false in
private theorem moduleUnitOfAbelian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hAb : IsIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app M.X)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
    (condensedRingObj Λ X)
  let scalar := Mod.extendRestrictAdjunction (condensedPullbackHom Λ i)
  have hη : IsIso (adj.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      change IsIso (adj.unit.app M).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      exact hAb
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hff := Functor.FullyFaithful.ofIso
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulInverse
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ i)).symm
  have := hff.full
  have := hff.faithful
  have : IsIso scalar.unit := scalar.unit_isIso_of_L_fully_faithful
  have hcomp : IsIso ((adj.comp scalar).unit.app M) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  change IsIso (((adj.comp scalar).ofNatIsoRight (comapPullbackHomCompIso Λ i)).unit.app M)
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private theorem exactClosedOfDetection
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Abelian C] [Abelian Z] [Abelian U]
    (ic : C ⥤ Z) (ip : Z ⥤ C) (jc : C ⥤ U)
    [ic.Additive] [ip.Additive] [jc.Additive]
    [PreservesFiniteLimits ip] [PreservesFiniteColimits ic] [PreservesFiniteColimits jc]
    (ai : ic ⊣ ip) [IsIso ai.counit]
    (hzero : ∀ M, IsZero (jc.obj (ip.obj M)))
    (hjoint : ∀ M, IsZero (ic.obj M) → IsZero (jc.obj M) → IsZero M) :
    PreservesFiniteColimits ip := by
  have hepi {M N : Z} (f : M ⟶ N) [Epi f] : Epi (ip.map f) := by
    have heq : ic.map (ip.map f) =
        ai.counit.app M ≫ f ≫ inv (ai.counit.app N) := by
      rw [← Category.assoc, IsIso.eq_comp_inv]
      exact ai.counit.naturality f
    have : Epi (ic.map (ip.map f)) := by rw [heq]; infer_instance
    apply Preadditive.epi_of_isZero_cokernel
    apply hjoint
    · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ _)
    · exact (IsZero.of_epi (cokernel.π _) (hzero N)).of_iso (PreservesCokernel.iso _ _)
  have : ip.PreservesEpimorphisms := ⟨fun f _ ↦ hepi f⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ip
  exact Functor.preservesFiniteColimits_of_preservesHomology ip

private theorem exceptionalAdjointOfSupport
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Abelian C] [Abelian Z] [Abelian U]
    (ic : C ⥤ Z) (ip : Z ⥤ C) (jc : C ⥤ U) (jp : U ⥤ C)
    [ic.Additive] [ip.Additive] [jc.Additive] [jp.Additive]
    [PreservesFiniteLimits jc] [ip.Full] [ip.Faithful]
    (ai : ic ⊣ ip) (aj : jc ⊣ jp) [IsIso aj.counit]
    (hzero : ∀ B, IsZero (jc.obj (ip.obj B)))
    (hsupport : ∀ F, IsZero (jc.obj F) → IsIso (ai.unit.app F)) :
    ∃ ir : C ⥤ Z, Nonempty (ip ⊣ ir) := by
  classical
  let S : C ⥤ C :=
    { obj F := kernel (aj.unit.app F)
      map f := kernel.map _ _ f ((jc ⋙ jp).map f) (aj.unit.naturality f).symm
      map_id F := by apply (cancel_mono (kernel.ι _)).1; simp
      map_comp f g := by apply (cancel_mono (kernel.ι _)).1; simp [Category.assoc] }
  have hs : ∀ F, IsIso (ai.unit.app (S.obj F)) := by
    intro F
    have hj : IsIso (jc.map (aj.unit.app F)) := by
      have : IsIso (jc.map (aj.unit.app F) ≫ aj.counit.app (jc.obj F)) := by
        erw [aj.left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (aj.counit.app (jc.obj F))
    apply hsupport
    exact (isZero_kernel_of_mono (jc.map (aj.unit.app F))).of_iso
      (PreservesKernel.iso jc (aj.unit.app F))
  let ε : S ⋙ ic ⋙ ip ⟶ 𝟭 C :=
    { app F := inv (ai.unit.app (S.obj F)) ≫ kernel.ι (aj.unit.app F)
      naturality F G f := by
        dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map]
        apply (cancel_epi (ai.unit.app (S.obj F))).1
        rw [← Category.assoc]
        erw [← ai.unit.naturality (S.map f)]
        simp [S, Category.assoc] }
  have hvanish {B : Z} {F : C} (f : ip.obj B ⟶ F) : f ≫ aj.unit.app F = 0 := by
    apply (aj.homEquiv (ip.obj B) (jc.obj F)).symm.injective
    rw [aj.homEquiv_counit, aj.homEquiv_counit]
    simp only [Functor.map_comp, Functor.map_zero, zero_comp]
    rw [Category.assoc, aj.left_triangle_components, Category.comp_id]
    exact (hzero B).eq_of_src _ _
  let e (B : Z) (F : C) : (B ⟶ (S ⋙ ic).obj F) ≃ (ip.obj B ⟶ F) :=
    Equiv.ofBijective (fun g ↦ ip.map g ≫ ε.app F) (by
      constructor
      · intro g h heq
        dsimp [ε] at heq
        apply ip.map_injective
        simp only [← Category.assoc] at heq
        exact (cancel_mono _).1 ((cancel_mono (kernel.ι (aj.unit.app F))).1 heq)
      · intro f
        refine ⟨ip.preimage
          (kernel.lift (aj.unit.app F) f (hvanish f) ≫ ai.unit.app (S.obj F)), ?_⟩
        simp [ε, Category.assoc])
  refine ⟨S ⋙ ic, ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun B F ↦ (e B F).symm
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }⟩⟩
  · intro B' B F f g
    change ip.map (f ≫ g) ≫ ε.app F = ip.map f ≫ (ip.map g ≫ ε.app F)
    simp [Functor.map_comp, Category.assoc]
  · intro B F G f g
    apply (e B G).injective
    change (e B G) ((e B G).symm (f ≫ g)) =
      (e B G) ((e B F).symm f ≫ (S ⋙ ic).map g)
    rw [Equiv.apply_symm_apply]
    change f ≫ g = ip.map ((e B F).symm f ≫ (S ⋙ ic).map g) ≫ ε.app G
    have hn := ε.naturality g
    change ip.map ((S ⋙ ic).map g) ≫ ε.app G = ε.app F ≫ g at hn
    rw [Functor.map_comp, Category.assoc, hn]
    have hf := (e B F).apply_symm_apply f
    change ip.map ((e B F).symm f) ≫ ε.app F = f at hf
    rw [← Category.assoc, hf]

private theorem naturalRecollementTriangle
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive U] [HasZeroObject U] [HasShift U ℤ]
    [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
    [HasShift Z ℤ]
    (i : Z ⥤ C) (G : C ⥤ Z) (jUp : C ⥤ U) (jLow : U ⥤ C)
    [i.CommShift ℤ] [G.CommShift ℤ] [jUp.CommShift ℤ] [jLow.CommShift ℤ]
    [jUp.IsTriangulated] (adj : jUp ⊣ jLow) (adj' : i ⊣ G)
    [adj.CommShift ℤ] [adj'.CommShift ℤ] [IsIso adj.counit]
    (hi : i.FullyFaithful) (hzero : ∀ M, IsZero (jUp.obj (i.obj M)))
    (hess : ∀ K, IsZero (jUp.obj K) → i.essImage K) :
    ∃ δ : jUp ⋙ jLow ⟶ G ⋙ i ⋙ shiftFunctor C (1 : ℤ),
      NatTrans.CommShift δ ℤ ∧
      ∀ K, Triangle.mk (adj'.counit.app K) (adj.unit.app K) (δ.app K) ∈ distTriang C := by
  classical
  have hex := Recollement.existsUnique_distTriang_counit_unit adj adj' hi hzero hess
  let w := fun K ↦ (hex K).choose
  have hw : ∀ K, Recollement.triangle adj adj' K (w K) ∈ distTriang C :=
    fun K ↦ (hex K).choose_spec.1
  let δ : jUp ⋙ jLow ⟶ G ⋙ i ⋙ shiftFunctor C (1 : ℤ) :=
    { app := w
      naturality K L f := by
        obtain ⟨τ, h₁, h₂, h₃⟩ := Recollement.exists_triangleHom adj adj' hzero f (hw K) (hw L)
        simpa only [h₁, h₃, Functor.comp_map] using τ.comm₃.symm }
  refine ⟨δ, ?_, hw⟩
  constructor
  intro n
  ext K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  let F := G ⋙ i
  let H := jUp ⋙ jLow
  let S := G ⋙ i ⋙ shiftFunctor C (1 : ℤ)
  let s₁ := ((F.commShiftIso n).app K).symm
  let s₃ := ((H.commShiftIso n).app K).symm
  let w' := (H.commShiftIso n).hom.app K ≫ (shiftFunctor C n).map (w K) ≫
    (S.commShiftIso n).inv.app K
  have he : (shiftFunctor C n).mapTriangle.obj (Recollement.triangle adj adj' K (w K)) ≅
      Recollement.triangle adj adj' (K⟦n⟧) w' := by
    refine Triangle.isoMk _ _ s₁ (Iso.refl _) s₃ ?_ ?_ ?_
    · change (shiftFunctor C n).map (adj'.counit.app K) ≫ 𝟙 _ =
        (F.commShiftIso n).inv.app K ≫ adj'.counit.app (K⟦n⟧)
      dsimp only [F]
      simp
    · change (shiftFunctor C n).map (adj.unit.app K) ≫ (H.commShiftIso n).inv.app K =
        𝟙 _ ≫ adj.unit.app (K⟦n⟧)
      dsimp only [H]
      simp
    · change ((shiftFunctor C n).map (w K) ≫
          ((shiftFunctor C n).commShiftIso (1 : ℤ)).hom.app (F.obj K)) ≫
          (shiftFunctor C (1 : ℤ)).map s₁.hom = s₃.hom ≫ w'
      dsimp only [s₁, s₃, Iso.symm_hom]
      simp only [Iso.app_inv, w', H, Category.assoc, Iso.inv_hom_id_app_assoc]
      simp only [S, F, Functor.commShiftIso_comp_inv_app, Functor.map_comp,
        Functor.comp_map, Category.assoc]
      have hs : (shiftFunctor C n).commShiftIso (1 : ℤ) =
          ((shiftFunctor C (1 : ℤ)).commShiftIso n).symm := by
        apply Iso.ext
        change ((1 * n).negOnePow • shiftFunctorComm C 1 n).hom =
          ((n * 1).negOnePow • shiftFunctorComm C n 1).inv
        rw [Preadditive.smul_iso_hom, Preadditive.smul_iso_inv,
          ← shiftFunctorComm_symm C 1 n]
        simp
      rw [hs]
      simp only [Iso.symm_hom]
      rfl
  have hw' := isomorphic_distinguished _ ((shiftFunctor C n).map_distinguished _ (hw K))
    _ he.symm
  have heq : w' = w (K⟦n⟧) := (hex (K⟦n⟧)).unique hw' (hw _)
  change (H.commShiftIso n).hom.app K ≫ (shiftFunctor C n).map (w K) =
    w (K⟦n⟧) ≫ (S.commShiftIso n).hom.app K
  rw [← heq]
  simp [w', H, S, Category.assoc]

private theorem plusIsZeroOfHomology
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory.Plus C)
    (hK : ∀ n, IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj K)) : IsZero K := by
  apply IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι K
  exact (DerivedCategory.isZero_iff _).2 hK

private theorem plusCompositeZero
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hzero : ∀ M, IsZero (G.obj (F.obj M))) (K : DerivedCategory.Plus A) :
    IsZero (G.mapDerivedCategoryPlus.obj (F.mapDerivedCategoryPlus.obj K)) := by
  apply plusIsZeroOfHomology
  intro n
  exact (hzero _).of_iso
    (((G.mapDerivedCategoryPlusHomologyFunctorIso n).app _).symm ≪≫
      G.mapIso ((F.mapDerivedCategoryPlusHomologyFunctorIso n).app K).symm)

private theorem plusJointZero
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : A ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hjoint : ∀ M, IsZero (F.obj M) → IsZero (G.obj M) → IsZero M)
    (K : DerivedCategory.Plus A) (hF : IsZero (F.mapDerivedCategoryPlus.obj K))
    (hG : IsZero (G.mapDerivedCategoryPlus.obj K)) : IsZero K := by
  apply plusIsZeroOfHomology
  intro n
  exact hjoint _
    (((DerivedCategory.Plus.homologyFunctor B n).map_isZero hF).of_iso
      ((F.mapDerivedCategoryPlusHomologyFunctorIso n).app K))
    (((DerivedCategory.Plus.homologyFunctor C n).map_isZero hG).of_iso
      ((G.mapDerivedCategoryPlusHomologyFunctorIso n).app K))

private theorem essImageOfUnit
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive Z] [HasZeroObject Z] [HasShift Z ℤ]
    [∀ n : ℤ, (shiftFunctor Z n).Additive] [Pretriangulated Z]
    [Preadditive U] [HasZeroObject U] [HasShift U ℤ]
    [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
    (ic : C ⥤ Z) (ip : Z ⥤ C) (jc : C ⥤ U)
    [ic.CommShift ℤ] [jc.CommShift ℤ] [ic.IsTriangulated] [jc.IsTriangulated]
    (ai : ic ⊣ ip) [IsIso ai.counit]
    (hzero : ∀ M, IsZero (jc.obj (ip.obj M)))
    (hjoint : ∀ M, IsZero (ic.obj M) → IsZero (jc.obj M) → IsZero M)
    (K : C) (hK : IsZero (jc.obj K)) : ip.essImage K := by
  obtain ⟨W, v, w, hT⟩ := distinguished_cocone_triangle (ai.unit.app K)
  have hiu : IsIso (ic.map (ai.unit.app K)) := Recollement.isIso_map_unit_app ic ai K
  have hju : IsIso (jc.map (ai.unit.app K)) :=
    isIso_of_source_target_iso_zero _ hK.isoZero (hzero _).isoZero
  have hW : IsZero W := hjoint _
    ((Triangle.isZero₃_iff_isIso₁ _ (ic.map_distinguished _ hT)).2 hiu)
    ((Triangle.isZero₃_iff_isIso₁ _ (jc.map_distinguished _ hT)).2 hju)
  have : IsIso (ai.unit.app K) := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hW
  exact ⟨ic.obj K, ⟨(asIso (ai.unit.app K)).symm⟩⟩

private theorem essImageOfCounit
    {C Z U : Type*} [Category* C] [Category* Z] [Category* U]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive Z] [HasZeroObject Z] [HasShift Z ℤ]
    [∀ n : ℤ, (shiftFunctor Z n).Additive] [Pretriangulated Z]
    [Preadditive U] [HasZeroObject U] [HasShift U ℤ]
    [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
    (jp : U ⥤ C) (jc : C ⥤ U) (ic : C ⥤ Z)
    [ic.CommShift ℤ] [jc.CommShift ℤ] [ic.IsTriangulated] [jc.IsTriangulated]
    (aj : jp ⊣ jc) [IsIso aj.unit]
    (hzero : ∀ M, IsZero (ic.obj (jp.obj M)))
    (hjoint : ∀ M, IsZero (ic.obj M) → IsZero (jc.obj M) → IsZero M)
    (K : C) (hK : IsZero (ic.obj K)) : jp.essImage K := by
  obtain ⟨W, v, w, hT⟩ := distinguished_cocone_triangle (aj.counit.app K)
  have hju : IsIso (jc.map (aj.counit.app K)) := by
    have : IsIso (aj.unit.app (jc.obj K) ≫ jc.map (aj.counit.app K)) := by
      rw [aj.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (aj.unit.app (jc.obj K)) _
  have hiu : IsIso (ic.map (aj.counit.app K)) :=
    isIso_of_source_target_iso_zero _ (hzero _).isoZero hK.isoZero
  have hW : IsZero W := hjoint _
    ((Triangle.isZero₃_iff_isIso₁ _ (ic.map_distinguished _ hT)).2 hiu)
    ((Triangle.isZero₃_iff_isIso₁ _ (jc.map_distinguished _ hT)).2 hju)
  have : IsIso (aj.counit.app K) := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hW
  exact ⟨jc.obj K, ⟨asIso (aj.counit.app K)⟩⟩

private theorem commShiftRestrictedAdjunction
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {iC : C ⥤ C'} {iD : D ⥤ D'} {L : C ⥤ D} {R : D ⥤ C}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    [iC.CommShift ℤ] [iD.CommShift ℤ] [L.CommShift ℤ] [R.CommShift ℤ]
    [L'.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L' ⊣ R') [adj.CommShift ℤ] (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
    (cL : iC ⋙ L' ≅ L ⋙ iD) (cR : iD ⋙ R' ≅ R ⋙ iC)
    [NatTrans.CommShift cL.hom ℤ] [NatTrans.CommShift cR.hom ℤ] :
    (adj.restrictFullyFaithful hiC hiD cL cR).CommShift ℤ := by
  have := hiC.faithful
  apply Adjunction.CommShift.mk'
  have heq : Functor.whiskerRight (adj.restrictFullyFaithful hiC hiD cL cR).unit iC =
      (Functor.leftUnitor iC).hom ≫ (Functor.rightUnitor iC).inv ≫
        Functor.whiskerLeft iC adj.unit ≫ (Functor.associator iC L' R').inv ≫
        Functor.whiskerRight cL.hom R' ≫ (Functor.associator L iD R').hom ≫
        Functor.whiskerLeft L cR.hom ≫ (Functor.associator L R iC).inv := by
    ext X
    simp [Adjunction.map_restrictFullyFaithful_unit_app]
  have : NatTrans.CommShift
      (Functor.whiskerRight (adj.restrictFullyFaithful hiC hiD cL cR).unit iC) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ iC

private theorem commShiftPlusCompatibility
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
  exact inferInstanceAs (NatTrans.CommShift
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) _).hom ℤ)

private theorem functorialInjectiveEmbeddings
    {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian.{u} C] :
    ∃ (J : C ⥤ C) (η : 𝟭 C ⟶ J),
      (∀ M, Mono (η.app M)) ∧ (∀ M, Injective (J.obj M)) := by
  let S := CochainComplex.singleFunctor C 0
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) 0
  let R := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let ηR := CochainComplex.toKInjectiveResolution.{u} C
  let J := S ⋙ R ⋙ E
  let η : 𝟭 C ⟶ J :=
    (HomologicalComplex.singleCompEvalIsoSelf C (ComplexShape.up ℤ) 0).inv ≫
      Functor.whiskerLeft S (Functor.whiskerRight ηR E)
  refine ⟨J, η, ?_, ?_⟩
  · intro M
    have := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C (S.obj M)).1
    dsimp [η]
    infer_instance
  · intro M
    exact CochainComplex.injective_kInjectiveResolutionFunctor_obj_X (S.obj M) 0

private theorem commonBoundResolution
    {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian.{u} C] (a : ℤ) :
    ∃ (I : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
      (α : CochainComplex.Plus.ι C ⟶ I ⋙ CochainComplex.Plus.ι C),
      (∀ K, K.obj.IsGE a → QuasiIso (α.app K)) ∧
      (∀ K, (I.obj K).obj.IsStrictlyGE a) ∧
      (∀ K n, Injective ((I.obj K).obj.X n)) := by
  classical
  obtain ⟨J, η, hη, hJ⟩ := functorialInjectiveEmbeddings (C := C)
  obtain ⟨R, β, hβ, hR, hbound⟩ :=
    CochainComplex.exists_functorial_bounded_injective_resolution J η hη hJ
  let T : CochainComplex.Plus C ⥤ CochainComplex.Plus C :=
    { obj K := ⟨K.obj.truncGE a, ⟨a, inferInstance⟩⟩
      map f := ⟨CochainComplex.truncGEMap f.hom a⟩
      map_id K := by
        apply ObjectProperty.hom_ext
        exact HomologicalComplex.truncGEMap_id K.obj (ComplexShape.embeddingUpIntGE a)
      map_comp f g := by
        apply ObjectProperty.hom_ext
        exact HomologicalComplex.truncGEMap_comp f.hom g.hom
          (ComplexShape.embeddingUpIntGE a) }
  let π : CochainComplex.Plus.ι C ⟶ T ⋙ CochainComplex.Plus.ι C :=
    { app K := K.obj.πTruncGE a
      naturality K L f := (CochainComplex.πTruncGE_naturality f.hom a).symm }
  refine ⟨T ⋙ R, π ≫ Functor.whiskerLeft T β, ?_, ?_, ?_⟩
  · intro K hK
    have : QuasiIso (K.obj.πTruncGE a) := by
      rw [CochainComplex.quasiIso_πTruncGE_iff]
      exact hK
    have := hβ (T.obj K)
    change QuasiIso (K.obj.πTruncGE a ≫ β.app (T.obj K))
    infer_instance
  · intro K
    exact hbound (T.obj K) a inferInstance
  · intro K n
    exact hR (T.obj K) n

private theorem commonBoundAcyclicResolution
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u} C] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (a : ℤ) :
    ∃ (I : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
      (α : CochainComplex.Plus.ι C ⟶ I ⋙ CochainComplex.Plus.ι C),
      (∀ K, K.obj.IsGE a → QuasiIso (α.app K)) ∧
      (∀ K, (I.obj K).obj.IsStrictlyGE a) ∧
      (∀ K n, Injective ((I.obj K).obj.X n)) ∧
      (∀ K, IsIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient C).obj (I.obj K)))) := by
  obtain ⟨I, α, hα, hbound, hinj⟩ := commonBoundResolution (C := C) a
  refine ⟨I, α, hα, hbound, hinj, ?_⟩
  intro K
  apply F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic
  intro n
  have := hinj K n
  exact F.rightAcyclic_of_injective _

private theorem rightDerivedPlus_isGE
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (K : DerivedCategory.Plus C) (a : ℤ)
    (hK : K.IsGE a) : (F.rightDerivedFunctorPlus.obj K).IsGE a := by
  have := hK
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
  intro q hq
  exact F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K a hq

set_option linter.unusedVariables false in
/-- Open-closed recollement on ordinary bounded below derived categories.
Source: Hemo--Richarz--Scholbach, (3.3), (3.4), Lemma 3.4 and Lemma 5.3(2);
Stacks, Tags 09AH, 09BM, 09AA, 09BN
(auxiliary; not a blueprint node).
Proof:
1. Use abelian closed support, and lift its unit and counit isomorphisms to module
objects through the monoidal adjunction and the equivalence given by the coefficient
isomorphism. The open unit is invertible by linearizing the fully faithful extension
by zero and composing with the scalar equivalence.
2. The open restriction of a closed direct image vanishes: after forgetting its action,
its sections on every open-site object are sections over the empty scheme. The other
zero composite follows from the two adjunctions. The restrictions jointly detect zero
objects by the supported-unit assertion. Applying them to cokernels proves exactness
of closed pushforward.
3. Construct i^!F as i^* applied to the kernel of F → j_*j^*F. The open restriction of
this kernel vanishes. Closed support and full faithfulness identify maps into that
kernel with maps into i^!F, giving the exceptional adjunction without choosing an
arbitrary representing object.
4. Derive the four adjunctions using the existing bounded-below derived API. Exact
functors and their composition comparisons preserve full faithfulness. Restrict the
shift-compatible exact adjunctions along the fully faithful inclusions into unbounded
derived categories. For the two right derived functors choose the shift structures
induced by their left adjoints. Right-derived homology vanishing gives left t-exactness.
5. Exact functors commute with cohomology. Thus both vanishing composites and joint
zero detection pass to bounded-below derived categories. Complete the closed unit or
the open counit to a triangle: both restrictions kill its cone, so the appropriate
supported object is in the essential image of the closed pushforward or open shriek.
6. Apply the library's general recollement triangle theorem twice. Orthogonality
makes each connecting arrow unique; the corresponding triangle morphisms prove
naturality. Transport the triangle under each signed shift functor and use uniqueness
again. This proves shift compatibility with the prescribed triangle signs.
7. Obtain functorial injective embeddings by applying the K-injective replacement
functor to complexes concentrated in degree zero and evaluating degree zero. Use the
existing bounded injective-resolution theorem. For a prescribed common bound a first
apply good truncation at a, then resolve. The truncation map is a quasi-isomorphism
when the input is cohomologically bounded below by a. Injective terms are acyclic for
each left exact functor, proving the two resolution-unit assertions.
8. The inverse images preserve small colimits by their ordinary adjunctions.

The sheaf-support input is
lem-weil-pbc-proetale-abelian-closed-support; the resolution input is
lem-weil-pbc-functorial-bounded-injective-resolution. Other arguments use proved
library APIs and the explicit constructions in this module. -/
theorem condensed_open_closed_recollement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    Exists fun [hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
    PreservesFiniteLimits (upperStar Λ j) ∧
    PreservesFiniteColimits (upperStar Λ j) ∧
    PreservesFiniteLimits (upperStar Λ i) ∧
    PreservesFiniteColimits (upperStar Λ i) ∧
    PreservesFiniteLimits (openImmersionLowerShriek Λ j) ∧
    PreservesFiniteColimits (openImmersionLowerShriek Λ j) ∧
    PreservesFiniteLimits (lowerStar Λ i) ∧
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ j) ∧
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ i) ∧
    (lowerStar Λ i).Full ∧ (lowerStar Λ i).Faithful ∧
    Nonempty (lowerStar Λ i ⋙ upperStar Λ i ≅ 𝟭 _) ∧
    ∃ (ishriek : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      Exists fun [hadd : ishriek.Additive] ↦
      Exists fun [hleft : PreservesFiniteLimits ishriek] ↦
      ∃ (ash : lowerStar Λ i ⊣ ishriek)
      (aj : D+(openImmersionLowerShriek Λ j) ⊣ D+(upperStar Λ j))
      (bj : D+(upperStar Λ j) ⊣ (lowerStar Λ j).rightDerivedFunctorPlus)
      (ai : D+(upperStar Λ i) ⊣ D+(lowerStar Λ i))
      (bi : D+(lowerStar Λ i) ⊣ ishriek.rightDerivedFunctorPlus),
      Exists fun [hjshift : (lowerStar Λ j).rightDerivedFunctorPlus.CommShift ℤ] ↦
      Exists fun [hishift : ishriek.rightDerivedFunctorPlus.CommShift ℤ] ↦
      aj = derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus Λ j ∧
      bj = derivedUpperStarLowerStarAdjunctionPlus Λ j ∧
      ai = (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryPlusAdjunction ∧
      bi = ash.derivedPlus ∧
      aj.CommShift ℤ ∧ bj.CommShift ℤ ∧ ai.CommShift ℤ ∧ bi.CommShift ℤ ∧
      (D+(lowerStar Λ i)).Full ∧ (D+(lowerStar Λ i)).Faithful ∧
      (∀ K, IsIso (ai.counit.app K)) ∧
      (∀ (K : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
        (a : ℤ), K.IsGE a → (ishriek.rightDerivedFunctorPlus.obj K).IsGE a) ∧
      ∃ (δ : D+(upperStar Λ i) ⋙ D+(lowerStar Λ i) ⟶
          D+(upperStar Λ j) ⋙ D+(openImmersionLowerShriek Λ j) ⋙ shiftFunctor _ (1 : ℤ))
        (ε : D+(upperStar Λ j) ⋙ (lowerStar Λ j).rightDerivedFunctorPlus ⟶
          ishriek.rightDerivedFunctorPlus ⋙ D+(lowerStar Λ i) ⋙ shiftFunctor _ (1 : ℤ)),
        NatTrans.CommShift δ ℤ ∧ NatTrans.CommShift ε ℤ ∧
        (∀ K, Triangle.mk (aj.counit.app K) (ai.unit.app K) (δ.app K) ∈ distTriang _) ∧
        (∀ K, Triangle.mk (bi.counit.app K) (bj.unit.app K) (ε.app K) ∈ distTriang _) ∧
        (∀ a : ℤ, ∃
          (I : CochainComplex.Plus
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
            CochainComplex.Plus
              (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
          (α : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _),
          (∀ K, K.obj.IsGE a → QuasiIso (α.app K)) ∧
          (∀ K, (I.obj K).obj.IsStrictlyGE a) ∧
          (∀ (K) (n : ℤ), Injective ((I.obj K).obj.X n)) ∧
          (∀ K, IsIso (ishriek.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient _).obj (I.obj K))))) ∧
        (∀ a : ℤ, ∃
          (I : CochainComplex.Plus
            (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ⥤
            CochainComplex.Plus
              (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
          (α : CochainComplex.Plus.ι _ ⟶ I ⋙ CochainComplex.Plus.ι _),
          (∀ K, K.obj.IsGE a → QuasiIso (α.app K)) ∧
          (∀ K, (I.obj K).obj.IsStrictlyGE a) ∧
          (∀ (K) (n : ℤ), Injective ((I.obj K).obj.X n)) ∧
          (∀ K, IsIso ((lowerStar Λ j).rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient _).obj (I.obj K))))) := by
  classical
  -- Reuse these witnesses across the derived adjunctions instead of repeating the
  -- quantified tensor and colimit instance searches.
  have hTensor₄ (T : Scheme.{u}) (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
      GradedObject.HasTensor₄ObjExt A B C D := inferInstance
  have hTensor₁₂ (T : Scheme.{u}) (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
      GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance
  have hTensor₂₃ (T : Scheme.{u}) (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
      GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance
  have hTensorLeft (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).obj M) := inferInstance
  have hTensorRight (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).flip.obj M) := inferInstance
  have hAb := ProEtale.isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i
  have hi := moduleCounitOfAbelian Λ i hAb
  have hjunit := openUnitIsIso Λ j
  have hzeroji := openRestrictionPushforwardZero Λ i j hij
  have hzeroij : ∀ M, IsZero ((upperStar Λ i).obj
      ((openImmersionLowerShriek Λ j).obj M)) := by
    intro M
    apply (IsZero.iff_id_eq_zero _).2
    apply ((upperStarLowerStarAdjunction Λ i).homEquiv _ _).injective
    apply ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).injective
    exact (hzeroji _).eq_of_tgt _ _
  have hsupport : ∀ M, IsZero ((upperStar Λ j).obj M) →
      IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
    intro M hjM
    apply moduleUnitOfAbelian Λ i M
    apply ProEtale.abelian_closed_support i j hij
    exact ((Mod.forget _).map_isZero hjM).of_iso
      ((profinitePointModuleForgetPullbackIso Λ j).app M).symm
  have hjcounit : IsIso (upperStarLowerStarAdjunction Λ j).counit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit
      ⟨openImmersionLowerShriekUpperStarAdjunction Λ j,
        upperStarLowerStarAdjunction Λ j⟩).1 hjunit
  have hjoint : ∀ M, IsZero ((upperStar Λ i).obj M) →
      IsZero ((upperStar Λ j).obj M) → IsZero M := by
    intro M hiM hjM
    have := hsupport M hjM
    exact ((lowerStar Λ i).map_isZero hiM).of_iso
      (asIso ((upperStarLowerStarAdjunction Λ i).unit.app M))
  have hclosed := exactClosedOfDetection (upperStar Λ i) (lowerStar Λ i)
    (upperStar Λ j) (upperStarLowerStarAdjunction Λ i) hzeroji hjoint
  have ff := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  let e := asIso (upperStarLowerStarAdjunction Λ i).counit
  let ai := (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryPlusAdjunction
  have dff := ai.fullyFaithfulROfCompIsoId
    ((Functor.mapDerivedCategoryPlusCompIso (lowerStar Λ i) (upperStar Λ i)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso e ≪≫ Functor.mapDerivedCategoryPlusIdIso _)
  have := dff.full
  have := dff.faithful
  have hjcol : PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ j) :=
    (upperStarLowerStarAdjunction Λ j).leftAdjoint_preservesColimits
  have hicol : PreservesColimitsOfSize.{u + 1, u + 1} (upperStar Λ i) :=
    (upperStarLowerStarAdjunction Λ i).leftAdjoint_preservesColimits
  refine ⟨hclosed, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hjcol, hicol, ff.full, ff.faithful, ⟨e⟩, ?_⟩
  -- Selecting the witnesses avoids eliminating an existential into this large dependent goal.
  have hexceptional :=
    exceptionalAdjointOfSupport (upperStar Λ i) (lowerStar Λ i)
      (upperStar Λ j) (lowerStar Λ j) (upperStarLowerStarAdjunction Λ i)
      (upperStarLowerStarAdjunction Λ j) hzeroji hsupport
  let ishriek := hexceptional.choose
  let ash := Classical.choice hexceptional.choose_spec
  have := ash.right_adjoint_additive
  have := ash.rightAdjoint_preservesLimits
  let aj := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus Λ j
  let bj := derivedUpperStarLowerStarAdjunctionPlus Λ j
  let bi := ash.derivedPlus
  let hjshift := bj.rightAdjointCommShift ℤ
  let hishift := bi.rightAdjointCommShift ℤ
  have hbjs : bj.CommShift ℤ := bj.commShift_of_leftAdjoint ℤ
  have hbis : bi.CommShift ℤ := bi.commShift_of_leftAdjoint ℤ
  have hajs : aj.CommShift ℤ := by
    change Adjunction.CommShift
      (openImmersionLowerShriekUpperStarAdjunction Λ j).mapDerivedCategoryPlusAdjunction ℤ
    have := commShiftPlusCompatibility (openImmersionLowerShriek Λ j)
    have := commShiftPlusCompatibility (upperStar Λ j)
    exact commShiftRestrictedAdjunction _ _ _ _ _
  have hais : ai.CommShift ℤ := by
    change (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryPlusAdjunction.CommShift ℤ
    have := commShiftPlusCompatibility (upperStar Λ i)
    have := commShiftPlusCompatibility (lowerStar Λ i)
    exact commShiftRestrictedAdjunction _ _ _ _ _
  refine ⟨ishriek, inferInstance, inferInstance, ash, aj, bj, ai, bi,
    hjshift, hishift, rfl, rfl, rfl, rfl, hajs, hbjs, hais, hbis, dff.full, dff.faithful,
    (fun K ↦ inferInstance), (fun K a hK ↦ rightDerivedPlus_isGE ishriek K a hK), ?_⟩
  have hGX : IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    Mod.isGrothendieckAbelian _
  have hGU : IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :=
    Mod.isGrothendieckAbelian _
  have hresX := fun a ↦ commonBoundAcyclicResolution ishriek a
  have hresU := fun a ↦ commonBoundAcyclicResolution (lowerStar Λ j) a
  let eOpen := (asIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit).symm
  have dffj := aj.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryPlusCompIso (openImmersionLowerShriek Λ j)
      (upperStar Λ j)).symm ≪≫ Functor.mapDerivedCategoryPlusNatIso eOpen ≪≫
      Functor.mapDerivedCategoryPlusIdIso _)
  have := dffj.full
  have := dffj.faithful
  have haju : IsIso aj.unit := aj.unit_isIso_of_L_fully_faithful
  have hbju : IsIso bj.counit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨aj, bj⟩).1 haju
  have haic : IsIso ai.counit := ai.counit_isIso_of_R_fully_faithful
  have hDji := plusCompositeZero (lowerStar Λ i) (upperStar Λ j) hzeroji
  have hDij := plusCompositeZero (openImmersionLowerShriek Λ j) (upperStar Λ i) hzeroij
  have hDjoint := plusJointZero (upperStar Λ i) (upperStar Λ j) hjoint
  have hδ := naturalRecollementTriangle
    D+(openImmersionLowerShriek Λ j) D+(upperStar Λ j)
    D+(upperStar Λ i) D+(lowerStar Λ i) ai aj dffj hDij
    (essImageOfCounit D+(openImmersionLowerShriek Λ j) D+(upperStar Λ j)
      D+(upperStar Λ i) aj hDij hDjoint)
  have hε := naturalRecollementTriangle
    D+(lowerStar Λ i) ishriek.rightDerivedFunctorPlus
    D+(upperStar Λ j) (lowerStar Λ j).rightDerivedFunctorPlus bj bi dff hDji
    (essImageOfUnit D+(upperStar Λ i) D+(lowerStar Λ i)
      D+(upperStar Λ j) ai hDji hDjoint)
  exact ⟨hδ.choose, hε.choose, hδ.choose_spec.1, hε.choose_spec.1,
    hδ.choose_spec.2, hε.choose_spec.2, hresX, hresU⟩

end AlgebraicGeometry.ProEtale.CondensedRing
