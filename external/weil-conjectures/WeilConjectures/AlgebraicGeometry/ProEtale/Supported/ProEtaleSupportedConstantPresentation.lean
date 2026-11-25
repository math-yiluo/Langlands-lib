/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Cokernel presentation of the supported constant pro-etale module

The finite-coefficient
argument below does not require a quasi-compact open complement.

## References

* Milne, Lectures on Etale Cohomology, Section 9, proof of Theorem 9.4, p. 67
* Stacks Project, Tag 09AH is the quasi-compact-open model only
* Milne, Section 9
* Stacks, Tags 09AE and 00YV
* Stacks, Tags 09A5 and 03D1
* Bhatt--Scholze, Lemma 4.2.12
* Milne Section 9 and Stacks Tag 09AH
* Milne, Section 9, proof of Theorem 9.4, p. 67
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Constant sections restrict to the same constants on the open localization.
This is the sheafification extension of the scalar-preserving presheaf map. -/
noncomputable def proEtaleFixedOpenConstantMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    proEtaleFixedConstantModule U A ⟶
      (ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          (proEtaleFixedConstantModule X A) :=
  ((sheafificationAdjunction (ProEt.topology U)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).homEquiv _ _).symm
      (Functor.whiskerLeft (MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale j)).op
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))

/-- The open adjunction counit at the constant module. The realization unit identifies
its open coefficient with the same constant module, and the uniquely normalized rank-one
comparisons identify both coefficients with their constant ring sheaves. -/
noncomputable def proEtaleOpenConstantCounit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicExtensionByZero j A).obj (proEtaleConstantModule U A) ⟶
      proEtaleConstantModule X A :=
  (sfIntrinsicExtensionByZero j A).map (proEtaleConstantModuleUnit U A).inv ≫
    (sfIntrinsicModuleEquivalence X A).functor.map
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map
          ((sfIntrinsicModuleEquivalence U A).unitIso.inv.app
            (proEtaleFixedConstantModule U A))) ≫
    (sfIntrinsicModuleEquivalence X A).functor.map
      (((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _).symm
          (proEtaleFixedOpenConstantMap j A)) ≫
    (proEtaleConstantModuleUnit X A).hom

/-- Constant restriction to the closed subscheme, realized in the ordinary module category.
The fixed-scalar arrow extends a ↦ a on the base-changed object. The direct-image
comparison is normalized on scalar-unit sections, and the rank-one comparisons also
preserve constants. Thus its component sends each constant a to that same constant on
W ×[X] Z. -/
noncomputable def proEtaleClosedConstantRestriction {Z X : Scheme.{u}} (i : Z ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleConstantModule X A ⟶
      (proEtaleConstantModuleDirectImage i A).obj (proEtaleConstantModule Z A) :=
  (proEtaleConstantModuleUnit X A).inv ≫
    (sfIntrinsicModuleEquivalence X A).functor.map
      (proEtaleConstantDirectImageMap i
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))) ≫
    (sfIntrinsicDirectImageComparison i A).inv.app (proEtaleFixedConstantModule Z A) ≫
    (proEtaleConstantModuleDirectImage i A).map (proEtaleConstantModuleUnit Z A).hom

namespace ProEt

noncomputable section

variable (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
  [TopologicalSpace R] [DiscreteTopology R]

/-- Continuous functions with pointwise fixed-scalar module operations. -/
private def constantFunctionsPresheaf : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj V := ModuleCat.of R C(V.unop.left, R)
  map f := ModuleCat.ofHom (ContinuousMap.compRightAlgHom R R f.unop.left.base.hom).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem constantFunctionsPresheaf_isSheaf :
    Presheaf.IsSheaf (topology X) (constantFunctionsPresheaf X R) := by
  have : PreservesLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : ReflectsLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    reflectsLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp (topology X) (constantFunctionsPresheaf X R)
    (CategoryTheory.forget (ModuleCat.{u + 1} R))
  change Presheaf.IsSheaf (topology X)
    ((ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf R)
  apply Functor.op_comp_isSheaf_of_isSheaf (F := ProEt.forget X ⋙ Over.forget X)
    (J := topology X) (K := proetaleTopology)
  exact (isSheaf_fpqcTopology_continuousMapPresheaf R).of_le
    proetaleTopology_le_fpqcTopology

/-- The pro-etale sheaf of locally constant functions, with its fixed-scalar action. -/
private def constantFunctionsSheaf : Sheaf (topology X) (ModuleCat.{u + 1} R) :=
  ⟨constantFunctionsPresheaf X R, constantFunctionsPresheaf_isSheaf X R⟩

/-- The constant-function map before sheafification. -/
private def constToFunctions :
    (Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of R R) ⟶
      (constantFunctionsSheaf X R).obj where
  app V := ModuleCat.ofHom
    { toFun := fun a ↦ ContinuousMap.const V.unop.left a
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

private theorem constToFunctions_locallySurjective :
    Presheaf.IsLocallySurjective (topology X) (constToFunctions X R) := by
  constructor
  intro V s₀
  let s : C(V.left, R) := s₀
  let O (x : V.left) : V.left.Opens :=
    ⟨s ⁻¹' {s x}, (isOpen_discrete _).preimage s.continuous⟩
  apply mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
  · intro x
    exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
  · intro x
    refine ⟨s x, ContinuousMap.ext fun y ↦ ?_⟩
    exact y.property.symm

private theorem constToFunctions_locallyInjective :
    Presheaf.IsLocallyInjective (topology X) (constToFunctions X R) := by
  constructor
  intro V a b h
  by_cases hab : a = b
  · subst b
    exact (topology X).superset_covering (fun _ _ _ ↦ rfl) ((topology X).top_mem _)
  · have : IsEmpty V.unop.left :=
      ⟨fun x ↦ hab (congrArg (fun f : C(V.unop.left, R) ↦ f x) h)⟩
    exact (topology X).superset_covering bot_le (bot_mem_topology _)

/-- The constant-module comparison induced by constant functions. -/
private def constantToFunctions :
    (constantSheaf (topology X) (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶
      constantFunctionsSheaf X R :=
  ⟨sheafifyLift _ (constToFunctions X R) (constantFunctionsSheaf X R).property⟩

/-- The comparison preserves the actual constant-presheaf unit. -/
private theorem toSheafify_constantToFunctions :
    toSheafify (topology X) _ ≫ (constantToFunctions X R).hom = constToFunctions X R :=
  toSheafify_sheafifyLift _ _ _

/-- The constant fixed-scalar module sheaf is the sheaf of continuous functions.
Continuous functions to a discrete ring are constant on their open fibres, giving local
surjectivity. Equal constants are equal on every nonempty object, and the empty cover
treats empty objects, giving local injectivity. The associated map of sheaves is thus
locally bijective, hence an isomorphism. No compactness assumption is used. -/
private theorem constantToFunctions_isIso : IsIso (constantToFunctions X R) := by
  have : PreservesLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have := constToFunctions_locallySurjective X R
  have := constToFunctions_locallyInjective X R
  have h := toSheafify_constantToFunctions X R
  refine (Sheaf.isLocallyBijective_iff_isIso (constantToFunctions X R)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (topology X) _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (topology X) _), h]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of continuous functions to the closed or arbitrary base-changed object. -/
private def functionsRestriction {Z X : Scheme.{u}} (f : Z ⟶ X)
    (R : Type (u + 1)) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] :
    constantFunctionsSheaf X R ⟶
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} R) f).obj
        (constantFunctionsSheaf Z R) where
  hom :=
    { app V := ModuleCat.ofHom
        (ContinuousMap.compRightAlgHom R R (pullback.fst V.unop.hom f).base.hom).toLinearMap
      naturality := by
        intro V W g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s₀
        let s : C(V.unop.left, R) := s₀
        apply ContinuousMap.ext
        intro x
        change s (g.unop.left ((pullback.fst W.unop.hom f) x)) =
          s ((pullback.fst V.unop.hom f)
          (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left x))
        exact congrArg (fun t : pullback W.unop.hom f ⟶ V.unop.left ↦ s (t x))
          (show pullback.fst W.unop.hom f ≫ g.unop.left =
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
              pullback.fst V.unop.hom f by
            simp [MorphismProperty.Over.pullback_map_left]) }

/-- A function on a closed subspace is constant near each ambient point on its domain.
Outside the closed subspace choose zero. At a point in its image, extend the open fibre
using the subspace topology. -/
private theorem exists_constant_neighbourhood {T Y : Type u} [TopologicalSpace T]
    [TopologicalSpace Y] (e : Y → T) (he : Topology.IsClosedEmbedding e)
    (R : Type (u + 1)) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (s : C(Y, R)) (x : T) :
    ∃ (O : TopologicalSpace.Opens T) (a : R),
      x ∈ O ∧ ∀ y, e y ∈ O → s y = a := by
  classical
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    obtain ⟨O, hO, hpre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp
      ((isOpen_discrete ({s y} : Set R)).preimage s.continuous)
    refine ⟨⟨O, hO⟩, s y, ?_, ?_⟩
    · change y ∈ e ⁻¹' O
      rw [hpre]
      rfl
    · intro z hz
      change z ∈ e ⁻¹' O at hz
      rw [hpre] at hz
      exact hz
  · exact ⟨⟨(Set.range e)ᶜ, he.isClosed_range.isOpen_compl⟩, 0, hx,
      fun y hy ↦ False.elim (hy ⟨y, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to a closed subscheme is locally surjective on locally constant functions.
The ambient open neighbourhoods supplied by the closed embedding form a Zariski cover. -/
private theorem functionsRestriction_locallySurjective {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (R : Type (u + 1)) [CommRing R]
    [TopologicalSpace R] [DiscreteTopology R] :
    Sheaf.IsLocallySurjective (functionsRestriction i R) := by
  classical
  constructor
  intro V s₀
  let s : C((pullback (C := Scheme.{u}) V.hom i), R) := s₀
  have he := (pullback.fst V.hom i).isClosedEmbedding
  choose O₀ a hx ha using exists_constant_neighbourhood (pullback.fst V.hom i) he R s
  let O (x : V.left) : V.left.Opens := O₀ x
  apply mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
  · intro x
    exact ⟨x, ⟨⟨x, hx x⟩, rfl⟩⟩
  · intro x
    refine ⟨ContinuousMap.const (O x) (a x), ?_⟩
    apply ContinuousMap.ext
    intro y
    change a x = s
      (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
        (ofOpenImmersionHom V (O x).ι)).left y)
    symm
    apply ha x
    have h := congrArg (fun f : pullback
        ((ofOpenImmersion V (O x).ι).hom) i ⟶ V.left ↦ f y)
      (show ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
        (ofOpenImmersionHom V (O x).ι)).left ≫ pullback.fst V.hom i =
        pullback.fst ((ofOpenImmersion V (O x).ι).hom) i ≫ (O x).ι by
          simp [MorphismProperty.Over.pullback_map_left]
          rfl)
    change (pullback.fst V.hom i)
      (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
        (ofOpenImmersionHom V (O x).ι)).left y) ∈ O x
    have h' : (pullback.fst V.hom i)
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
          (ofOpenImmersionHom V (O x).ι)).left y) =
        ((pullback.fst ((ofOpenImmersion V (O x).ι).hom) i) y).val := h
    exact h'.symm ▸ (pullback.fst ((ofOpenImmersion V (O x).ι).hom) i y).property

/-- The constant-sheaf comparisons commute with the actual restriction maps. -/
private theorem constantToFunctions_restriction {Z X : Scheme.{u}} (f : Z ⟶ X)
    (R : Type (u + 1)) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] :
    constantToFunctions X R ≫ functionsRestriction f R =
      AlgebraicGeometry.Scheme.proEtaleConstantDirectImageMap f (ModuleCat.{u + 1} R)
        (ModuleCat.of R R) ≫
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} R) f).map
        (constantToFunctions Z R) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} R) f).obj
      (constantFunctionsSheaf Z R)).property
  change toSheafify (topology X) _ ≫
    (constantToFunctions X R).hom ≫ (functionsRestriction f R).hom =
      toSheafify (topology X) _ ≫
        (AlgebraicGeometry.Scheme.proEtaleConstantDirectImageMap f
          (ModuleCat.{u + 1} R) (ModuleCat.of R R)).hom ≫ _
  rw [← Category.assoc, toSheafify_constantToFunctions]
  rw [← Category.assoc (toSheafify (topology X) _)
    (AlgebraicGeometry.Scheme.proEtaleConstantDirectImageMap f
      (ModuleCat.{u + 1} R) (ModuleCat.of R R)).hom]
  have h := Equiv.apply_symm_apply
    ((sheafificationAdjunction (topology X) (ModuleCat.{u + 1} R)).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of R R))
      ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} R) f).obj
        ((constantSheaf (topology Z) (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R))))
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (toSheafify (topology Z) ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of R R))))
  change toSheafify (topology X) _ ≫
    (AlgebraicGeometry.Scheme.proEtaleConstantDirectImageMap f
      (ModuleCat.{u + 1} R) (ModuleCat.of R R)).hom = _ at h
  rw [h]
  change constToFunctions X R ≫ (functionsRestriction f R).hom =
    Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (toSheafify (topology Z) _) ≫
    Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (constantToFunctions Z R).hom
  rw [← Functor.whiskerLeft_comp, toSheafify_constantToFunctions]
  rfl

end

end ProEt

set_option backward.isDefEq.respectTransparency false in
/-- The open counit and closed restriction compose to zero.
The adjunction identifies any map from the open extension to the closed direct image
with a map into its zero open restriction. Transport through coefficient realization
and the rank-one comparisons preserves the resulting zero composite. -/
private theorem proEtale_supported_constant_presentation_zero (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    proEtaleOpenConstantCounit i.openComplement.ι A ≫
      proEtaleClosedConstantRestriction i A = 0 := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let j := i.openComplement.ι
  let a := ProEtale.openImmersionLowerShriekAdjunction C j
  let b := (a.homEquiv _ _).symm (proEtaleFixedOpenConstantMap j A)
  let r := proEtaleConstantDirectImageMap i C
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
  have hj : Set.range i.base ∩ Set.range j.base = ∅ := by
    ext x
    simp [j, Scheme.Hom.openComplement]
  have hz := ProEtale.isZero_openImmersionRestriction_lowerStar C i j hj
    (proEtaleFixedConstantModule Z A)
  have hbr : b ≫ r = 0 := (a.homEquiv _ _).injective (hz.eq_of_tgt _ _)
  dsimp only [proEtaleOpenConstantCounit, proEtaleClosedConstantRestriction]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change _ ≫ _ ≫ (sfIntrinsicModuleEquivalence X A).functor.map b ≫
    (sfIntrinsicModuleEquivalence X A).functor.map r ≫ _ = 0
  rw [← Functor.map_comp_assoc _ b r, hbr, Functor.map_zero]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The restriction from the constant module on X to the closed direct image is epic.
Identify constant modules with continuous functions. A function on a closed subspace
lifts to a constant on an ambient neighbourhood of each of its points, and zero lifts
it on the complement. These open neighbourhoods form a Zariski cover, so restriction
is locally surjective and hence epic. Transport through the fixed-scalar comparison,
coefficient realization and the normalized rank-one comparisons preserves epimorphisms. -/
private theorem proEtale_closed_constant_restriction_epi (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (proEtaleClosedConstantRestriction i A) := by
  let R := ULift.{u + 1, u} A
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let C := ModuleCat.{u + 1} R
  have hX := ProEt.constantToFunctions_isIso X R
  have hZ := ProEt.constantToFunctions_isIso Z R
  have hf := ProEt.functionsRestriction_locallySurjective i R
  have : Epi (ProEt.constantToFunctions X R ≫ ProEt.functionsRestriction i R) :=
    inferInstance
  rw [ProEt.constantToFunctions_restriction] at this
  have hr : Epi (proEtaleConstantDirectImageMap i C (ModuleCat.of R R)) :=
    (epi_comp_iff_of_isIso _ _).mp this
  dsimp only [proEtaleClosedConstantRestriction]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem fixedOpenConstantMap_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    IsIso (proEtaleFixedOpenConstantMap j A) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let G := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let P := (Functor.const X.ProEtᵒᵖ).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
  have h : proEtaleFixedOpenConstantMap j A =
      (G.pushforwardContinuousSheafificationCompatibility C
        (ProEt.topology U) (ProEt.topology X)).hom.app P := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _
      ((ProEtale.openImmersionRestriction C j).obj
        (proEtaleFixedConstantModule X A)).property
    exact (Equiv.apply_symm_apply
      ((sheafificationAdjunction (ProEt.topology U) C).homEquiv _ _) _).trans
        (G.toSheafify_pullbackSheafificationCompatibility C
          (ProEt.topology U) (ProEt.topology X) P).symm
  rw [h]
  infer_instance

private noncomputable abbrev fixedCounit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :=
  ((ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _).symm
      (proEtaleFixedOpenConstantMap j A)

set_option backward.isDefEq.respectTransparency false in
private theorem fixedCounit_mono {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] : Mono (fixedCounit j A) := by
  have := fixedOpenConstantMap_isIso j A
  apply ProEtale.mono_of_mono_openImmersionLowerShriekAdjunction_unit_app_comp
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  change Mono ((ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _ (fixedCounit j A))
  rw [Equiv.apply_symm_apply]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem fixedCounit_restriction_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    IsIso ((ProEtale.openImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map (fixedCounit j A)) := by
  have := fixedOpenConstantMap_isIso j A
  let adj := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  have h : adj.unit.app _ ≫ (ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map (fixedCounit j A) =
      proEtaleFixedOpenConstantMap j A :=
    (adj.homEquiv _ _).apply_symm_apply _
  have : IsIso (adj.unit.app (proEtaleFixedConstantModule U A) ≫
      (ProEtale.openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).map (fixedCounit j A)) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp this

set_option backward.isDefEq.respectTransparency false in
private theorem fixedKernel_locallySurjective (A : Type u) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (h : fixedCounit i.openComplement.ι A ≫
      proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) = 0) :
    Sheaf.IsLocallySurjective (kernel.lift _ _ h) := by
  classical
  let R := ULift.{u + 1, u} A
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let C := ModuleCat.{u + 1} R
  let r := proEtaleConstantDirectImageMap i C (ModuleCat.of R R)
  let b := fixedCounit i.openComplement.ι A
  let k := kernel.lift r b h
  have := ProEt.constantToFunctions_isIso X R
  have := ProEt.constantToFunctions_isIso Z R
  have := fixedCounit_restriction_isIso i.openComplement.ι A
  have htzero : kernel.ι r ≫ ProEt.constantToFunctions X R ≫
      ProEt.functionsRestriction i R = 0 := by
    rw [ProEt.constantToFunctions_restriction, ← Category.assoc, kernel.condition,
      zero_comp]
  constructor
  intro V s
  let t := (kernel.ι r).hom.app (op V) s
  let g : C(V.left, R) := (ProEt.constantToFunctions X R).hom.app (op V) t
  have hg (y : pullback (C := Scheme.{u}) V.hom i) : g ((pullback.fst V.hom i) y) = 0 := by
    exact congrArg (fun f : C(pullback (C := Scheme.{u}) V.hom i, R) ↦ f y)
      (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op V)) htzero) s)
  let O (x : V.left) : V.left.Opens :=
    ⟨g ⁻¹' {g x}, (isOpen_discrete _).preimage g.continuous⟩
  apply ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
  · intro x
    exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
  · intro x
    let W := ProEt.ofOpenImmersion V (O x).ι
    let a := ProEt.ofOpenImmersionHom V (O x).ι
    have hki : Function.Injective ((kernel.ι r).hom.app (op W)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hnat : (kernel.ι r).hom.app (op W) ((kernel r).obj.map a.op s) =
        (proEtaleFixedConstantModule X A).obj.map a.op t := by
      exact NatTrans.naturality_apply (kernel.ι r).hom a.op s
    by_cases hx : g x = 0
    · refine ⟨0, hki ?_⟩
      rw [map_zero, hnat]
      apply (ModuleCat.mono_iff_injective
        ((ProEt.constantToFunctions X R).hom.app (op W))).mp inferInstance
      simp only [map_zero]
      change (0 : C(W.left, R)) = _
      rw [NatTrans.naturality_apply (ProEt.constantToFunctions X R).hom a.op t]
      apply ContinuousMap.ext
      intro y
      exact (y.property.trans hx).symm
    · have hrange : Set.range ((O x).ι ≫ V.hom) ⊆
          Set.range i.openComplement.ι := by
        rintro _ ⟨y, rfl⟩
        change V.hom y.val ∈ Set.range i.openComplement.ι
        rw [Scheme.Opens.range_ι]
        change V.hom y.val ∉ Set.range i.base
        rintro ⟨z, hz⟩
        obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := V.hom) (g := i) y.val z hz.symm
        have hwzero := hg w
        rw [hw] at hwzero
        exact hx (y.property.symm.trans hwzero)
      let p := IsOpenImmersion.lift i.openComplement.ι W.hom hrange
      have hp : p ≫ i.openComplement.ι = W.hom :=
        IsOpenImmersion.lift_fac _ _ hrange
      have := ProEtale.isIso_app_of_isIso_localizationRestriction C b
        i.openComplement.ι (fixedCounit_restriction_isIso i.openComplement.ι A) W p hp
      obtain ⟨q, hq⟩ := (ConcreteCategory.isIso_iff_bijective
        (b.hom.app (op W))).mp inferInstance |>.surjective
          ((proEtaleFixedConstantModule X A).obj.map a.op t)
      refine ⟨q, hki ?_⟩
      have hk : k ≫ kernel.ι r = b := kernel.lift_ι r b h
      have hkq := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.hom.app (op W)) hk) q
      exact hkq.trans (hq.trans hnat.symm)

/-- The open counit is the kernel inclusion of the closed restriction. -/
private theorem proEtale_open_constant_counit_is_kernel (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (h : proEtaleOpenConstantCounit i.openComplement.ι A ≫
      proEtaleClosedConstantRestriction i A = 0) :
    Nonempty (IsLimit (KernelFork.ofι (proEtaleOpenConstantCounit i.openComplement.ι A) h)) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let j := i.openComplement.ι
  let E := sfIntrinsicModuleEquivalence X A
  let b := fixedCounit j A
  let r := proEtaleConstantDirectImageMap i C
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
  have hj : Set.range i.base ∩ Set.range j.base = ∅ := by
    ext x
    simp [j, Scheme.Hom.openComplement]
  have hz := ProEtale.isZero_openImmersionRestriction_lowerStar C i j hj
    (proEtaleFixedConstantModule Z A)
  let adj := ProEtale.openImmersionLowerShriekAdjunction C j
  have hbr : b ≫ r = 0 := (adj.homEquiv _ _).injective (hz.eq_of_tgt _ _)
  have := fixedCounit_mono j A
  have := fixedKernel_locallySurjective A i hbr
  have : IsIso (kernel.lift r b hbr) := isIso_of_mono_of_epi _
  have hk := kernel.isoKernel r b (asIso (kernel.lift r b hbr))
    (kernel.lift_ι r b hbr)
  have hm := isLimitForkMapOfIsLimit' E.functor hbr hk
  let es := asIso
    ((sfIntrinsicExtensionByZero j A).map (proEtaleConstantModuleUnit _ A).inv ≫
      E.functor.map ((ProEtale.openImmersionLowerShriek C j).map
        ((sfIntrinsicModuleEquivalence _ A).unitIso.inv.app
          (proEtaleFixedConstantModule _ A))))
  let ey := (sfIntrinsicDirectImageComparison i A).symm.app
      (proEtaleFixedConstantModule Z A) ≪≫
    (proEtaleConstantModuleDirectImage i A).mapIso (proEtaleConstantModuleUnit Z A)
  refine ⟨IsKernel.ofIso _ hm (KernelFork.ofι _ h)
    (proEtaleConstantModuleUnit X A) ey es.symm ?_ ?_⟩
  · dsimp only [proEtaleClosedConstantRestriction, ey]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · change es.inv ≫ (es.hom ≫ E.functor.map b ≫
        (proEtaleConstantModuleUnit X A).hom) = _
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl

/-- The constant restriction is the cokernel of the open constant counit, with no
quasi-compactness assumption on the open complement and no finiteness condition on X. -/
theorem proEtale_supported_constant_presentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : proEtaleOpenConstantCounit i.openComplement.ι A ≫
        proEtaleClosedConstantRestriction i A = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (proEtaleClosedConstantRestriction i A) h)) := by
  have h := proEtale_supported_constant_presentation_zero A i
  have := proEtale_closed_constant_restriction_epi A i
  obtain ⟨hk⟩ := proEtale_open_constant_counit_is_kernel A i h
  exact ⟨h, ⟨Abelian.epiIsCokernelOfKernel _ hk⟩⟩

end AlgebraicGeometry.Scheme
