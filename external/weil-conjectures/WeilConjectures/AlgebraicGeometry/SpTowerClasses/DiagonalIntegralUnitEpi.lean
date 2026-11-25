/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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

import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Integral generators of the supported diagonal source

Source: blueprint classes clause (3), supported quotient normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Restriction of locally constant integer functions to the base-changed closed subset. -/
private def integerFunctionsRestriction {Z X : Scheme.{u}} (f : Z ⟶ X) :
    continuousSheaf X ℤ ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj
      (continuousSheaf Z ℤ) where
  hom :=
    { app V := AddCommGrpCat.ofHom
        { toFun s := ULift.up (s.down.comp (pullback.fst V.unop.hom f).base.hom)
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality := by
        intro V W g
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s₀
        let s : C(V.unop.left, ℤ) := s₀.down
        apply ULift.ext
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

/-- A locally constant function on a closed subset is constant near each ambient point. -/
private theorem integer_constant_neighbourhood {T Y : Type u} [TopologicalSpace T]
    [TopologicalSpace Y] (e : Y → T) (he : Topology.IsClosedEmbedding e)
    (s : C(Y, ℤ)) (x : T) :
    ∃ (O : TopologicalSpace.Opens T) (a : ℤ),
      x ∈ O ∧ ∀ y, e y ∈ O → s y = a := by
  classical
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    obtain ⟨O, hO, hpre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp
      ((isOpen_discrete ({s y} : Set ℤ)).preimage s.continuous)
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

private theorem integerFunctionsRestriction_locallySurjective {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf.IsLocallySurjective (integerFunctionsRestriction i) := by
  classical
  constructor
  intro V s₀
  let s : C((pullback (C := Scheme.{u}) V.hom i), ℤ) := s₀.down
  have he := (pullback.fst V.hom i).isClosedEmbedding
  choose O₀ a hx ha using integer_constant_neighbourhood (pullback.fst V.hom i) he s
  let O (x : V.left) : V.left.Opens := O₀ x
  apply ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
  · intro x
    exact ⟨x, ⟨⟨x, hx x⟩, rfl⟩⟩
  · intro x
    refine ⟨ULift.up (ContinuousMap.const (O x) (a x)), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    change a x = s
      (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
        (ProEt.ofOpenImmersionHom V (O x).ι)).left y)
    symm
    apply ha x
    have h := congrArg (fun f : pullback
        ((ProEt.ofOpenImmersion V (O x).ι).hom) i ⟶ V.left ↦ f y)
      (show ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
        (ProEt.ofOpenImmersionHom V (O x).ι)).left ≫ pullback.fst V.hom i =
        pullback.fst ((ProEt.ofOpenImmersion V (O x).ι).hom) i ≫ (O x).ι by
          simp [MorphismProperty.Over.pullback_map_left]
          rfl)
    change (pullback.fst V.hom i)
      (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
        (ProEt.ofOpenImmersionHom V (O x).ι)).left y) ∈ O x
    have h' : (pullback.fst V.hom i)
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).map
          (ProEt.ofOpenImmersionHom V (O x).ι)).left y) =
        ((pullback.fst ((ProEt.ofOpenImmersion V (O x).ι).hom) i) y).val := h
    exact h'.symm ▸ (pullback.fst ((ProEt.ofOpenImmersion V (O x).ι).hom) i y).property

private theorem integerComparison_restriction {Z X : Scheme.{u}} (f : Z ⟶ X) :
    constantSheafToContinuousSheaf X ℤ ≫ integerFunctionsRestriction f =
      Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (constantSheafToContinuousSheaf Z ℤ) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((lowerStar AddCommGrpCat.{u + 1} f).obj (continuousSheaf Z ℤ)).property
  change toSheafify (ProEt.topology X) _ ≫
    (constantSheafToContinuousSheaf X ℤ).hom ≫ (integerFunctionsRestriction f).hom =
      toSheafify (ProEt.topology X) _ ≫
        (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫ _
  rw [← Category.assoc, toSheafify_constantSheafToContinuousSheaf]
  rw [← Category.assoc (toSheafify (ProEt.topology X) _)
    (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom]
  have h := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((lowerStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf (ProEt.topology Z) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (toSheafify (ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
  change toSheafify (ProEt.topology X) _ ≫
    (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom = _ at h
  rw [h]
  change constToContinuousSheaf X ℤ ≫ (integerFunctionsRestriction f).hom =
    Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (toSheafify (ProEt.topology Z) _) ≫
    Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
      (constantSheafToContinuousSheaf Z ℤ).hom
  rw [← Functor.whiskerLeft_comp, toSheafify_constantSheafToContinuousSheaf]
  rfl

/-- The constant integers generate the integral direct image of a closed subscheme.
Source: blueprint classes clause (3), supported quotient normalization; the
open--closed sequence for integral sheaves (Milne, Section 9).
(blueprint: lem-sp-diagonal-integral-unit-epi).

Proof: a locally constant integer section on
its inverse image in a pro-etale chart extends locally to the ambient chart:
near a point of the closed subspace, choose an open neighbourhood on which its
restriction has the chosen constant value, and use zero on the complementary
open. These neighbourhoods cover the ambient chart. Thus restriction from the
constant integer sheaf is locally surjective, hence epic. This argument also
covers the empty chart and the empty scheme. -/
theorem closedIntegralUnit_epi {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (Scheme.proEtaleConstantDirectImageMap i
      AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  have := integerFunctionsRestriction_locallySurjective i
  have : Epi (constantSheafToContinuousSheaf X ℤ ≫
      integerFunctionsRestriction i) := inferInstance
  rw [integerComparison_restriction] at this
  exact (epi_comp_iff_of_isIso _ _).mp this

end AlgebraicGeometry.ProEtale.SpTowerClasses
