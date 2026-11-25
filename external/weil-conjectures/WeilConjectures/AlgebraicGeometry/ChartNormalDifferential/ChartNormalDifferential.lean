/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
import WeilConjectures.AlgebraicGeometry.DiagonalConormalDerivation
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineComparison
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionCentredCoordinates
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import all WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraHomExt
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The actual normal comparison of an etale coordinate chart

Source: current blueprint, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Steps 1--2; Stacks Tags 0633--0635, 0473,
08S2 and 01LX (blueprint: lem-pur-chart-normal-differential).

The specification below retains the canonical graded maps, their relative spectra,
and the difference convention. No map or isomorphism is chosen from its existence.
The relative-spectrum normal cone is the existing PurityNormalBundle construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ChartNormalDifferential

/-- The existing relative-spectrum identification for the actual conormal algebra.
Source: Stacks Tags 0636, 01LX (blueprint: lem-pur-chart-normal-differential). -/
def normalAlgebraIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (ConormalGradedAlgebra.presentation i).algebra ≅
      Under.mk (⟨(PurityNormalBundle.projection i).c⟩ : Z.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (PurityNormalBundle.projection i).base).obj (PurityNormalBundle.normalCone i).sheaf) :=
  ((ObjectProperty.ι (fun A : Z.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence Z).counitIso.app
      (PurityNormalBundle.algebraObject i))).symm

/-- Sectionwise normalization of a relative-spectrum map by an algebra pullback.
The equation includes all sections, not just degree one. Source: Stacks Tag 01LX
(blueprint: lem-pur-chart-normal-differential). -/
def IsSpecMap {Z Z' N N' : Scheme.{u}} (f : Z ⟶ Z')
    (B : Z.CommAlgebraSheaf) (B' : Z'.CommAlgebraSheaf)
    (π : N ⟶ Z) (π' : N' ⟶ Z')
    (α : B ≅ Under.mk (⟨π.c⟩ : Z.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj N.sheaf))
    (α' : B' ≅ Under.mk (⟨π'.c⟩ : Z'.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} π'.base).obj N'.sheaf))
    (ν : N ⟶ N')
    (ψ : ∀ V : Z'.Opens, B'.right.obj.obj (op V) → B.right.obj.obj (op (f ⁻¹ᵁ V))) : Prop :=
  ∃ h : ν ≫ π' = π ≫ f, ∀ (V : Z'.Opens) (a : B'.right.obj.obj (op V)),
    α.hom.right.hom.app (op (f ⁻¹ᵁ V)) (ψ V a) =
      ν.appLE (π' ⁻¹ᵁ V) (π ⁻¹ᵁ (f ⁻¹ᵁ V))
        (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])
        (α'.hom.right.hom.app (op V) a)

/-- The adjunction sends a section to its pure tensor with one, then applies `c`.
Source: Stacks Tags 0634--0635 (blueprint: lem-pur-chart-normal-differential). -/
def pullbackSection {Z Z' : Scheme.{u}} (f : Z ⟶ Z')
    (M : Z.Modules) (M' : Z'.Modules) (c : (tensorPullback f).obj M' ⟶ M)
    (V : Z'.Opens) (a : M'.val.obj (op V)) : M.val.obj (op (f ⁻¹ᵁ V)) :=
  c.val.app (op (f ⁻¹ᵁ V))
    (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M').val.app (op V) a)

/-- The differential/conormal identification uses the difference second minus first.
This works with either the full ambient product or its open neighbourhood.
Source: Stacks Tag 08S2 (blueprint: lem-pur-chart-normal-differential). -/
def IsDifferenceIdentification {U Y M : Scheme.{u}} (h : U ⟶ Y)
    (δ : U ⟶ M) [IsClosedImmersion δ] (p₁ p₂ : M ⟶ U)
    (ω : h.relativeDifferentials ≅ ConormalGradedAlgebra.piece δ 1) : Prop :=
  ∀ (V : U.Opens) (T : M.Opens) (h₁ : T ≤ p₁ ⁻¹ᵁ V) (h₂ : T ≤ p₂ ⁻¹ᵁ V)
    (hδ : V ≤ δ ⁻¹ᵁ T) (a : Γ(U, V))
    (s : (ConormalGradedAlgebra.power δ 1).val.obj (op T)),
    (ConormalGradedAlgebra.powerInclusion δ 1).val.app (op T) s =
        p₂.appLE V T h₂ a - p₁.appLE V T h₁ a →
      ω.hom.val.app (op V) (h.relativeDifferentialsDerivation.d (X := op V) a) =
        (ConormalGradedAlgebra.piece δ 1).val.map (homOfLE hδ).op
          (ConormalGradedAlgebra.representative δ 1 T s)

/-- A normal/tangent identification is induced by the symmetric-algebra map with the
specified degree-one identification. It fixes the projection and the zero section.
Source: Stacks Tags 0637, 08S2, 01LX
(blueprint: lem-pur-chart-normal-differential). -/
def IsNormalTangentIdentification {U Y M : Scheme.{u}} (h : U ⟶ Y) [Smooth h]
    (δ : U ⟶ M) [IsClosedImmersion δ]
    (ω : h.relativeDifferentials ≅ ConormalGradedAlgebra.piece δ 1)
    (t : PurityNormalBundle.normalCone δ ≅ RelativeTangentBundle.scheme h) : Prop :=
  t.hom ≫ RelativeTangentBundle.projection h = PurityNormalBundle.projection δ ∧
    PurityNormalBundle.zeroSection δ ≫ t.hom = RelativeTangentBundle.zeroSection h ∧
    ∃ β : SymmetricAlgebraSheaf.algebra h.relativeDifferentials ≅
        (ConormalGradedAlgebra.presentation δ).algebra,
      (∀ (V : U.Opens) (a : h.relativeDifferentials.val.obj (op V)),
        β.hom.right.hom.app (op V)
            ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).val.app (op V) a) =
          ((ConormalGradedAlgebra.presentation δ).inclusion 1).val.app (op V)
            (ω.hom.val.app (op V) a)) ∧
      IsSpecMap (𝟙 U) (ConormalGradedAlgebra.presentation δ).algebra
        (SymmetricAlgebraSheaf.algebra h.relativeDifferentials)
        (PurityNormalBundle.projection δ) (RelativeTangentBundle.projection h)
        (normalAlgebraIso δ) (RelativeTangentBundle.algebraIso h) t.hom
        (fun V a ↦ β.hom.right.hom.app (op V) a)

/-- The actual differential is normalized on every local differential `da` by
`da ↦ d(e-sharp a)`. Projection fixes scalars, so the symmetric-algebra universal
property determines the whole scheme map. Source: Stacks Tag 08S2 and the blueprint's
Step 2 (blueprint: lem-pur-chart-normal-differential). -/
def IsDifferential {U A Y : Scheme.{u}} (p : A ⟶ Y) (e : U ⟶ A)
    [Smooth p] [Smooth (e ≫ p)]
    (de : RelativeTangentBundle.scheme (e ≫ p) ⟶ RelativeTangentBundle.scheme p) : Prop :=
  ∃ he : de ≫ RelativeTangentBundle.projection p =
      RelativeTangentBundle.projection (e ≫ p) ≫ e,
    ∀ (V : A.Opens) (a : Γ(A, V)),
      de.appLE ((RelativeTangentBundle.projection p) ⁻¹ᵁ V)
          ((RelativeTangentBundle.projection (e ≫ p)) ⁻¹ᵁ (e ⁻¹ᵁ V))
          (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, he])
          ((RelativeTangentBundle.algebraIso p).hom.right.hom.app (op V)
            ((SymmetricAlgebraSheaf.inclusion p.relativeDifferentials).val.app (op V)
              (p.relativeDifferentialsDerivation.d (X := op V) a))) =
        (RelativeTangentBundle.algebraIso (e ≫ p)).hom.right.hom.app (op (e ⁻¹ᵁ V))
          ((SymmetricAlgebraSheaf.inclusion (e ≫ p).relativeDifferentials).val.app
            (op (e ⁻¹ᵁ V))
            ((e ≫ p).relativeDifferentialsDerivation.d (X := op (e ⁻¹ᵁ V)) (e.app V a)))

section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] tensorPullback tensorPullbackObj ConormalGradedAlgebra.presentation
  PurityNormalBundle.normalCone RelativeTangentBundle.scheme

attribute [local irreducible] normalAlgebraIso PurityNormalBundle.projection
  RelativeTangentBundle.projection PurityNormalBundle.zeroSection
  RelativeTangentBundle.zeroSection RelativeTangentBundle.algebraIso
  Scheme.Hom.relativeDifferentials SymmetricAlgebraSheaf.algebra ConormalGradedAlgebra.piece

/-- All clauses of the chart comparison, with every map normalized. This is a package
of the conclusions of the lemma, not additional hypotheses on a chart.
Source: current blueprint Step 2; Stacks Tags 0633--0635, 0473, 08S2 and 01LX
(blueprint: lem-pur-chart-normal-differential). -/
structure Comparison {U A Y : Scheme.{u}} (d : ℕ) (p : A ⟶ Y) (e : U ⟶ A)
    [IsSeparated p] [IsSeparated (e ≫ p)] [Smooth p] [Smooth (e ≫ p)] where
  /-- The specified open neighbourhood of the diagonal. -/
  O : (pullback (e ≫ p) (e ≫ p)).Opens
  open_set : O.1 =
    (Set.range (fun z : ↥(pullback e e) ↦
      (pullback.map e e (e ≫ p) (e ≫ p) (𝟙 U) (𝟙 U) p (by simp) (by simp)) z) \
      Set.range (fun z : U ↦ (pullback.diagonal (e ≫ p)) z))ᶜ
  δ : U ⟶ O.toScheme
  diagonal_factorization : δ ≫ O.ι = pullback.diagonal (e ≫ p)
  [closed : IsClosedImmersion δ]
  q : O.toScheme ⟶ pullback p p
  q_eq : q = O.ι ≫ pullback.map (e ≫ p) (e ≫ p) p p e e (𝟙 Y)
    (by simp) (by simp)
  square : δ ≫ q = e ≫ pullback.diagonal p
  cartesian : IsLimit (PullbackCone.mk δ e square)
  etale : Etale q
  regular_U : ∀ z : U, ∃ r : Fin d → (pullback (e ≫ p) (e ≫ p)).presheaf.stalk
      ((pullback.diagonal (e ≫ p)) z),
    RingTheory.Sequence.IsRegular
      ((pullback (e ≫ p) (e ≫ p)).presheaf.stalk ((pullback.diagonal (e ≫ p)) z))
      (List.ofFn r) ∧
      Ideal.span (Set.range r) = RingHom.ker ((pullback.diagonal (e ≫ p)).stalkMap z).hom
  codimension_U : ∀ z : U,
    ringKrullDim ((pullback (e ≫ p) (e ≫ p)).presheaf.stalk
      ((pullback.diagonal (e ≫ p)) z)) = ringKrullDim (U.presheaf.stalk z) + (d : WithBot ℕ∞)
  regular_A : ∀ z : A, ∃ r : Fin d → (pullback p p).presheaf.stalk
      ((pullback.diagonal p) z),
    RingTheory.Sequence.IsRegular
      ((pullback p p).presheaf.stalk ((pullback.diagonal p) z)) (List.ofFn r) ∧
      Ideal.span (Set.range r) = RingHom.ker ((pullback.diagonal p).stalkMap z).hom
  codimension_A : ∀ z : A,
    ringKrullDim ((pullback p p).presheaf.stalk ((pullback.diagonal p) z)) =
      ringKrullDim (A.presheaf.stalk z) + (d : WithBot ℕ∞)
  c : (tensorPullback e).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra.toModule ≅
    (ConormalGradedAlgebra.presentation δ).algebra.toModule
  graded_comparison : ConormalGradedAlgebra.IsBaseChangeMap δ (pullback.diagonal p) q e
    square (ConormalGradedAlgebra.presentation δ)
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)) c.hom
  restriction_square : δ ≫ O.ι = (𝟙 U) ≫ pullback.diagonal (e ≫ p)
  restriction : (tensorPullback (𝟙 U)).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).algebra.toModule ≅
    (ConormalGradedAlgebra.presentation δ).algebra.toModule
  graded_restriction : ConormalGradedAlgebra.IsBaseChangeMap δ
    (pullback.diagonal (e ≫ p)) O.ι (𝟙 U) restriction_square
    (ConormalGradedAlgebra.presentation δ)
    (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))) restriction.hom
  r : PurityNormalBundle.normalCone δ ≅
    PurityNormalBundle.normalCone (pullback.diagonal (e ≫ p))
  restriction_spec : IsSpecMap (𝟙 U) (ConormalGradedAlgebra.presentation δ).algebra
    (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).algebra
    (PurityNormalBundle.projection δ)
    (PurityNormalBundle.projection (pullback.diagonal (e ≫ p)))
    (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal (e ≫ p))) r.hom
    (pullbackSection (𝟙 U) _ _ restriction.hom)
  ν : PurityNormalBundle.normalCone δ ⟶ PurityNormalBundle.normalCone (pullback.diagonal p)
  normal_spec : IsSpecMap e (ConormalGradedAlgebra.presentation δ).algebra
    (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra
    (PurityNormalBundle.projection δ) (PurityNormalBundle.projection (pullback.diagonal p))
    (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal p)) ν
    (pullbackSection e _ _ c.hom)
  normal_cartesian : IsPullback ν (PurityNormalBundle.projection δ)
    (PurityNormalBundle.projection (pullback.diagonal p)) e
  zero_section : PurityNormalBundle.zeroSection δ ≫ ν =
    e ≫ PurityNormalBundle.zeroSection (pullback.diagonal p)
  restriction_zero : PurityNormalBundle.zeroSection δ ≫ r.hom =
    PurityNormalBundle.zeroSection (pullback.diagonal (e ≫ p))
  ωU : (e ≫ p).relativeDifferentials ≅
    ConormalGradedAlgebra.piece (pullback.diagonal (e ≫ p)) 1
  difference_U : IsDifferenceIdentification (e ≫ p) (pullback.diagonal (e ≫ p))
    (pullback.fst (e ≫ p) (e ≫ p)) (pullback.snd (e ≫ p) (e ≫ p)) ωU
  ωA : p.relativeDifferentials ≅ ConormalGradedAlgebra.piece (pullback.diagonal p) 1
  difference_A : IsDifferenceIdentification p (pullback.diagonal p)
    (pullback.fst p p) (pullback.snd p p) ωA
  rank_U : (ConormalGradedAlgebra.piece
    (pullback.diagonal (e ≫ p)) 1).IsFiniteLocallyFreeOfRank d
  rank_A : (ConormalGradedAlgebra.piece (pullback.diagonal p) 1).IsFiniteLocallyFreeOfRank d
  tU : PurityNormalBundle.normalCone (pullback.diagonal (e ≫ p)) ≅
    RelativeTangentBundle.scheme (e ≫ p)
  tangent_U : IsNormalTangentIdentification (e ≫ p) (pullback.diagonal (e ≫ p)) ωU tU
  tA : PurityNormalBundle.normalCone (pullback.diagonal p) ≅ RelativeTangentBundle.scheme p
  tangent_A : IsNormalTangentIdentification p (pullback.diagonal p) ωA tA
  de : RelativeTangentBundle.scheme (e ≫ p) ⟶ RelativeTangentBundle.scheme p
  differential : IsDifferential p e de
  differential_cartesian : IsPullback de (RelativeTangentBundle.projection (e ≫ p))
    (RelativeTangentBundle.projection p) e
  normal_is_differential : r.inv ≫ ν ≫ tA.hom = tU.hom ≫ de

end

attribute [local irreducible] tensorPullback tensorPullbackObj ConormalGradedAlgebra.presentation

attribute [local irreducible] Scheme.Hom.relativeDifferentials

-- Compare the concrete ideal sheaf with the kernel used by the diagonal derivation.
private theorem app_zero_of_eq {Z X : Scheme.{u}} {f g : Z ⟶ X}
    (h : f = g) (V : X.Opens) (a : Γ(X, V)) (ha : f.app V a = 0) :
    g.app V a = 0 := by
  subst g
  exact ha

private theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Opens) (W : X.Opens) (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) :
    f.appLE V W hf = g.appLE V W hg := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem idealKernelIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    ∃ e : i.ker.toModules ≅
        kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom),
      e.hom ≫ kernel.ι _ = i.ker.toModulesι := by
  let φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  have hi : i.ker.toModulesι ≫ φ = 0 := by
    apply Scheme.Modules.hom_ext
    intro V
    ext a
    change i.app V (i.ker.toModulesι.app V a) = 0
    have ha := (i.ker.range_toModulesι_app_eq V).subset ⟨a, rfl⟩
    apply app_zero_of_eq i.toImage_imageι V (i.ker.toModulesι.app V a)
    change i.toImage.app _ (i.ker.subschemeι.app V (i.ker.toModulesι.app V a)) = 0
    rw [ha, map_zero]
  let f : i.ker.toModules ⟶ kernel φ := kernel.lift φ i.ker.toModulesι hi
  have hf : f ≫ kernel.ι φ = i.ker.toModulesι := kernel.lift_ι _ _ _
  have hg : kernel.ι φ ≫ i.ker.toPushforwardSubscheme = 0 := by
    apply Scheme.Modules.hom_ext
    intro V
    ext b
    have hb : i.app V ((kernel.ι φ).val.app (op V) b) = 0 := by
      exact congrArg (fun q ↦ q.val.app (op V) b) (kernel.condition φ)
    change i.ker.subschemeι.app V ((kernel.ι φ).val.app (op V) b) = 0
    apply (ConcreteCategory.bijective_of_isIso
      (i.toImage.app (i.ker.subschemeι ⁻¹ᵁ V))).injective
    rw [map_zero]
    change (i.ker.subschemeι.app V ≫ i.toImage.app _)
      ((kernel.ι φ).val.app (op V) b) = 0
    exact app_zero_of_eq i.toImage_imageι.symm V _ hb
  let g : kernel φ ⟶ i.ker.toModules :=
    kernel.lift i.ker.toPushforwardSubscheme (kernel.ι φ) hg
  have hgι : g ≫ i.ker.toModulesι = kernel.ι φ := kernel.lift_ι _ _ _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (cancel_mono i.ker.toModulesι).mp
    simp only [Category.assoc, hgι, hf, Category.id_comp]
  · apply (cancel_mono (kernel.ι φ)).mp
    simp only [Category.assoc, hf, hgι, Category.id_comp]

private theorem differenceIdentification {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] :
    ∃ ω : f.relativeDifferentials ≅ ConormalGradedAlgebra.piece (pullback.diagonal f) 1,
      IsDifferenceIdentification f (pullback.diagonal f)
        (pullback.fst f f) (pullback.snd f f) ω := by
  obtain ⟨D, hD⟩ := exists_diagonalConormalDerivation f
  let φ : f.relativeDifferentials ⟶ diagonalConormal f :=
    (f.relativeDifferentialsHomEquiv (diagonalConormal f)).symm D
  let B := { U : X.Opens // IsAffineOpen U ∧
    ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V }
  have hB : TopologicalSpace.Opens.IsBasis (Set.range (fun U : B ↦ U.1)) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) TopologicalSpace.isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩) (U ⊓ f ⁻¹ᵁ V).isOpen
    exact ⟨W, ⟨⟨W, hW, V, hV, hWU.trans inf_le_right⟩, rfl⟩,
      hxW, hWU.trans inf_le_left⟩
  have hφ (U : B) : Function.Bijective (φ.app U.1) := by
    obtain ⟨V, hV, hUV⟩ := U.2.2
    exact diagonalConormalComparison_bijective_on_affine f D hD ⟨U.1, U.2.1⟩ ⟨V, hV⟩ hUV
  have : IsIso φ := Scheme.Modules.isIso_of_bijective_app_of_basis hB φ hφ
  let δ := pullback.diagonal f
  obtain ⟨k, hk⟩ := idealKernelIso δ
  let K : ConormalGradedAlgebra.piece δ 1 ≅ diagonalConormal f :=
    (tensorPullback δ).mapIso k
  let ω : f.relativeDifferentials ≅ ConormalGradedAlgebra.piece δ 1 :=
    asIso φ ≪≫ K.symm
  refine ⟨ω, ?_⟩
  intro V T h₁ h₂ hδ a s hs
  have hks : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      δ.toRingCatSheafHom)).val.app (op T) (k.hom.app T s) =
      (ConormalGradedAlgebra.powerInclusion δ 1).val.app (op T) s :=
    congrArg (fun q ↦ q.val.app (op T) s) hk
  have hd := hD V T h₁ h₂ hδ a (k.hom.app T s) (hks.trans hs)
  have hu := ((Classical.choose (exists_tensorPullbackAdjunction δ)).unit.naturality k.hom)
  have hus := congrArg (fun q ↦ q.val.app (op T) s) hu
  have hφa := f.relativeDifferentialsHomEquiv_symm_app_d D a
  apply (ConcreteCategory.bijective_of_isIso (K.hom.app V)).injective
  change K.hom.app V (K.inv.app V (φ.app V _)) = K.hom.app V _
  rw [show K.hom.app V (K.inv.app V (φ.app V _)) = φ.app V _ from
    ConcreteCategory.congr_hom (congrArg (fun q ↦ q.app V) K.inv_hom_id) _]
  change φ.app V (f.relativeDifferentialsDerivation.d (X := op V) a) = D.d a at hφa
  refine hφa.trans (hd.trans ?_)
  exact (congrArg ((diagonalConormal f).presheaf.map (homOfLE hδ).op) hus).trans
    (Hom.app_presheaf_map K.hom (homOfLE hδ)
      (ConormalGradedAlgebra.representative δ 1 T s)).symm

-- The complement of the off-diagonal part of U ×_A U gives the specified open.
set_option backward.isDefEq.respectTransparency false in
private theorem chartGeometry {U A Y : Scheme.{u}} (p : A ⟶ Y) (e : U ⟶ A)
    [IsSeparated p] [Etale e] [IsSeparated (e ≫ p)] :
    ∃ (O : (pullback (e ≫ p) (e ≫ p)).Opens) (δ : U ⟶ O.toScheme),
      O.1 = (Set.range (fun z : ↥(pullback e e) ↦
        (pullback.map e e (e ≫ p) (e ≫ p) (𝟙 U) (𝟙 U) p (by simp) (by simp)) z) \
          Set.range (fun z : U ↦ (pullback.diagonal (e ≫ p)) z))ᶜ ∧
      δ ≫ O.ι = pullback.diagonal (e ≫ p) ∧
      IsPullback δ e (O.ι ≫ pullback.map (e ≫ p) (e ≫ p) p p e e (𝟙 Y)
        (by simp) (by simp)) (pullback.diagonal p) ∧
      Etale (O.ι ≫ pullback.map (e ≫ p) (e ≫ p) p p e e (𝟙 Y)
        (by simp) (by simp)) ∧ IsClosedImmersion δ := by
  let z : pullback e e ⟶ pullback (e ≫ p) (e ≫ p) := pullback.mapDesc e e p
  let ee := pullback.map (e ≫ p) (e ≫ p) p p e e (𝟙 Y) (by simp) (by simp)
  have hp : IsPullback z (pullback.fst e e ≫ e) ee (pullback.diagonal p) :=
    (pullback_map_diagonal_isPullback e e p).flip
  have : IsClosedImmersion z := MorphismProperty.of_isPullback hp.flip inferInstance
  have : IsSeparated e := IsSeparated.of_comp e p
  let Δ := pullback.diagonal e
  have hzΔ : Δ ≫ z = pullback.diagonal (e ≫ p) := by ext <;> simp [Δ, z]
  have hclosed : IsClosed (z '' (Set.range Δ)ᶜ) :=
    z.isClosedEmbedding.isClosedMap _ Δ.isOpenEmbedding.isOpen_range.isClosed_compl
  let O : (pullback (e ≫ p) (e ≫ p)).Opens := ⟨_, hclosed.isOpen_compl⟩
  have hzO : z ⁻¹ᵁ O = Δ.opensRange := by
    ext x
    change z x ∉ z '' (Set.range Δ)ᶜ ↔ x ∈ Set.range Δ
    rw [z.isClosedEmbedding.injective.mem_set_image]
    simp
  have hΔO : Set.range (pullback.diagonal (e ≫ p)) ⊆ O := by
    rintro _ ⟨x, rfl⟩
    have hx : Δ x ∈ z ⁻¹ᵁ O := by rw [hzO]; exact ⟨x, rfl⟩
    have heval : z (Δ x) = (pullback.diagonal (e ≫ p)) x :=
      congrArg (fun k : U ⟶ pullback (e ≫ p) (e ≫ p) ↦ k x) hzΔ
    change z (Δ x) ∈ O.1 at hx
    change (pullback.diagonal (e ≫ p)) x ∈ O.1
    exact heval ▸ hx
  let δ := IsOpenImmersion.lift O.ι (pullback.diagonal (e ≫ p))
    (by simpa only [Scheme.Opens.range_ι] using hΔO)
  have hδ : δ ≫ O.ι = pullback.diagonal (e ≫ p) := IsOpenImmersion.lift_fac ..
  have hsq : IsPullback δ Δ O.ι z := by
    apply IsOpenImmersion.isPullback
    · exact hzΔ.trans hδ.symm
    · simpa using hzO
  have hcomp : Δ ≫ (pullback.fst e e ≫ e) = e := by simp [Δ]
  have hcart : IsPullback δ e (O.ι ≫ ee) (pullback.diagonal p) := by
    simpa only [hcomp] using hsq.paste_vert hp
  have hee : Etale ee := by
    let r : pullback (e ≫ p) (e ≫ p) ⟶ pullback (e ≫ p) p :=
      pullback.map _ _ _ _ (𝟙 U) e (𝟙 Y) (by simp) (by simp)
    let s : pullback (e ≫ p) p ⟶ pullback p p :=
      pullback.map _ _ _ _ e (𝟙 A) (𝟙 Y) (by simp) (by simp)
    have hr : IsPullback r (pullback.snd _ _) (pullback.snd _ _) e :=
      isPullback_pullback_map (e ≫ p) (e ≫ p) p e rfl
    have hs : IsPullback (pullback.fst _ _) s e (pullback.fst _ _) :=
      isPullback_pullback_map_left e p p
    have : Etale r := MorphismProperty.of_isPullback hr.flip inferInstance
    have : Etale s := MorphismProperty.of_isPullback hs inferInstance
    have heq : ee = r ≫ s := by ext <;> simp [ee, r, s]
    rw [heq]
    infer_instance
  have het : Etale (O.ι ≫ ee) := inferInstance
  have hδclosed : IsClosedImmersion δ := by
    have : IsClosedImmersion (δ ≫ O.ι) := hδ ▸ inferInstance
    exact IsClosedImmersion.of_comp δ O.ι
  refine ⟨O, δ, ?_, hδ, hcart, het, hδclosed⟩
  have hr : z '' Set.range Δ = Set.range (pullback.diagonal (e ≫ p)) := by
    rw [← Set.range_comp]
    change Set.range (fun x ↦ (Δ ≫ z) x) = _
    rw [hzΔ]
  change (z '' (Set.range Δ)ᶜ)ᶜ = _
  rw [Set.image_compl_eq_range_sdiff_image z.isClosedEmbedding.injective, hr]

private theorem diagonalRegular {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∀ z : X, ∃ r : Fin d → (pullback f f).presheaf.stalk ((pullback.diagonal f) z),
      RingTheory.Sequence.IsRegular
        ((pullback f f).presheaf.stalk ((pullback.diagonal f) z)) (List.ofFn r) ∧
      Ideal.span (Set.range r) = RingHom.ker ((pullback.diagonal f).stalkMap z).hom) ∧
    (∀ z : X, ringKrullDim ((pullback f f).presheaf.stalk ((pullback.diagonal f) z)) =
      ringKrullDim (X.presheaf.stalk z) + (d : WithBot ℕ∞)) := by
  by_cases hd : 1 ≤ d
  · have h := diagonal_isRegularImmersionOfPureCodimension k aY f d hd
    exact ⟨h.2.2, h.2.1⟩
  · have hd0 : d = 0 := by omega
    subst d
    have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
    let δ := pullback.diagonal f
    have hiso (z : X) : IsIso (δ.stalkMap z) := inferInstance
    constructor
    · intro z
      refine ⟨Fin.elim0, ?_, ?_⟩
      · simpa using (RingTheory.Sequence.IsRegular.nil
          ((pullback f f).presheaf.stalk (δ z))
          ((pullback f f).presheaf.stalk (δ z)))
      · rw [show Set.range (Fin.elim0 : Fin 0 → _) = ∅ from Set.range_eq_empty _,
          Ideal.span_empty]
        exact ((RingHom.injective_iff_ker_eq_bot _).mp
          (ConcreteCategory.bijective_of_isIso (δ.stalkMap z)).injective).symm
    · intro z
      simpa using ringKrullDim_eq_of_ringEquiv
        (asIso (δ.stalkMap z)).commRingCatIsoToRingEquiv

-- Symmetric-algebra maps are determined by their degree-one generators.
private def symmetricMap {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    SymmetricAlgebraSheaf.algebra M ⟶ SymmetricAlgebraSheaf.algebra N :=
  (exists_quasiCoherentSymmetricAlgebra_core X M _
    (f ≫ SymmetricAlgebraSheaf.inclusion N)).exists.choose

private theorem symmetricMap_inclusion {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (V : X.Opens) (a : M.val.obj (op V)) :
    (symmetricMap f).right.hom.app (op V)
        ((SymmetricAlgebraSheaf.inclusion M).val.app (op V) a) =
      (SymmetricAlgebraSheaf.inclusion N).val.app (op V) (f.app V a) :=
  (exists_quasiCoherentSymmetricAlgebra_core X M _
    (f ≫ SymmetricAlgebraSheaf.inclusion N)).exists.choose_spec V a

private def symmetricIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    SymmetricAlgebraSheaf.algebra M ≅ SymmetricAlgebraSheaf.algebra N where
  hom := symmetricMap e.hom
  inv := symmetricMap e.inv
  hom_inv_id := by
    apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core X M _
      (SymmetricAlgebraSheaf.inclusion M))
    · intro V a
      change (symmetricMap e.inv).right.hom.app (op V)
        ((symmetricMap e.hom).right.hom.app (op V) _) = _
      erw [symmetricMap_inclusion, symmetricMap_inclusion]
      have h := congrArg (fun q ↦ q.app V a) e.hom_inv_id
      exact congrArg ((SymmetricAlgebraSheaf.inclusion M).val.app (op V)) h
    · intro V a
      rfl
  inv_hom_id := by
    apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core X N _
      (SymmetricAlgebraSheaf.inclusion N))
    · intro V a
      change (symmetricMap e.hom).right.hom.app (op V)
        ((symmetricMap e.inv).right.hom.app (op V) _) = _
      erw [symmetricMap_inclusion, symmetricMap_inclusion]
      have h := congrArg (fun q ↦ q.app V a) e.inv_hom_id
      exact congrArg ((SymmetricAlgebraSheaf.inclusion N).val.app (op V)) h
    · intro V a
      rfl

private theorem diagonalSymmetric {X Y : Scheme.{u}} [IsNoetherian X]
    (d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] :
    IsIso (ConormalGradedAlgebra.symmetricComparison (pullback.diagonal f)) := by
  exact (SmoothSectionCentredCoordinates.exists_centred_coordinates d
    (pullback.fst f f) (pullback.diagonal f) (by simp)).2.2.2

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_inclusion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (ConormalGradedAlgebra.presentation i).inclusion 1 ≫
      (commAlgebraSheafModuleFunctor Z.sheaf).map
        (ConormalGradedAlgebra.augmentation i) = 0 := by
  let adj := (exists_tensorPullbackAdjunction i).choose
  apply (adj.homEquiv (ConormalGradedAlgebra.power i 1) _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext a
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (i ⁻¹ᵁ U.unop))
    (ConormalGradedAlgebra.homogeneousClass i _ _ 1 U.unop a) = 0
  have h := (ConormalGradedAlgebra.presentation i).augmentation.exists.choose_spec
  simpa only [ConormalGradedAlgebra.augmentation, Nat.one_ne_zero, ↓reduceIte] using
    h 1 U.unop a

private theorem inverse_map_preimage {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) {A B : D} {X : C} (b : A ⟶ B)
    (c : B ⟶ E.functor.obj X) (d : A ⟶ E.functor.obj X) (h : b ≫ c = d) :
    E.inverse.map b ≫ E.functor.preimage ((E.counitIso.app B).hom ≫ c) =
      E.functor.preimage ((E.counitIso.app A).hom ≫ d) := by
  apply E.functor.map_injective
  simp only [Functor.map_comp, Functor.map_preimage]
  have hn := E.counitIso.hom.naturality b
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [← Category.assoc, hn, Category.assoc, h]
  rfl

private theorem symmetricAugmentation {U : Scheme.{u}} {M : U.Modules}
    {B : U.CommAlgebraSheaf} (β : SymmetricAlgebraSheaf.algebra M ≅ B)
    (ε : B ⟶ Under.mk (𝟙 U.sheaf))
    (hε : ∀ V a, ε.right.hom.app (op V)
      (β.hom.right.hom.app (op V) ((SymmetricAlgebraSheaf.inclusion M).app V a)) = 0) :
    β.hom ≫ ε = VectorBundleZeroSection.augmentation U M := by
  apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core U M
    (Under.mk (𝟙 U.sheaf)) 0)
  · exact hε
  · exact (exists_quasiCoherentSymmetricAlgebra_core U M
      (Under.mk (𝟙 U.sheaf)) 0).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
private theorem normalTangentIdentification {U Y M : Scheme.{u}}
    (h : U ⟶ Y) [Smooth h] (δ : U ⟶ M) [IsClosedImmersion δ]
    (ω : h.relativeDifferentials ≅ ConormalGradedAlgebra.piece δ 1)
    [IsIso (ConormalGradedAlgebra.symmetricComparison δ)] :
    ∃ t : PurityNormalBundle.normalCone δ ≅ RelativeTangentBundle.scheme h,
      IsNormalTangentIdentification h δ ω t := by
  let β : SymmetricAlgebraSheaf.algebra h.relativeDifferentials ≅
      (ConormalGradedAlgebra.presentation δ).algebra :=
    symmetricIso ω ≪≫ asIso (ConormalGradedAlgebra.symmetricComparison δ)
  have hβ (V : U.Opens) (a : h.relativeDifferentials.val.obj (op V)) :
      β.hom.right.hom.app (op V)
          ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).val.app (op V) a) =
        ((ConormalGradedAlgebra.presentation δ).inclusion 1).val.app (op V)
          (ω.hom.app V a) := by
    change (ConormalGradedAlgebra.symmetricComparison δ).right.hom.app (op V)
      ((symmetricMap ω.hom).right.hom.app (op V) _) = _
    rw [symmetricMap_inclusion]
    exact (ConormalGradedAlgebra.presentation δ).symmetricComparison.exists.choose_spec _ _
  let E := VectorBundleZeroSection.antiEquivalence U
  let A := RelativeTangentBundle.algebraObject h
  let B := PurityNormalBundle.algebraObject δ
  let b : A ≅ B := ObjectProperty.isoMk _ β
  let tOver := (ObjectProperty.ι (fun T : Over U ↦ IsAffineHom T.hom)).mapIso
    ((E.inverse.mapIso b).unop)
  let t : PurityNormalBundle.normalCone δ ≅ RelativeTangentBundle.scheme h :=
    (Over.forget U).mapIso tOver
  have ht : t.hom ≫ RelativeTangentBundle.projection h = PurityNormalBundle.projection δ :=
    Over.w tOver.hom
  have haug0 : β.hom ≫ ConormalGradedAlgebra.augmentation δ =
      RelativeTangentBundle.augmentation h := by
    apply symmetricAugmentation β
    intro V a
    erw [hβ]
    exact congrArg (fun q ↦ q.app V (ω.hom.app V a)) (augmentation_inclusion δ)
  have haug : β.hom ≫ PurityNormalBundle.augmentationToBase δ =
      VectorBundleZeroSection.augmentationToBase U h.relativeDifferentials := by
    dsimp only [PurityNormalBundle.augmentationToBase]
    rw [← Category.assoc, haug0]
    apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core U
      h.relativeDifferentials ((E.functor.obj (op (VectorBundleZeroSection.baseObject U))).obj) 0)
    · intro V a
      change ((E.functor.obj (op (VectorBundleZeroSection.baseObject U))).obj.hom.hom.app
        (op V)) ((RelativeTangentBundle.augmentation h).right.hom.app (op V)
          ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).app V a)) = 0
      have hv := (exists_quasiCoherentSymmetricAlgebra_core U h.relativeDifferentials
        (Under.mk (𝟙 U.sheaf)) 0).exists.choose_spec V a
      change (RelativeTangentBundle.augmentation h).right.hom.app (op V)
        ((SymmetricAlgebraSheaf.inclusion h.relativeDifferentials).app V a) = 0 at hv
      erw [hv]
    · exact (exists_quasiCoherentSymmetricAlgebra_core U h.relativeDifferentials
        ((E.functor.obj (op (VectorBundleZeroSection.baseObject U))).obj) 0).exists.choose_spec
  have hz : PurityNormalBundle.zeroSection δ ≫ t.hom = RelativeTangentBundle.zeroSection h := by
    have ha : b.hom ≫ ObjectProperty.homMk (PurityNormalBundle.augmentationToBase δ) =
        ObjectProperty.homMk
          (VectorBundleZeroSection.augmentationToBase U h.relativeDifferentials) := by
      apply ObjectProperty.hom_ext
      exact haug
    have he := inverse_map_preimage E b.hom
      (ObjectProperty.homMk (PurityNormalBundle.augmentationToBase δ))
      (ObjectProperty.homMk
        (VectorBundleZeroSection.augmentationToBase U h.relativeDifferentials)) ha
    exact congrArg (fun q ↦ q.unop.hom.left) he
  refine ⟨t, ht, hz, β, hβ, ?_⟩
  refine ⟨by simpa using ht, ?_⟩
  intro V a
  have hn := E.counitIso.inv.naturality b.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have hs := congrArg (fun q ↦ q.hom.right.hom.app (op V) a) hn
  change (normalAlgebraIso δ).hom.right.hom.app (op V)
        (β.hom.right.hom.app (op V) a) =
      (t.hom.appLE (RelativeTangentBundle.projection h ⁻¹ᵁ V)
      (PurityNormalBundle.projection δ ⁻¹ᵁ V) _)
        ((RelativeTangentBundle.algebraIso h).hom.right.hom.app (op V) a) at hs
  exact hs

-- Construct and recognize the actual spectrum maps by their section formulas.
private theorem affineHom_exists {X Y : Scheme.{u}} [IsAffine Y]
    (a : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) : ∃ f : X ⟶ Y, f.appTop = a := by
  let f := ΓSpec.adjunction.homEquiv X (op Γ(Y, ⊤)) a.op ≫ Y.isoSpec.inv
  refine ⟨f, ?_⟩
  have h : f ≫ Y.isoSpec.hom = ΓSpec.adjunction.homEquiv X (op Γ(Y, ⊤)) a.op := by
    simp [f]
  have hh := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, ΓSpec_adjunction_homEquiv_eq] at hh
  apply (cancel_epi (Scheme.ΓSpecIso Γ(Y, ⊤)).hom).mp
  simpa only [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] using hh

private theorem algebraHom_ext {S : Scheme.{u}} [IsAffine S]
    {A B : S.CommAlgebraSheaf} [A.toModule.IsQuasicoherent]
    {a b : A ⟶ B} (h : ∀ x, a.right.hom.app (op ⊤) x = b.right.hom.app (op ⊤) x) :
    a = b := by
  have hm : (commAlgebraSheafModuleFunctor S.sheaf).map a =
      (commAlgebraSheafModuleFunctor S.sheaf).map b := by
    apply Scheme.Modules.hom_ext_of_isAffine (M := A.toModule) (N := B.toModule)
    exact h
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun q ↦ q.val.app V x) hm

private def structureAlgebra {X S : Scheme.{u}} (f : X ⟶ S) :
    S.CommAlgebraSheaf := Under.mk (⟨f.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)

private def structureAlgebraMap {S T Y : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (f : T ⟶ Y) (hf : f ≫ p = t) : structureAlgebra p ⟶ structureAlgebra t := by
  refine Under.homMk ⟨{
    app := fun W ↦ f.appLE (p ⁻¹ᵁ W.unop) (t ⁻¹ᵁ W.unop)
      (by rw [← Scheme.Hom.comp_preimage, hf])
    naturality := ?_ }⟩ ?_
  · intro U W i
    change Y.presheaf.map _ ≫ _ = _ ≫ T.presheaf.map _
    simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    change p.app W.unop ≫ f.appLE _ _ _ = t.app W.unop
    rw [← Scheme.Hom.comp_appLE]
    subst t
    exact Scheme.Hom.appLE_eq_app (f ≫ p)

set_option backward.isDefEq.respectTransparency false in
private theorem specMap_exists {Z Z' N N' : Scheme.{u}} [IsAffine Z']
    (f : Z ⟶ Z') (B : Z.CommAlgebraSheaf) (B' : Z'.CommAlgebraSheaf)
    [B'.toModule.IsQuasicoherent]
    (π : N ⟶ Z) (π' : N' ⟶ Z') [IsAffineHom π']
    (α : B ≅ structureAlgebra π) (α' : B' ≅ structureAlgebra π')
    (ρ : B'.right ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj B.right)
    (hρ : B'.hom ≫ ρ = (⟨f.c⟩ : Z'.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map B.hom) :
    ∃ ν : N ⟶ N', IsSpecMap f B B' π π' α α' ν
      (fun V a ↦ ρ.hom.app (op V) a) := by
  let F := TopCat.Sheaf.pushforward CommRingCat.{u} f.base
  let θ : B' ⟶ structureAlgebra (π ≫ f) :=
    Under.homMk (ρ ≫ F.map α.hom.right) (by
      rw [← Category.assoc, hρ, Category.assoc, ← Functor.map_comp, Under.w α.hom]
      rfl)
  let κ := α'.inv ≫ θ
  have : IsAffine N' := isAffine_of_isAffineHom π'
  obtain ⟨ν, hν⟩ := affineHom_exists (κ.right.hom.app (op ⊤))
  have hw : ν ≫ π' = π ≫ f := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, hν]
    exact congrArg (fun q ↦ q.hom.app (op ⊤)) (Under.w κ)
  have hκ : κ = structureAlgebraMap π' (π ≫ f) ν hw := by
    have : (structureAlgebra π').toModule.IsQuasicoherent :=
      (affine_morphism_relative_spec Z').1 π' inferInstance
    apply algebraHom_ext
    intro a
    change _ = ν.appLE ⊤ ⊤ _ a
    have ht : ν.appLE ⊤ ⊤ (by simp) = ν.appTop := by
      unfold Scheme.Hom.appLE
      rw [show (homOfLE (show (⊤ : N.Opens) ≤ ν ⁻¹ᵁ ⊤ from le_rfl)).op =
        𝟙 (op (⊤ : N.Opens)) from Subsingleton.elim _ _]
      erw [N.presheaf.map_id]
      rfl
    rw [ht]
    exact (congrArg (fun q ↦ q a) hν).symm
  refine ⟨ν, hw, ?_⟩
  intro V a
  have he : α'.hom ≫ κ = θ := by simp [κ]
  rw [hκ] at he
  exact congrArg (fun q ↦ q.right.hom.app (op V) a) he.symm

private theorem algebra_isIso_of_module {S : Scheme.{u}} {A B : S.CommAlgebraSheaf}
    (f : A ⟶ B) [IsIso ((commAlgebraSheafModuleFunctor S.sheaf).map f)] : IsIso f := by
  let k := (commAlgebraSheafModuleFunctor S.sheaf).map f
  have : IsIso k.val := by
    change IsIso ((SheafOfModules.forget S.ringCatSheaf).map k)
    infer_instance
  have (V : S.Opensᵒᵖ) : IsIso (f.right.hom.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have : IsIso (k.val.app V) := by
      change IsIso ((PresheafOfModules.evaluation _ V).map k.val)
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (k.val.app V)
  have : IsIso f.right.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((TopCat.Sheaf.forget CommRingCat S.toTopCat).map f.right) :=
    ‹IsIso f.right.hom›
  have : IsIso f.right := isIso_of_reflects_iso _
    (TopCat.Sheaf.forget CommRingCat S.toTopCat)
  have : IsIso ((Under.forget S.sheaf).map f) := ‹IsIso f.right›
  exact isIso_of_reflects_iso f (Under.forget S.sheaf)

private theorem specIso_exists {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) [IsAffineHom p] [IsAffineHom q]
    {A B : S.CommAlgebraSheaf} (α : A ≅ structureAlgebra p)
    (β : B ≅ structureAlgebra q) (c : B ≅ A) :
    ∃ r : X ≅ Y, IsSpecMap (𝟙 S) A B p q α β r.hom
      (fun V a ↦ c.hom.right.hom.app (op V) a) := by
  let E := VectorBundleZeroSection.antiEquivalence S
  let P : ObjectProperty.FullSubcategory (fun T : Over S ↦ IsAffineHom T.hom) :=
    ⟨Over.mk p, ‹IsAffineHom p›⟩
  let Q : ObjectProperty.FullSubcategory (fun T : Over S ↦ IsAffineHom T.hom) :=
    ⟨Over.mk q, ‹IsAffineHom q›⟩
  let a : E.functor.obj (op Q) ≅ E.functor.obj (op P) :=
    ObjectProperty.isoMk _ (β.symm ≪≫ c ≪≫ α)
  let b := E.functor.preimageIso a
  let r : X ≅ Y := (ObjectProperty.ι _ ⋙ Over.forget S).mapIso b.unop
  have hr : r.hom ≫ q = p := Over.w b.hom.unop.hom
  refine ⟨r, by simpa using hr, ?_⟩
  intro V x
  have hb := E.functor.map_preimage a.hom
  have h := congrArg (fun k ↦ k.hom.right.hom.app (op V)
    (β.hom.right.hom.app (op V) x)) hb
  change r.hom.appLE (q ⁻¹ᵁ V) (p ⁻¹ᵁ V) _
      (β.hom.right.hom.app (op V) x) =
    α.hom.right.hom.app (op V) (c.hom.right.hom.app (op V)
      (β.inv.right.hom.app (op V) (β.hom.right.hom.app (op V) x))) at h
  have hi := congrArg (fun k ↦ k.right.hom.app (op V) x) β.hom_inv_id
  change β.inv.right.hom.app (op V) (β.hom.right.hom.app (op V) x) = x at hi
  erw [hi] at h
  exact h.symm

private theorem pullbackSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {P : X.Modules} (g : M ⟶ N)
    (c : (tensorPullback f).obj N ⟶ P) (V : Y.Opens) (a : M.val.obj (op V)) :
    pullbackSection f P M ((tensorPullback f).map g ≫ c) V a =
      pullbackSection f P N c V (g.app V a) := by
  have hn := congrArg (fun t ↦ t.app V a)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_naturality g)
  exact congrArg (c.app (f ⁻¹ᵁ V)) hn

attribute [local irreducible] moduleBaseChangeMap tensorPullbackObjUnitToUnit

-- Affine pushforward base change identifies the algebra on the scheme pullback.
set_option backward.isDefEq.respectTransparency false in
private theorem specBaseChangeModule {Z Z' N N' : Scheme.{u}}
    (f : Z ⟶ Z') (B : Z'.CommAlgebraSheaf)
    (π : N ⟶ Z') [IsAffineHom π] (α : B ≅ structureAlgebra π)
    (π' : N' ⟶ Z) (g : N' ⟶ N) (sq : IsPullback g π' π f) :
    ∃ b : (tensorPullback f).obj B.toModule ≅ (structureAlgebra π').toModule,
      ∀ (V : Z'.Opens) (a : B.right.obj.obj (op V)),
        b.hom.app (f ⁻¹ᵁ V)
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
            B.toModule).app V a) =
        g.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ (f ⁻¹ᵁ V))
          (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])
          (α.hom.right.hom.app (op V) a) := by
  have := SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := N.ringCatSheaf)
  have := (affinePushforward_baseChange π π' f g sq
    (SheafOfModules.unit N.ringCatSheaf)).2
  have := (tensorPullbackObjUnitToUnit_isIso g).1
  let a := (commAlgebraSheafModuleFunctor Z'.sheaf).mapIso α
  let δ := moduleBaseChangeMap π π' f g sq.w (SheafOfModules.unit N.ringCatSheaf) ≫
    (pushforward π').map (tensorPullbackObjUnitToUnit g)
  have : IsIso δ := by
    dsimp only [δ]
    infer_instance
  let b : (tensorPullback f).obj B.toModule ≅ (structureAlgebra π').toModule :=
    (tensorPullback f).mapIso a ≪≫ asIso δ
  refine ⟨b, ?_⟩
  intro V s
  change pullbackSection f _ _ ((tensorPullback f).map a.hom ≫ δ) V s = _
  rw [pullbackSection_map]
  have hadj := baseChangeUnit_adjoint π π' f g sq.w
  have hv := congrArg (fun t ↦ t.app V
    (α.hom.right.hom.app (op V) s)) hadj
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app] at hv
  exact hv

-- Check equality of pullback-module maps on the adjunction's generating sections.
private theorem pullbackSection_ext {Z Z' : Scheme.{u}} (f : Z ⟶ Z')
    {M : Z.Modules} {M' : Z'.Modules}
    {c d : (tensorPullback f).obj M' ⟶ M}
    (h : ∀ V a, pullbackSection f M M' c V a = pullbackSection f M M' d V a) :
    c = d := by
  apply (Classical.choose (exists_tensorPullbackAdjunction f)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro V
  ext a
  exact h V a

set_option backward.isDefEq.respectTransparency false in
private theorem specMap_cartesian {Z Z' N N' : Scheme.{u}}
    (f : Z ⟶ Z') (B : Z.CommAlgebraSheaf) (B' : Z'.CommAlgebraSheaf)
    (π : N ⟶ Z) (π' : N' ⟶ Z') [IsAffineHom π] [IsAffineHom π']
    (α : B ≅ structureAlgebra π) (α' : B' ≅ structureAlgebra π')
    (c : (tensorPullback f).obj B'.toModule ≅ B.toModule) (ν : N ⟶ N')
    (hν : IsSpecMap f B B' π π' α α' ν (pullbackSection f _ _ c.hom)) :
    IsPullback ν π π' f := by
  obtain ⟨hw, hs⟩ := hν
  let P := pullback π' f
  let p : P ⟶ Z := pullback.snd π' f
  let g : P ⟶ N' := pullback.fst π' f
  let l : N ⟶ P := pullback.lift ν π hw
  have hl : l ≫ p = π := by simp [l, p]
  have : IsAffineHom p := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback π' f) ‹IsAffineHom π'›
  obtain ⟨b, hb⟩ := specBaseChangeModule f B' π' α' p g
    (IsPullback.of_hasPullback π' f)
  let κ := structureAlgebraMap p π l hl
  let k := (commAlgebraSheafModuleFunctor Z.sheaf).map κ
  let a := (commAlgebraSheafModuleFunctor Z.sheaf).mapIso α
  have he : b.hom ≫ k = c.hom ≫ a.hom := by
    apply pullbackSection_ext f
    intro V x
    change l.appLE (p ⁻¹ᵁ (f ⁻¹ᵁ V)) (π ⁻¹ᵁ (f ⁻¹ᵁ V)) _
        (b.hom.app (f ⁻¹ᵁ V) _) =
      α.hom.right.hom.app (op (f ⁻¹ᵁ V)) (pullbackSection f _ _ c.hom V x)
    have hlg : l ≫ g = ν := by simp [l, g]
    have hg : p ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ g ⁻¹ᵁ (π' ⁻¹ᵁ V) :=
      (congrArg (fun k : P ⟶ Z' ↦ k ⁻¹ᵁ V)
        (show g ≫ π' = p ≫ f from pullback.condition)).symm.le
    have hlV : π ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ l ⁻¹ᵁ (p ⁻¹ᵁ (f ⁻¹ᵁ V)) :=
      (congrArg (fun k : N ⟶ Z ↦ k ⁻¹ᵁ (f ⁻¹ᵁ V)) hl).symm.le
    have ht := Scheme.Hom.appLE_comp_appLE l g (π' ⁻¹ᵁ V)
      (p ⁻¹ᵁ (f ⁻¹ᵁ V)) (π ⁻¹ᵁ (f ⁻¹ᵁ V)) hg hlV
    exact (congrArg (fun y ↦ l.appLE (p ⁻¹ᵁ (f ⁻¹ᵁ V))
      (π ⁻¹ᵁ (f ⁻¹ᵁ V)) hlV y) (hb V x)).trans
      ((ConcreteCategory.congr_hom ht (α'.hom.right.hom.app (op V) x)).trans
        ((congrArg (fun k ↦ k (α'.hom.right.hom.app (op V) x))
          (appLE_eq_of_eq hlg (π' ⁻¹ᵁ V) (π ⁻¹ᵁ (f ⁻¹ᵁ V)) _ _)).trans
            (hs V x).symm))
  have hk : k = b.inv ≫ c.hom ≫ a.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  have : IsIso k := by rw [hk]; infer_instance
  have : IsIso κ := algebra_isIso_of_module κ
  let E := VectorBundleZeroSection.antiEquivalence Z
  let X : ObjectProperty.FullSubcategory (fun T : Over Z ↦ IsAffineHom T.hom) :=
    ⟨Over.mk π, ‹IsAffineHom π›⟩
  let Y : ObjectProperty.FullSubcategory (fun T : Over Z ↦ IsAffineHom T.hom) :=
    ⟨Over.mk p, ‹IsAffineHom p›⟩
  let m : X ⟶ Y := ⟨Over.homMk l hl⟩
  have : IsIso (E.functor.map m.op) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    change IsIso κ
    infer_instance
  have : IsIso m.op := isIso_of_reflects_iso m.op E.functor
  have : IsIso m := by
    simpa using (inferInstance : IsIso m.op.unop)
  have : IsIso l := by
    change IsIso ((ObjectProperty.ι _ ⋙ Over.forget Z).map m)
    infer_instance
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso l) (by simp [l]) (by simp [l])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem identitySpecMap {S N N' : Scheme.{u}}
    (B B' : S.CommAlgebraSheaf) (π : N ⟶ S) (π' : N' ⟶ S)
    [IsAffineHom π] [IsAffineHom π']
    (α : B ≅ structureAlgebra π) (α' : B' ≅ structureAlgebra π')
    (c : (tensorPullback (𝟙 S)).obj B'.toModule ≅ B.toModule)
    (ρ : B'.right ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (𝟙 S : S ⟶ S).base).obj
      B.right)
    (hρ : B'.hom ≫ ρ = (⟨(𝟙 S : S ⟶ S).c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (𝟙 S : S ⟶ S).base).obj S.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} (𝟙 S : S ⟶ S).base).map B.hom)
    (hc : ∀ V a, pullbackSection (𝟙 S) _ _ c.hom V a = ρ.hom.app (op V) a) :
    ∃ r : N ≅ N', IsSpecMap (𝟙 S) B B' π π' α α' r.hom
      (pullbackSection (𝟙 S) _ _ c.hom) := by
  let θ : B' ⟶ B := Under.homMk ρ (by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have ht := congrArg (fun q ↦ q.hom.app V) hρ
    change B'.hom.hom.app V ≫ ρ.hom.app V =
      (𝟙 S : S ⟶ S).app V.unop ≫ B.hom.hom.app V at ht
    simpa only [TopCat.Sheaf.comp_app, Scheme.Hom.id_app, Category.id_comp] using ht)
  let adj := Classical.choose (exists_tensorPullbackAdjunction (𝟙 S))
  have he : (commAlgebraSheafModuleFunctor S.sheaf).map θ =
      adj.unit.app B'.toModule ≫ (pushforward (𝟙 S)).map c.hom ≫
        (pushforwardId S).hom.app B.toModule := by
    apply Scheme.Modules.hom_ext
    intro V
    ext a
    exact (hc V a).symm
  have : (tensorPullback (𝟙 S)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Classical.choice (nonempty_tensorPullbackId S)).symm
  have : IsIso ((commAlgebraSheafModuleFunctor S.sheaf).map θ) := by
    rw [he]
    infer_instance
  have : IsIso θ := algebra_isIso_of_module θ
  obtain ⟨r, hr⟩ := specIso_exists π π' α α' (asIso θ)
  refine ⟨r, hr.1, ?_⟩
  intro V a
  rw [hc V a]
  exact hr.2 V a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalZero_app {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : Z.Opens) (a : (ConormalGradedAlgebra.presentation i).algebra.right.obj.obj (op V)) :
    (PurityNormalBundle.zeroSection i).appLE (PurityNormalBundle.projection i ⁻¹ᵁ V) V
      (by rw [← Scheme.Hom.comp_preimage, (PurityNormalBundle.zeroSection_spec i).1]; simp)
      ((normalAlgebraIso i).hom.right.hom.app (op V) a) =
    (ConormalGradedAlgebra.augmentation i).right.hom.app (op V) a := by
  let E := VectorBundleZeroSection.antiEquivalence Z
  let A := PurityNormalBundle.algebraObject i
  have he := E.functor.map_preimage ((E.counitIso.app A).hom ≫
    ObjectProperty.homMk (PurityNormalBundle.augmentationToBase i))
  have ht := congrArg (fun k ↦ (E.counitIso.app A).inv ≫ k) he
  simp only [Iso.inv_hom_id_assoc] at ht
  have hs := congrArg (fun k ↦ k.hom.right.hom.app (op V) a) ht
  exact hs

private theorem schemeHom_ext_over {S X Y : Scheme.{u}} (p : Y ⟶ S)
    [IsAffineHom p] (t : X ⟶ S) (f g : X ⟶ Y)
    (hf : f ≫ p = t) (hg : g ≫ p = t)
    (hs : ∀ V : S.Opens,
      f.appLE (p ⁻¹ᵁ V) (t ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hf]) =
      g.appLE (p ⁻¹ᵁ V) (t ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hg])) : f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show t x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
  refine ⟨t ⁻¹ᵁ V, hxV, ?_⟩
  have : IsAffine (p ⁻¹ᵁ V).toScheme := hV.preimage p
  have he : f.resLE (p ⁻¹ᵁ V) (t ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.comp_preimage, hf]) =
    g.resLE (p ⁻¹ᵁ V) (t ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.comp_preimage, hg]) := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rw [hs V]
  simpa only [Scheme.Hom.resLE_comp_ι] using congrArg (· ≫ (p ⁻¹ᵁ V).ι) he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gradedSection {Z Z' : Scheme.{u}} (f : Z ⟶ Z')
    {A : Z.CommAlgebraSheaf} {A' : Z'.CommAlgebraSheaf}
    {M : Z.Modules} {M' : Z'.Modules} (j : M ⟶ A.toModule) (j' : M' ⟶ A'.toModule)
    (c : (tensorPullback f).obj A'.toModule ⟶ A.toModule)
    (d : (tensorPullback f).obj M' ⟶ M)
    (hc : (tensorPullback f).map j' ≫ c = d ≫ j)
    (V : Z'.Opens) (a : M'.val.obj (op V)) :
    pullbackSection f _ _ c V (j'.app V a) =
      j.app (f ⁻¹ᵁ V) (pullbackSection f _ _ d V a) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  have h := congrArg (fun k ↦ k.app V a) (adj.unit_naturality j')
  change ((tensorPullback f).map j').app (f ⁻¹ᵁ V)
      ((adj.unit.app M').app V a) =
    (adj.unit.app A'.toModule).app V (j'.app V a) at h
  dsimp only [pullbackSection]
  erw [← h]
  exact congrArg (fun k ↦ k.app (f ⁻¹ᵁ V) ((adj.unit.app M').app V a)) hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gradedAugmentation {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (f : Z ⟶ Z')
    (c : (tensorPullback f).obj (ConormalGradedAlgebra.presentation i').algebra.toModule ⟶
      (ConormalGradedAlgebra.presentation i).algebra.toModule)
    (d : (tensorPullback f).obj (ConormalGradedAlgebra.piece i' 1) ⟶
      ConormalGradedAlgebra.piece i 1)
    (ρ : (ConormalGradedAlgebra.presentation i').algebra.right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        (ConormalGradedAlgebra.presentation i).algebra.right)
    (hρ : (ConormalGradedAlgebra.presentation i').algebra.hom ≫ ρ =
      (⟨f.c⟩ : Z'.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
        (ConormalGradedAlgebra.presentation i).algebra.hom)
    (hs : ∀ V a, pullbackSection f _ _ c V a = ρ.hom.app (op V) a)
    (hg : (tensorPullback f).map ((ConormalGradedAlgebra.presentation i').inclusion 1) ≫ c =
      d ≫ (ConormalGradedAlgebra.presentation i).inclusion 1) :
    ∀ (V : Z'.Opens) (a : (ConormalGradedAlgebra.presentation i').algebra.right.obj.obj
      (op V)),
      (ConormalGradedAlgebra.augmentation i).right.hom.app (op (f ⁻¹ᵁ V))
        (ρ.hom.app (op V) a) =
      f.app V ((ConormalGradedAlgebra.augmentation i').right.hom.app (op V) a) := by
  let F := TopCat.Sheaf.pushforward CommRingCat.{u} f.base
  let ψ : (ConormalGradedAlgebra.presentation i').algebra ⟶ structureAlgebra f :=
    Under.homMk (ρ ≫ F.map (ConormalGradedAlgebra.augmentation i).right) (by
      rw [← Category.assoc, hρ, Category.assoc, ← Functor.map_comp,
        Under.w (ConormalGradedAlgebra.augmentation i)]
      change (⟨f.c⟩ : Z'.sheaf ⟶ F.obj Z.sheaf) ≫ F.map (𝟙 Z.sheaf) = _
      exact (congrArg (fun k ↦ (⟨f.c⟩ : Z'.sheaf ⟶ F.obj Z.sheaf) ≫ k)
        (F.map_id Z.sheaf)).trans (Category.comp_id _))
  let ψ' : (ConormalGradedAlgebra.presentation i').algebra ⟶ structureAlgebra f :=
    ConormalGradedAlgebra.augmentation i' ≫ Under.homMk ⟨f.c⟩ (by rfl)
  have he : ψ = ψ' := by
    apply ConormalGradedAlgebra.hom_ext_degree_one i'
    intro T a
    let V := i' ⁻¹ᵁ T.1
    let x := ConormalGradedAlgebra.representative i' 1 T.1 a
    have hgen := gradedSection f ((ConormalGradedAlgebra.presentation i).inclusion 1)
      ((ConormalGradedAlgebra.presentation i').inclusion 1) c d hg V x
    rw [hs] at hgen
    change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (f ⁻¹ᵁ V))
        (ρ.hom.app (op V) (((ConormalGradedAlgebra.presentation i').inclusion 1).app V x)) =
      f.app V ((ConormalGradedAlgebra.augmentation i').right.hom.app (op V)
        (((ConormalGradedAlgebra.presentation i').inclusion 1).app V x))
    erw [hgen]
    have h0 := congrArg (fun k ↦ k.app (f ⁻¹ᵁ V) (pullbackSection f _ _ d V x))
      (augmentation_inclusion i)
    have h0' := congrArg (fun k ↦ k.app V x) (augmentation_inclusion i')
    change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (f ⁻¹ᵁ V)) _ = 0 at h0
    change (ConormalGradedAlgebra.augmentation i').right.hom.app (op V) _ = 0 at h0'
    erw [h0, h0', map_zero]
  intro V a
  exact congrArg (fun k ↦ k.right.hom.app (op V) a) he

-- Augmentation compatibility for an arbitrary normalized spectrum map.
private theorem specMap_zero {Z Z' N N' : Scheme.{u}}
    (f : Z ⟶ Z') (B : Z.CommAlgebraSheaf) (B' : Z'.CommAlgebraSheaf)
    (π : N ⟶ Z) (π' : N' ⟶ Z') [IsAffineHom π']
    (α : B ≅ structureAlgebra π) (α' : B' ≅ structureAlgebra π')
    (ν : N ⟶ N')
    (ρ : ∀ V : Z'.Opens, B'.right.obj.obj (op V) →
      B.right.obj.obj (op (f ⁻¹ᵁ V)))
    (hs : IsSpecMap f B B' π π' α α' ν ρ)
    (z : Z ⟶ N) (z' : Z' ⟶ N') (hz : z ≫ π = 𝟙 Z) (hz' : z' ≫ π' = 𝟙 Z')
    (ε : ∀ V : Z.Opens, B.right.obj.obj (op V) → Γ(Z, V))
    (ε' : ∀ V : Z'.Opens, B'.right.obj.obj (op V) → Γ(Z', V))
    (hzapp : ∀ V a, z.appLE (π ⁻¹ᵁ V) V
      (by rw [← Scheme.Hom.comp_preimage, hz]; simp) (α.hom.right.hom.app (op V) a) = ε V a)
    (hzapp' : ∀ V a, z'.appLE (π' ⁻¹ᵁ V) V
      (by rw [← Scheme.Hom.comp_preimage, hz']; simp) (α'.hom.right.hom.app (op V) a) = ε' V a)
    (hε : ∀ V a, ε (f ⁻¹ᵁ V) (ρ V a) = f.app V (ε' V a)) :
    z ≫ ν = f ≫ z' := by
  have hw : ν ≫ π' = π ≫ f := hs.1
  apply schemeHom_ext_over π' f (z ≫ ν) (f ≫ z')
    (by rw [Category.assoc, hw, ← Category.assoc, hz, Category.id_comp])
    (by rw [Category.assoc, hz', Category.comp_id])
  intro V
  apply (cancel_epi (α'.hom.right.hom.app (op V))).mp
  apply ConcreteCategory.hom_ext
  intro a
  have hν : π ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ ν ⁻¹ᵁ (π' ⁻¹ᵁ V) := by
    exact (congrArg (fun g : N ⟶ Z' ↦
      g ⁻¹ᵁ V) hw).symm.le
  have hzi : f ⁻¹ᵁ V ≤ z ⁻¹ᵁ (π ⁻¹ᵁ (f ⁻¹ᵁ V)) := by
    exact (congrArg (fun g : Z ⟶ Z ↦ g ⁻¹ᵁ (f ⁻¹ᵁ V)) hz).symm.le
  have hz'i : V ≤ z' ⁻¹ᵁ (π' ⁻¹ᵁ V) := by
    exact (congrArg (fun f : Z' ⟶ Z' ↦ f ⁻¹ᵁ V) hz').symm.le
  simp only [ConcreteCategory.comp_apply]
  have hL := Scheme.Hom.appLE_comp_appLE z ν (π' ⁻¹ᵁ V)
    (π ⁻¹ᵁ (f ⁻¹ᵁ V)) (f ⁻¹ᵁ V) hν hzi
  have hR := Scheme.Hom.appLE_comp_appLE f z' (π' ⁻¹ᵁ V) V
    (f ⁻¹ᵁ V) hz'i le_rfl
  have hR' := ConcreteCategory.congr_hom hR
    (α'.hom.right.hom.app (op V) a)
  erw [Scheme.Hom.appLE_eq_app f] at hR'
  let a' := α'.hom.right.hom.app (op V) a
  have hspec := congrArg (fun x ↦ z.appLE (π ⁻¹ᵁ (f ⁻¹ᵁ V))
    (f ⁻¹ᵁ V) hzi x) (hs.2 V a)
  have hzero := hzapp (f ⁻¹ᵁ V) (ρ V a)
  have hzero' := congrArg (fun x ↦ f.app V x) (hzapp' V a)
  exact (ConcreteCategory.congr_hom hL a').symm.trans
    (hspec.symm.trans (hzero.trans ((hε V a).trans
      (hzero'.symm.trans hR'))))

set_option backward.isDefEq.respectTransparency true in
private theorem normalMap_zero {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (f : Z ⟶ Z') (ν : PurityNormalBundle.normalCone i ⟶ PurityNormalBundle.normalCone i')
    (ρ : ∀ V : Z'.Opens,
      (ConormalGradedAlgebra.presentation i').algebra.right.obj.obj (op V) →
        (ConormalGradedAlgebra.presentation i).algebra.right.obj.obj (op (f ⁻¹ᵁ V)))
    (hs : IsSpecMap f (ConormalGradedAlgebra.presentation i).algebra
      (ConormalGradedAlgebra.presentation i').algebra
      (PurityNormalBundle.projection i) (PurityNormalBundle.projection i')
      (normalAlgebraIso i) (normalAlgebraIso i') ν ρ)
    (hε : ∀ V a, (ConormalGradedAlgebra.augmentation i).right.hom.app (op (f ⁻¹ᵁ V))
      (ρ V a) = f.app V ((ConormalGradedAlgebra.augmentation i').right.hom.app (op V) a)) :
    PurityNormalBundle.zeroSection i ≫ ν = f ≫ PurityNormalBundle.zeroSection i' := by
  have : IsAffineHom (PurityNormalBundle.projection i') :=
    (PurityNormalBundle.over i').property
  exact specMap_zero f _ _ (PurityNormalBundle.projection i)
    (PurityNormalBundle.projection i') (normalAlgebraIso i) (normalAlgebraIso i') ν ρ hs
    (PurityNormalBundle.zeroSection i) (PurityNormalBundle.zeroSection i')
    (PurityNormalBundle.zeroSection_spec i).1 (PurityNormalBundle.zeroSection_spec i').1
    (fun V a ↦ (ConormalGradedAlgebra.augmentation i).right.hom.app (op V) a)
    (fun V a ↦ (ConormalGradedAlgebra.augmentation i').right.hom.app (op V) a)
    (normalZero_app i) (normalZero_app i') hε

private theorem conormalAdjointSection {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') (f : Z ⟶ Z')
    (h : i ≫ g = f ≫ i') (M : X.Modules) (M' : X'.Modules)
    (γ : (tensorPullback g).obj M' ⟶ M)
    (d : (tensorPullback f).obj ((tensorPullback i').obj M') ⟶ (tensorPullback i).obj M)
    (hc : ((exists_tensorPullbackAdjunction i').choose.unit.app M') ≫
      (pushforward i').map (((exists_tensorPullbackAdjunction f).choose.unit.app
        ((tensorPullback i').obj M')) ≫ (pushforward f).map d) ≫
      (pushforwardComp f i').hom.app ((tensorPullback i).obj M) ≫
      (pushforwardCongr h.symm).hom.app ((tensorPullback i).obj M) =
      (exists_tensorPullbackAdjunction g).choose.unit.app M' ≫
      (pushforward g).map (γ ≫ (exists_tensorPullbackAdjunction i).choose.unit.app M) ≫
      (pushforwardComp i g).hom.app ((tensorPullback i).obj M))
    (T : X'.Opens) (a : M'.val.obj (op T)) :
    ((tensorPullback i).obj M).presheaf.map
      (eqToHom (congrArg (fun k : Z ⟶ X' ↦ k ⁻¹ᵁ T) h)).op
      (pullbackSection f _ _ d (i' ⁻¹ᵁ T)
        (((exists_tensorPullbackAdjunction i').choose.unit.app M').app T a)) =
      ((exists_tensorPullbackAdjunction i).choose.unit.app M).app (g ⁻¹ᵁ T)
        (γ.app (g ⁻¹ᵁ T)
          (((exists_tensorPullbackAdjunction g).choose.unit.app M').app T a)) := by
  have ht := congrArg (fun k ↦ k.app T a) hc
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem conormalRepresentative {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (d : (tensorPullback f).obj (ConormalGradedAlgebra.piece i' 1) ⟶
      ConormalGradedAlgebra.piece i 1)
    (hd : d = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2))
    (T : X'.Opens) (a : (ConormalGradedAlgebra.power i' 1).val.obj (op T)) :
    ∃ b : (ConormalGradedAlgebra.power i 1).val.obj (op (g ⁻¹ᵁ T)),
      (ConormalGradedAlgebra.powerInclusion i 1).app (g ⁻¹ᵁ T) b =
        g.app T ((ConormalGradedAlgebra.powerInclusion i' 1).app T a) ∧
      (ConormalGradedAlgebra.piece i 1).presheaf.map
        (eqToHom (congrArg (fun k : Z ⟶ X' ↦ k ⁻¹ᵁ T) h)).op
        (pullbackSection f _ _ d (i' ⁻¹ᵁ T)
          (ConormalGradedAlgebra.representative i' 1 T a)) =
        ConormalGradedAlgebra.representative i 1 (g ⁻¹ᵁ T) b := by
  let γ := Classical.choose (closedImmersion_conormal_functorial i i' g f h).2
  have hγ := (Classical.choose_spec (closedImmersion_conormal_functorial i i' g f h).2).1
  have hc := (Classical.choose_spec ((Classical.choose_spec
    (closedImmersion_conormal_functorial i i' g f h).2).2)).1.1
  rw [hd]
  let adjg := Classical.choose (exists_tensorPullbackAdjunction g)
  let adji := Classical.choose (exists_tensorPullbackAdjunction i)
  let b := γ.app (g ⁻¹ᵁ T) ((adjg.unit.app i'.ker.toModules).app T a)
  refine ⟨b, hγ T a, ?_⟩
  exact conormalAdjointSection i i' g f h i.ker.toModules i'.ker.toModules γ _ hc T a

set_option backward.isDefEq.respectTransparency false in
private theorem differenceRepresentative {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (V : X.Opens) (a : Γ(X, V)) :
    ∃ s : (ConormalGradedAlgebra.power (pullback.diagonal f) 1).val.obj
        (op ((pullback.fst f f) ⁻¹ᵁ V ⊓ (pullback.snd f f) ⁻¹ᵁ V)),
      (ConormalGradedAlgebra.powerInclusion (pullback.diagonal f) 1).app _ s =
        (pullback.snd f f).appLE V _ inf_le_right a -
        (pullback.fst f f).appLE V _ inf_le_left a := by
  let T := (pullback.fst f f) ⁻¹ᵁ V ⊓ (pullback.snd f f) ⁻¹ᵁ V
  let δ := pullback.diagonal f
  let φ := SheafOfModules.unitToPushforwardObjUnit δ.toRingCatSheafHom
  let b := (pullback.snd f f).appLE V T inf_le_right a -
    (pullback.fst f f).appLE V T inf_le_left a
  have hb : (SheafOfModules.evaluation (pullback f f).ringCatSheaf (op T)).map φ b = 0 := by
    change δ.app T b = 0
    dsimp only [b]
    rw [map_sub]
    have hsnd : (pullback.snd f f).appLE V T inf_le_right ≫ δ.app T =
        (pullback.fst f f).appLE V T inf_le_left ≫ δ.app T := by
      rw [δ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        Scheme.Hom.appLE_comp_appLE]
      simp [δ]
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hsnd a)
  have hb' : b ∈ Set.range
      ((SheafOfModules.evaluation (pullback f f).ringCatSheaf (op T)).map (kernel.ι φ)) := by
    rw [Scheme.Modules.range_map_kernelι]
    exact hb
  obtain ⟨b', hb'⟩ := hb'
  obtain ⟨k, hk⟩ := idealKernelIso δ
  refine ⟨k.inv.app T b', ?_⟩
  have hki : k.inv ≫ δ.ker.toModulesι = kernel.ι φ := by
    rw [← hk, Iso.inv_hom_id_assoc]
  exact (congrArg (fun q ↦ q.app T b') hki).trans hb'

-- Restrict the canonical conormal map to the open where a difference is defined.
private theorem conormalRepresentativeLocal {X Z X' Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (d : (tensorPullback f).obj (ConormalGradedAlgebra.piece i' 1) ⟶
      ConormalGradedAlgebra.piece i 1)
    (hd : d = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2))
    (T : X'.Opens) (a : (ConormalGradedAlgebra.power i' 1).val.obj (op T))
    (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ (g ⁻¹ᵁ T))
    (hW' : W ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ T)) :
    ∃ b : (ConormalGradedAlgebra.power i 1).val.obj (op (g ⁻¹ᵁ T)),
      (ConormalGradedAlgebra.powerInclusion i 1).app (g ⁻¹ᵁ T) b =
        g.app T ((ConormalGradedAlgebra.powerInclusion i' 1).app T a) ∧
      (ConormalGradedAlgebra.piece i 1).presheaf.map (homOfLE hW').op
        (pullbackSection f _ _ d (i' ⁻¹ᵁ T)
          (ConormalGradedAlgebra.representative i' 1 T a)) =
      (ConormalGradedAlgebra.piece i 1).presheaf.map (homOfLE hW).op
        (ConormalGradedAlgebra.representative i 1 (g ⁻¹ᵁ T) b) := by
  obtain ⟨b, hb, he⟩ := conormalRepresentative i i' g f h d hd T a
  refine ⟨b, hb, ?_⟩
  rw [← he]
  change _ = ((ConormalGradedAlgebra.piece i 1).presheaf.map _ ≫
    (ConormalGradedAlgebra.piece i 1).presheaf.map _) _
  erw [← Functor.map_comp]
  congr 1

private theorem pullbackSection_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : X.Modules} {N : Y.Modules} (c : (tensorPullback f).obj N ⟶ M)
    {V W : Y.Opens} (h : V ≤ W) (a : N.val.obj (op W)) :
    pullbackSection f _ _ c V (N.presheaf.map (homOfLE h).op a) =
      M.presheaf.map (homOfLE (f.preimage_mono h)).op
        (pullbackSection f _ _ c W a) := by
  exact Hom.app_presheaf_map
    ((Classical.choose (exists_tensorPullbackAdjunction f)).homEquiv N M c)
    (homOfLE h) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem representative_eq_of_inclusion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {T T' : X.Opens} (h : T = T')
    (a : (ConormalGradedAlgebra.power i 1).val.obj (op T))
    (b : (ConormalGradedAlgebra.power i 1).val.obj (op T'))
    (he : X.presheaf.map (eqToHom h).op
      ((ConormalGradedAlgebra.powerInclusion i 1).app T' b) =
      (ConormalGradedAlgebra.powerInclusion i 1).app T a)
    (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ T) (hV' : V ≤ i ⁻¹ᵁ T') :
    (ConormalGradedAlgebra.piece i 1).presheaf.map (homOfLE hV).op
      (ConormalGradedAlgebra.representative i 1 T a) =
    (ConormalGradedAlgebra.piece i 1).presheaf.map (homOfLE hV').op
      (ConormalGradedAlgebra.representative i 1 T' b) := by
  subst T'
  have hab : b = a := by
    apply i.ker.injective_toModulesι_app T
    have ht : (ConormalGradedAlgebra.powerInclusion i 1).app T b =
        (ConormalGradedAlgebra.powerInclusion i 1).app T a := by
      simpa only [eqToHom_refl, op_id, X.presheaf.map_id,
        ConcreteCategory.id_apply] using he
    exact ht
  subst b
  rfl

-- Pullback of a difference is the difference of the two pulled-back sections.
private theorem appLE_difference {A U X Y O : Scheme.{u}} (e : U ⟶ A)
    (a₁ a₂ : X ⟶ A) (u₁ u₂ : Y ⟶ U) (q : O ⟶ X) (i : O ⟶ Y)
    (h₁ : i ≫ u₁ ≫ e = q ≫ a₁) (h₂ : i ≫ u₂ ≫ e = q ≫ a₂)
    (V : A.Opens) (T : X.Opens) (W : Y.Opens)
    (hT₁ : T ≤ a₁ ⁻¹ᵁ V) (hT₂ : T ≤ a₂ ⁻¹ᵁ V)
    (hW₁ : W ≤ u₁ ⁻¹ᵁ (e ⁻¹ᵁ V)) (hW₂ : W ≤ u₂ ⁻¹ᵁ (e ⁻¹ᵁ V))
    (hW : i ⁻¹ᵁ W = q ⁻¹ᵁ T) (a : Γ(A, V)) :
    q.appLE T (i ⁻¹ᵁ W) hW.le (a₂.appLE V T hT₂ a - a₁.appLE V T hT₁ a) =
      i.app W (u₂.appLE (e ⁻¹ᵁ V) W hW₂ (e.app V a) -
        u₁.appLE (e ⁻¹ᵁ V) W hW₁ (e.app V a)) := by
  rw [map_sub, map_sub]
  congr 1
  · change (a₂.appLE _ _ _ ≫ q.appLE _ _ _) a =
      (e.app V ≫ u₂.appLE _ _ _ ≫ i.app W) a
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact ConcreteCategory.congr_hom (appLE_eq_of_eq h₂.symm V (i ⁻¹ᵁ W) _ _) a
  · change (a₁.appLE _ _ _ ≫ q.appLE _ _ _) a =
      (e.app V ≫ u₁.appLE _ _ _ ≫ i.app W) a
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact ConcreteCategory.congr_hom (appLE_eq_of_eq h₁.symm V (i ⁻¹ᵁ W) _ _) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gradedDifference {U A Y : Scheme.{u}} (p : A ⟶ Y) (e : U ⟶ A)
    [IsSeparated p] [IsSeparated (e ≫ p)]
    (O : (pullback (e ≫ p) (e ≫ p)).Opens) (δ : U ⟶ O.toScheme)
    [IsClosedImmersion δ] (hδ : δ ≫ O.ι = pullback.diagonal (e ≫ p))
    (q : O.toScheme ⟶ pullback p p)
    (hq : q = O.ι ≫ pullback.map (e ≫ p) (e ≫ p) p p e e (𝟙 Y) (by simp) (by simp))
    (hsq : δ ≫ q = e ≫ pullback.diagonal p)
    (hsqR : δ ≫ O.ι = (𝟙 U) ≫ pullback.diagonal (e ≫ p))
    (c : (tensorPullback e).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra.toModule ⟶
      (ConormalGradedAlgebra.presentation δ).algebra.toModule)
    (hc : ConormalGradedAlgebra.IsBaseChangeMap δ (pullback.diagonal p) q e hsq
      (ConormalGradedAlgebra.presentation δ)
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)) c)
    (cR : (tensorPullback (𝟙 U)).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).algebra.toModule ⟶
      (ConormalGradedAlgebra.presentation δ).algebra.toModule)
    (hcR : ConormalGradedAlgebra.IsBaseChangeMap δ (pullback.diagonal (e ≫ p)) O.ι (𝟙 U)
      hsqR (ConormalGradedAlgebra.presentation δ)
      (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))) cR)
    (ωA : p.relativeDifferentials ≅ ConormalGradedAlgebra.piece (pullback.diagonal p) 1)
    (hdA : IsDifferenceIdentification p (pullback.diagonal p)
      (pullback.fst p p) (pullback.snd p p) ωA)
    (ωU : (e ≫ p).relativeDifferentials ≅
      ConormalGradedAlgebra.piece (pullback.diagonal (e ≫ p)) 1)
    (hdU : IsDifferenceIdentification (e ≫ p) (pullback.diagonal (e ≫ p))
      (pullback.fst (e ≫ p) (e ≫ p)) (pullback.snd (e ≫ p) (e ≫ p)) ωU) :
    ∀ (V : A.Opens) (a : Γ(A, V)),
      pullbackSection e _ _ c V
        (((ConormalGradedAlgebra.presentation (pullback.diagonal p)).inclusion 1).app V
          (ωA.hom.app V (p.relativeDifferentialsDerivation.d a))) =
      pullbackSection (𝟙 U) _ _ cR (e ⁻¹ᵁ V)
        (((ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).inclusion 1).app
          (e ⁻¹ᵁ V) (ωU.hom.app (e ⁻¹ᵁ V)
            ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a)))) := by
  let d := hc.choose_spec.choose
  have hgr := hc.choose_spec.choose_spec.2.2.1
  have h1 := hc.choose_spec.choose_spec.2.2.2.2.2
  let dR := hcR.choose_spec.choose
  have hgrR := hcR.choose_spec.choose_spec.2.2.1
  have h1R := hcR.choose_spec.choose_spec.2.2.2.2.2
  intro V a
  let T := (pullback.fst p p) ⁻¹ᵁ V ⊓ (pullback.snd p p) ⁻¹ᵁ V
  let W := (pullback.fst (e ≫ p) (e ≫ p)) ⁻¹ᵁ (e ⁻¹ᵁ V) ⊓
    (pullback.snd (e ≫ p) (e ≫ p)) ⁻¹ᵁ (e ⁻¹ᵁ V)
  have hV : V ≤ (pullback.diagonal p) ⁻¹ᵁ T := by
    simp only [T, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem, le_refl]
  have hU : e ⁻¹ᵁ V ≤ (pullback.diagonal (e ≫ p)) ⁻¹ᵁ W := by
    simp only [W, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc, inf_idem, le_refl]
  have hW : O.ι ⁻¹ᵁ W = q ⁻¹ᵁ T := by
    rw [hq, Scheme.Hom.comp_preimage]
    congr 1
    simp only [T, W, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullback.lift_fst, pullback.lift_snd]
  have hδT : e ⁻¹ᵁ V ≤ δ ⁻¹ᵁ (q ⁻¹ᵁ T) := by
    rw [← Scheme.Hom.comp_preimage, hsq, Scheme.Hom.comp_preimage]
    exact e.preimage_mono hV
  have hδW : e ⁻¹ᵁ V ≤ δ ⁻¹ᵁ (O.ι ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hδ]
    exact hU
  obtain ⟨sA, hsA⟩ := differenceRepresentative p V a
  obtain ⟨sU, hsU⟩ := differenceRepresentative (e ≫ p) (e ⁻¹ᵁ V) (e.app V a)
  obtain ⟨bA, hbA, hcA⟩ := conormalRepresentativeLocal δ (pullback.diagonal p) q e hsq
    (d 1) h1 T sA (e ⁻¹ᵁ V) hδT (e.preimage_mono hV)
  obtain ⟨bU, hbU, hcU⟩ := conormalRepresentativeLocal δ (pullback.diagonal (e ≫ p))
    O.ι (𝟙 U) hsqR (dR 1) h1R W sU (e ⁻¹ᵁ V) hδW hU
  have hclasses :
      (ConormalGradedAlgebra.piece δ 1).presheaf.map (homOfLE hδT).op
        (ConormalGradedAlgebra.representative δ 1 (q ⁻¹ᵁ T) bA) =
      (ConormalGradedAlgebra.piece δ 1).presheaf.map (homOfLE hδW).op
        (ConormalGradedAlgebra.representative δ 1 (O.ι ⁻¹ᵁ W) bU) := by
    apply (representative_eq_of_inclusion δ hW bU bA ?_
      (e ⁻¹ᵁ V) hδW hδT).symm
    rw [hbA, hbU, hsA, hsU]
    change (q.appLE T (O.ι ⁻¹ᵁ W) hW.le) _ = _
    exact appLE_difference e (pullback.fst p p) (pullback.snd p p)
      (pullback.fst (e ≫ p) (e ≫ p)) (pullback.snd (e ≫ p) (e ≫ p)) q O.ι
      (by simp only [hq, Category.assoc, pullback.lift_fst])
      (by simp only [hq, Category.assoc, pullback.lift_snd]) V T W
      inf_le_left inf_le_right inf_le_left inf_le_right hW a
  rw [gradedSection e _ _ c (d 1) (hgr 1),
    gradedSection (𝟙 U) _ _ cR (dR 1) (hgrR 1)]
  apply congrArg (((ConormalGradedAlgebra.presentation δ).inclusion 1).app (e ⁻¹ᵁ V))
  erw [hdA V T inf_le_left inf_le_right hV a sA hsA,
    hdU (e ⁻¹ᵁ V) W inf_le_left inf_le_right hU (e.app V a) sU hsU,
    pullbackSection_naturality, pullbackSection_naturality, hcA, hcU]
  exact hclasses

-- Transport a section identity along three isomorphisms over the two bases.
private theorem conjugate_app {U A N NU NA TU TA : Scheme.{u}}
    (e : U ⟶ A) (π : N ⟶ U) (πU : NU ⟶ U) (πA : NA ⟶ A)
    (τU : TU ⟶ U) (τA : TA ⟶ A) (r : N ≅ NU) (tU : NU ≅ TU) (tA : NA ≅ TA)
    (ν : N ⟶ NA) (hr : r.hom ≫ πU = π)
    (htU : tU.hom ≫ τU = πU) (htA : tA.hom ≫ τA = πA)
    (hν : ν ≫ πA = π ≫ e) (V : A.Opens)
    (x : Γ(TA, τA ⁻¹ᵁ V)) (y : Γ(TU, τU ⁻¹ᵁ (e ⁻¹ᵁ V)))
    (xA : Γ(NA, πA ⁻¹ᵁ V)) (xU : Γ(NU, πU ⁻¹ᵁ (e ⁻¹ᵁ V)))
    (hA : tA.hom.appLE (τA ⁻¹ᵁ V) (πA ⁻¹ᵁ V)
      (congrArg (fun f ↦ f ⁻¹ᵁ V) htA).symm.le x = xA)
    (hU : tU.hom.appLE (τU ⁻¹ᵁ (e ⁻¹ᵁ V)) (πU ⁻¹ᵁ (e ⁻¹ᵁ V))
      (congrArg (fun f ↦ f ⁻¹ᵁ (e ⁻¹ᵁ V)) htU).symm.le y = xU)
    (hclass : ν.appLE (πA ⁻¹ᵁ V) (π ⁻¹ᵁ (e ⁻¹ᵁ V))
        (congrArg (fun f ↦ f ⁻¹ᵁ V) hν).symm.le xA =
      r.hom.appLE (πU ⁻¹ᵁ (e ⁻¹ᵁ V)) (π ⁻¹ᵁ (e ⁻¹ᵁ V))
        (congrArg (fun f ↦ f ⁻¹ᵁ (e ⁻¹ᵁ V)) hr).symm.le xU) :
    ∃ he : (tU.inv ≫ r.inv ≫ ν ≫ tA.hom) ≫ τA = τU ≫ e,
      (tU.inv ≫ r.inv ≫ ν ≫ tA.hom).appLE (τA ⁻¹ᵁ V) (τU ⁻¹ᵁ (e ⁻¹ᵁ V))
        (congrArg (fun f ↦ f ⁻¹ᵁ V) he).symm.le x = y := by
  let s := r ≪≫ tU
  let de := tU.inv ≫ r.inv ≫ ν ≫ tA.hom
  have hs : s.hom ≫ τU = π := by
    change r.hom ≫ tU.hom ≫ _ = _
    rw [htU]
    simpa using hr
  have hsd : s.hom ≫ de = ν ≫ tA.hom := by simp [s, de]
  have he : de ≫ τA = τU ≫ e := by
    apply (cancel_epi s.hom).mp
    rw [← Category.assoc, hsd, Category.assoc, htA, hν, ← Category.assoc, hs]
  let W := e ⁻¹ᵁ V
  have hW : π ⁻¹ᵁ W =
      s.hom ⁻¹ᵁ (τU ⁻¹ᵁ W) := by
    exact (congrArg (fun f : N ⟶ U ↦
      f ⁻¹ᵁ W) hs).symm
  let k := s.hom.appLE (τU ⁻¹ᵁ W)
    (π ⁻¹ᵁ W) hW.le
  have : IsIso k := by
    unfold k Scheme.Hom.appLE
    have : IsIso (homOfLE hW.le) := homOfLE_isIso_of_eq _ hW
    infer_instance
  refine ⟨he, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso k).injective
  have htAi : πA ⁻¹ᵁ V ≤
      tA.hom ⁻¹ᵁ (τA ⁻¹ᵁ V) := by
    exact (congrArg (fun f ↦ f ⁻¹ᵁ V) htA).symm.le
  have hνi : π ⁻¹ᵁ W ≤
      ν ⁻¹ᵁ (πA ⁻¹ᵁ V) := by
    exact (congrArg (fun f ↦ f ⁻¹ᵁ V) hν).symm.le
  have htUi : πU ⁻¹ᵁ W ≤
      tU.hom ⁻¹ᵁ (τU ⁻¹ᵁ W) := by
    exact (congrArg (fun f ↦ f ⁻¹ᵁ W) htU).symm.le
  have hri : π ⁻¹ᵁ W ≤
      r.hom ⁻¹ᵁ (πU ⁻¹ᵁ W) := by
    exact (congrArg (fun f ↦ f ⁻¹ᵁ W) hr).symm.le
  have hleft : de.appLE (τA ⁻¹ᵁ V)
        (τU ⁻¹ᵁ W)
        (congrArg (fun f ↦ f ⁻¹ᵁ V) he).symm.le ≫ k =
      tA.hom.appLE (τA ⁻¹ᵁ V)
        (πA ⁻¹ᵁ V) htAi ≫
      ν.appLE (πA ⁻¹ᵁ V)
        (π ⁻¹ᵁ W) hνi := by
    dsimp only [k]
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq hsd _ _ _ _
  have hright : k =
      tU.hom.appLE (τU ⁻¹ᵁ W)
        (πU ⁻¹ᵁ W) htUi ≫
      r.hom.appLE (πU ⁻¹ᵁ W)
        (π ⁻¹ᵁ W) hri := by
    dsimp only [k]
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  change (de.appLE _ _ _ ≫ k) _ = k _
  erw [hleft, hright]
  change ν.appLE _ _ _ (tA.hom.appLE _ _ _ _) =
    r.hom.appLE _ _ _ (tU.hom.appLE _ _ _ _)
  erw [hA, hU]
  exact hclass

private theorem normalProjection_affine {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : IsAffineHom (PurityNormalBundle.projection i) :=
  (PurityNormalBundle.over i).property

attribute [local irreducible] PurityNormalBundle.normalCone RelativeTangentBundle.scheme
  normalAlgebraIso RelativeTangentBundle.algebraIso PurityNormalBundle.zeroSection
  RelativeTangentBundle.zeroSection VectorBundleZeroSection.antiEquivalence
  PurityNormalBundle.over RelativeTangentBundle.over

-- The two normalized spectrum formulas transport the generator calculation.
set_option backward.isDefEq.respectTransparency true in
private theorem differentialFromNormal {U A Y M : Scheme.{u}}
    (p : A ⟶ Y) (e : U ⟶ A) [Smooth p] [Smooth (e ≫ p)]
    [IsSeparated p] [IsSeparated (e ≫ p)]
    (δ : U ⟶ M) [IsClosedImmersion δ]
    (c : (tensorPullback e).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra.toModule ⟶
      (ConormalGradedAlgebra.presentation δ).algebra.toModule)
    (cR : (tensorPullback (𝟙 U)).obj
      (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).algebra.toModule ⟶
      (ConormalGradedAlgebra.presentation δ).algebra.toModule)
    (r : PurityNormalBundle.normalCone δ ≅
      PurityNormalBundle.normalCone (pullback.diagonal (e ≫ p)))
    (hr : IsSpecMap (𝟙 U) (ConormalGradedAlgebra.presentation δ).algebra
      (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).algebra
      (PurityNormalBundle.projection δ)
      (PurityNormalBundle.projection (pullback.diagonal (e ≫ p)))
      (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal (e ≫ p))) r.hom
      (pullbackSection (𝟙 U) _ _ cR))
    (ν : PurityNormalBundle.normalCone δ ⟶
      PurityNormalBundle.normalCone (pullback.diagonal p))
    (hν : IsSpecMap e (ConormalGradedAlgebra.presentation δ).algebra
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra
      (PurityNormalBundle.projection δ)
      (PurityNormalBundle.projection (pullback.diagonal p))
      (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal p)) ν
      (pullbackSection e _ _ c))
    (ωU : (e ≫ p).relativeDifferentials ≅
      ConormalGradedAlgebra.piece (pullback.diagonal (e ≫ p)) 1)
    (ωA : p.relativeDifferentials ≅ ConormalGradedAlgebra.piece (pullback.diagonal p) 1)
    (tU : PurityNormalBundle.normalCone (pullback.diagonal (e ≫ p)) ≅
      RelativeTangentBundle.scheme (e ≫ p))
    (htU : IsNormalTangentIdentification (e ≫ p) (pullback.diagonal (e ≫ p)) ωU tU)
    (tA : PurityNormalBundle.normalCone (pullback.diagonal p) ≅ RelativeTangentBundle.scheme p)
    (htA : IsNormalTangentIdentification p (pullback.diagonal p) ωA tA)
    (hgen : ∀ (V : A.Opens) (a : Γ(A, V)),
      pullbackSection e _ _ c V
        (((ConormalGradedAlgebra.presentation (pullback.diagonal p)).inclusion 1).app V
          (ωA.hom.app V (p.relativeDifferentialsDerivation.d a))) =
      pullbackSection (𝟙 U) _ _ cR (e ⁻¹ᵁ V)
        (((ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).inclusion 1).app
          (e ⁻¹ᵁ V) (ωU.hom.app (e ⁻¹ᵁ V)
            ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a))))) :
    IsDifferential p e (tU.inv ≫ r.inv ≫ ν ≫ tA.hom) := by
  have he : (tU.inv ≫ r.inv ≫ ν ≫ tA.hom) ≫ RelativeTangentBundle.projection p =
      RelativeTangentBundle.projection (e ≫ p) ≫ e := by
    calc
      _ = tU.inv ≫ r.inv ≫ PurityNormalBundle.projection δ ≫ e := by
        simp only [Category.assoc]
        rw [htA.1, hν.1]
      _ = RelativeTangentBundle.projection (e ≫ p) ≫ e := by
        have hrp := hr.1
        simp only [Category.comp_id] at hrp
        rw [← hrp]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← htU.1]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  refine ⟨he, ?_⟩
  intro V a
  let W := e ⁻¹ᵁ V
  obtain ⟨βU, hβU, htUspec⟩ := htU.2.2
  obtain ⟨βA, hβA, htAspec⟩ := htA.2.2
  have hA := htAspec.2 V
    ((SymmetricAlgebraSheaf.inclusion p.relativeDifferentials).app V
      (p.relativeDifferentialsDerivation.d a))
  have hAgen := congrArg
    ((normalAlgebraIso (pullback.diagonal p)).hom.right.hom.app (op V))
    (hβA V (p.relativeDifferentialsDerivation.d a))
  have hA := hAgen.symm.trans hA
  have hU := htUspec.2 W
    ((SymmetricAlgebraSheaf.inclusion (e ≫ p).relativeDifferentials).app W
      ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a)))
  have hUgen := congrArg
    ((normalAlgebraIso (pullback.diagonal (e ≫ p))).hom.right.hom.app (op W))
    (hβU W ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a)))
  have hU := hUgen.symm.trans hU
  have hc := hν.2 V
    (((ConormalGradedAlgebra.presentation (pullback.diagonal p)).inclusion 1).app V
      (ωA.hom.app V (p.relativeDifferentialsDerivation.d a)))
  have hcR := hr.2 W
    (((ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).inclusion 1).app W
      (ωU.hom.app W ((e ≫ p).relativeDifferentialsDerivation.d (e.app V a))))
  have hclass := hc.symm.trans
    ((congrArg ((normalAlgebraIso δ).hom.right.hom.app (op W))
      (hgen V a)).trans hcR)
  obtain ⟨_, hx⟩ := conjugate_app e
    (PurityNormalBundle.projection δ)
    (PurityNormalBundle.projection (pullback.diagonal (e ≫ p)))
    (PurityNormalBundle.projection (pullback.diagonal p))
    (RelativeTangentBundle.projection (e ≫ p)) (RelativeTangentBundle.projection p)
    r tU tA ν (by simpa using hr.1) htU.1 htA.1 hν.1 V _ _ _ _ hA.symm hU.symm hclass
  exact hx

attribute [local irreducible] SymmetricAlgebraSheaf.algebra ConormalGradedAlgebra.piece
  PurityNormalBundle.projection RelativeTangentBundle.projection

-- Keep the affine-space implementation out of the normal-comparison construction.
set_option backward.isDefEq.respectTransparency true in
private theorem comparisonOfChart {k : Type u} [Field k]
    {Y U A : Scheme.{u}} [IsAffine Y] [IsAffine A]
    [IsNoetherian Y] [IsNoetherian U] [IsNoetherian A]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (p : A ⟶ Y) (e : U ⟶ A) [Etale e]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [SmoothOfRelativeDimension d p] [Smooth p]
    [IsSeparated (e ≫ p)] [LocallyOfFiniteType (e ≫ p)] [QuasiCompact (e ≫ p)]
    [SmoothOfRelativeDimension d (e ≫ p)] [Smooth (e ≫ p)] :
    Nonempty (Comparison d p e) := by
  classical
  obtain ⟨O, δ, hO, hδ, hcart, het, hclosed⟩ := chartGeometry p e
  have : IsClosedImmersion δ := hclosed
  generalize hq : (O.ι ≫ pullback.map (e ≫ p) (e ≫ p) p p e e (𝟙 Y)
    (by simp) (by simp)) = q at hcart het
  have : Etale q := het
  have hsq := hcart.w
  obtain ⟨regU, codimU⟩ := diagonalRegular aY (e ≫ p) d
  obtain ⟨regA, codimA⟩ := diagonalRegular aY p d
  obtain ⟨_, ⟨c₀, hc₀, _⟩, hciso⟩ := ConormalGradedAlgebra.existsUnique_baseChangeMap
    δ (pullback.diagonal p) q e hsq hcart.isLimit
      (ConormalGradedAlgebra.presentation δ)
      (ConormalGradedAlgebra.presentation (pullback.diagonal p))
  have : IsIso c₀ := (hciso c₀ hc₀).2 inferInstance
  let c := asIso c₀
  have hrsq : δ ≫ O.ι = (𝟙 U) ≫ pullback.diagonal (e ≫ p) := by simpa using hδ
  have hrcart : IsPullback δ (𝟙 U) O.ι (pullback.diagonal (e ≫ p)) := by
    apply IsOpenImmersion.isPullback
    · exact hrsq.symm
    · rw [Scheme.Opens.opensRange_ι]
      change (pullback.diagonal (e ≫ p)) ⁻¹ᵁ O = (𝟙 U : U ⟶ U).opensRange
      rw [← hδ, Scheme.Hom.comp_preimage]
      ext x
      simp
  obtain ⟨_, ⟨cR, hcR, _⟩, hcRiso⟩ := ConormalGradedAlgebra.existsUnique_baseChangeMap
    δ (pullback.diagonal (e ≫ p)) O.ι (𝟙 U) hrsq hrcart.isLimit
      (ConormalGradedAlgebra.presentation δ)
      (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p)))
  have : IsIso cR := (hcRiso cR hcR).2 inferInstance
  have hcRkeep := hcR
  let ρR := hcR.choose
  let dR := hcR.choose_spec.choose
  have hρR := hcR.choose_spec.choose_spec.1
  have hsecR := hcR.choose_spec.choose_spec.2.1
  have hgrR := hcR.choose_spec.choose_spec.2.2.1
  have : IsAffineHom (PurityNormalBundle.projection δ) := normalProjection_affine δ
  have : IsAffineHom (PurityNormalBundle.projection (pullback.diagonal (e ≫ p))) :=
    normalProjection_affine (pullback.diagonal (e ≫ p))
  have : IsAffineHom (PurityNormalBundle.projection (pullback.diagonal p)) :=
    normalProjection_affine (pullback.diagonal p)
  obtain ⟨r, hr⟩ := identitySpecMap
    (ConormalGradedAlgebra.presentation δ).algebra
    (ConormalGradedAlgebra.presentation (pullback.diagonal (e ≫ p))).algebra
    (PurityNormalBundle.projection δ)
    (PurityNormalBundle.projection (pullback.diagonal (e ≫ p)))
    (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal (e ≫ p)))
    (asIso cR) ρR hρR hsecR
  have hcKeep := hc₀
  let ρ := hc₀.choose
  let dc := hc₀.choose_spec.choose
  have hρ := hc₀.choose_spec.choose_spec.1
  have hsec := hc₀.choose_spec.choose_spec.2.1
  have hgr := hc₀.choose_spec.choose_spec.2.2.1
  have : (ConormalGradedAlgebra.presentation
      (pullback.diagonal p)).algebra.toModule.IsQuasicoherent :=
    (ConormalGradedAlgebra.presentation (pullback.diagonal p)).quasicoherent
  obtain ⟨ν, hν⟩ := specMap_exists e
    (ConormalGradedAlgebra.presentation δ).algebra
    (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra
    (PurityNormalBundle.projection δ) (PurityNormalBundle.projection (pullback.diagonal p))
    (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal p)) ρ hρ
  have hνspec : IsSpecMap e (ConormalGradedAlgebra.presentation δ).algebra
      (ConormalGradedAlgebra.presentation (pullback.diagonal p)).algebra
      (PurityNormalBundle.projection δ)
      (PurityNormalBundle.projection (pullback.diagonal p))
      (normalAlgebraIso δ) (normalAlgebraIso (pullback.diagonal p)) ν
      (pullbackSection e _ _ c.hom) := by
    refine ⟨hν.1, ?_⟩
    intro V a
    exact (congrArg ((normalAlgebraIso δ).hom.right.hom.app (op (e ⁻¹ᵁ V)))
      (hsec V a)).trans (hν.2 V a)
  have hνcart := specMap_cartesian e _ _ _ _ (normalAlgebraIso δ)
    (normalAlgebraIso (pullback.diagonal p)) c ν hνspec
  obtain ⟨ωU, hdU⟩ := differenceIdentification (e ≫ p)
  obtain ⟨ωA, hdA⟩ := differenceIdentification p
  have rankU : (ConormalGradedAlgebra.piece
      (pullback.diagonal (e ≫ p)) 1).IsFiniteLocallyFreeOfRank d :=
    (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials (e ≫ p) d).of_iso ωU
  have rankA : (ConormalGradedAlgebra.piece
      (pullback.diagonal p) 1).IsFiniteLocallyFreeOfRank d :=
    (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials p d).of_iso ωA
  have := diagonalSymmetric d (e ≫ p)
  have := diagonalSymmetric d p
  obtain ⟨tU, htU⟩ := normalTangentIdentification (e ≫ p)
    (pullback.diagonal (e ≫ p)) ωU
  obtain ⟨tA, htA⟩ := normalTangentIdentification p (pullback.diagonal p) ωA
  refine ⟨{
    O := O
    open_set := hO
    δ := δ
    diagonal_factorization := hδ
    q := q
    q_eq := hq.symm
    square := hsq
    cartesian := hcart.isLimit
    etale := het
    regular_U := regU
    codimension_U := codimU
    regular_A := regA
    codimension_A := codimA
    c := c
    graded_comparison := hcKeep
    restriction_square := hrsq
    restriction := asIso cR
    graded_restriction := hcRkeep
    r := r
    restriction_spec := hr
    ν := ν
    normal_spec := hνspec
    normal_cartesian := hνcart
    zero_section := normalMap_zero δ (pullback.diagonal p) e ν
      (fun V a ↦ ρ.hom.app (op V) a) hν
      (gradedAugmentation δ (pullback.diagonal p) e c₀ (dc 1) ρ hρ hsec (hgr 1))
    restriction_zero := by
      simpa only [Category.id_comp] using normalMap_zero δ (pullback.diagonal (e ≫ p)) (𝟙 U) r.hom
        (pullbackSection (𝟙 U) _ _ cR) hr
        (by
          intro V a
          exact (congrArg
            ((ConormalGradedAlgebra.augmentation δ).right.hom.app (op V))
            (hsecR V a)).trans
              (gradedAugmentation δ (pullback.diagonal (e ≫ p)) (𝟙 U) cR
                (dR 1) ρR hρR hsecR (hgrR 1) V a))
    ωU := ωU
    difference_U := hdU
    ωA := ωA
    difference_A := hdA
    rank_U := rankU
    rank_A := rankA
    tU := tU
    tangent_U := htU
    tA := tA
    tangent_A := htA
    de := tU.inv ≫ r.inv ≫ ν ≫ tA.hom
    differential := differentialFromNormal p e δ c₀ cR r hr ν hνspec ωU ωA tU htU tA htA
      (gradedDifference p e O δ hδ q hq.symm hsq hrsq c₀ hcKeep cR hcRkeep ωA hdA ωU hdU)
    differential_cartesian := by
      apply hνcart.of_iso (r ≪≫ tU) tA (Iso.refl U) (Iso.refl A)
      · simp
      · have hrt := hr.1
        have htt := htU.1
        change PurityNormalBundle.projection δ ≫ 𝟙 U =
          r.hom ≫ tU.hom ≫ RelativeTangentBundle.projection (e ≫ p)
        rw [Category.comp_id, htt]
        exact (hrt.trans (Category.comp_id _)).symm
      · change PurityNormalBundle.projection (pullback.diagonal p) ≫ 𝟙 A =
          tA.hom ≫ RelativeTangentBundle.projection p
        exact (Category.comp_id _).trans htA.1.symm
      · exact Category.comp_id e
    normal_is_differential := by simp
  }⟩

set_option backward.isDefEq.respectTransparency true in
/-- The actual graded and normal comparisons for an etale affine coordinate chart,
including dimension zero and the empty source.
Source: current blueprint sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md Step 2; Stacks 0633--0635, 0473, 08S2, 01LX
(blueprint: lem-pur-chart-normal-differential).

Proof:
1. lem-pur-chart-cartesian-domain, with source U and base open Y, gives exactly O,
   the restricted diagonal, the Cartesian square, and q etale, hence flat. The smooth
   diagonal calculation gives the two regular sequences and codimensions. For d=0
   the diagonals are open and closed and the stalk kernels are zero.
2. Apply lem-pur-conormal-algebra-flat-base-change to this square. Its unique actual
   graded comparison is invertible, has formula [a] tensor r -> [q-sharp(a) r], fixes
   degree zero, and in degree one is the canonical map of
   lem-weil-pbc-closed-immersion-conormal-flat-base-change.
3. Restriction to O preserves the diagonal ideal, its powers, quotient sheaves, and
   multiplication (lem-pur-conormal-graded-algebra). This gives the normalized graded
   restriction isomorphism, including its degree-one component.
4. Apply lem-weil-pbc-affine-morphism-relative-spec and
   lem-weil-pbc-relative-spec-base-change. Contravariance gives the specified normal
   maps, the restriction isomorphism, and the Cartesian normal square. Both graded maps
   commute with the degree-zero augmentations, hence preserve zero sections.
5. lem-sc-diagonal-conormal-derivation-exists and
   lem-sc-diagonal-conormal-affine-sections fix da as the class of p2*a-p1*a.
   lem-sc-smooth-proper-diagonal-conormal-differentials gives the conormal identifications.
   The representative formula sends this difference to the same difference of pulled-back
   sections. Thus the degree-one map sends da to d(e-sharp a). The universal property
   lem-weil-pbc-quasi-coherent-symmetric-algebra-core identifies the induced normal map
   with the actual differential under prose-09-15, not merely with some isomorphism.
6. No step selects a point of U or a coordinate. For empty U all comparisons are unique
   over the empty base; for d=0 the degree-one modules have rank zero, leaving the identity
   on scalars. The constructions and the augmentation identities apply in both cases. -/
theorem comparison (D : WeilConjectures.FiniteFieldDatum.{u})
    (_C : D.CoefficientDatum) (n : ℕ) (_hn : 1 ≤ n)
    {Y U : Scheme.{u}} [IsAffine Y]
    (aY : Y ⟶ Spec (CommRingCat.of D.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    [IsSeparated (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))]
    [LocallyOfFiniteType (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))]
    [QuasiCompact (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))]
    [SmoothOfRelativeDimension d (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))] :
    Nonempty (@Comparison U (AffineSpace (ULift.{u} (Fin d)) Y) Y d
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) e inferInstance inferInstance
      (SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin d)))
        (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
      (SmoothOfRelativeDimension.smooth d
        (e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)))) := by
  classical
  let A := AffineSpace (ULift.{u} (Fin d)) Y
  let p : A ⟶ Y := A ↘ Y
  have hcard : Nat.card (ULift.{u} (Fin d)) = d := by simp
  have : SmoothOfRelativeDimension d p := by
    simpa only [hcard] using (inferInstance : SmoothOfRelativeDimension
      (Nat.card (ULift.{u} (Fin d))) p)
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : Smooth (e ≫ p) := SmoothOfRelativeDimension.smooth d (e ≫ p)
  change Nonempty (Comparison d p e)
  have := LocallyOfFiniteType.isLocallyNoetherian aY
  have := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := {}
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian A := {}
  have := LocallyOfFiniteType.isLocallyNoetherian (e ≫ p)
  have := QuasiCompact.compactSpace_of_compactSpace (e ≫ p)
  have : IsNoetherian U := {}
  exact comparisonOfChart aY d p e

end AlgebraicGeometry.ChartNormalDifferential
