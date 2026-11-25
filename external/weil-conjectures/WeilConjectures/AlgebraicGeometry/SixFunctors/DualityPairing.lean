/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairingHelpers
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact

/-! # Evaluation and the ambient double-dual morphism

## Main definitions and statement

* `CategoryTheory.dualityDoubleFunctor`: the covariant double internal Hom.
* `CategoryTheory.DualityPairingCompatibility`: the naturality, shift and triangle clauses.
* `AlgebraicGeometry.Etale.AmbientDualityPairing` and
  `AlgebraicGeometry.ProEtale.AmbientDualityPairing`: the canonical evaluation and transpose,
  specified by the tensor-Hom adjunction and the descended Koszul symmetry.
* `AlgebraicGeometry.Etale.ambient_duality_pairing`: the evaluation pairing exists on the étale
  site (with the dualizing complex) and on the pro-étale site.

The tensor-Hom adjunction has left tensor as its left adjoint. Evaluation in the order
DK tensor K therefore includes the Koszul symmetry. Its adjunct, with left tensor DK,
is the double-dual morphism. All derived categories here are unbounded.

## Implementation details

The Koszul symmetry condition is named (`AlgebraicGeometry.Etale.IsEtaleKoszulSymmetry`) to keep
the large derived-monoidal instance out of the implicit predicate argument of
`Classical.choose`. The double-dual morphisms `bidualityMap` extract uniquely determined data:
the symmetry is fixed, evaluation is the adjunct of the identity and the arrow is its transpose.

## References

* Stacks Project, Tags 08J9, 08JA and 08JC
-/

@[expose] public section

set_option autoImplicit false

universe v u a c d w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Double application of the contravariant internal Hom into W. -/
def dualityDoubleFunctor {C : Type u} [Category.{v} C]
    (H : Cᵒᵖ ⥤ C ⥤ C) (W : C) : C ⥤ C :=
  (H.flip.obj W).rightOp ⋙ H.flip.obj W

/-- The compatibility assertions for the specified evaluation and its specified transpose.
This packages the conclusion, including the connecting square of triangles. The shift
isomorphisms include coherence for zero and addition, through Functor.CommShift. -/
def DualityPairingCompatibility {C : Type u} [Category.{v} C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (W : C)
    (e : ∀ K : C, (T.obj ((H.obj (op K)).obj W)).obj K ⟶ W)
    (δ : ∀ K : C, K ⟶ (dualityDoubleFunctor H W).obj K) : Prop :=
  (∀ (K L : C) (f : K ⟶ L),
    ((T.map ((H.map f.op).app W)).app K) ≫ e K =
      (T.obj ((H.obj (op L)).obj W)).map f ≫ e L) ∧
  (∀ (K L : C) (f : K ⟶ L),
    f ≫ δ L = δ K ≫ (dualityDoubleFunctor H W).map f) ∧
  ∃ s : (dualityDoubleFunctor H W).CommShift ℤ,
    (∀ (n : ℤ) (K : C),
      δ ((shiftFunctor C n).obj K) ≫ (s.commShiftIso n).hom.app K =
        (shiftFunctor C n).map (δ K)) ∧
    ∀ (U : Triangle C), U ∈ distTriang C →
      Triangle.mk ((dualityDoubleFunctor H W).map U.mor₁)
        ((dualityDoubleFunctor H W).map U.mor₂)
        ((dualityDoubleFunctor H W).map U.mor₃ ≫
          (s.commShiftIso (1 : ℤ)).hom.app U.obj₁) ∈ distTriang C ∧
      ∃ t : U ⟶ Triangle.mk ((dualityDoubleFunctor H W).map U.mor₁)
          ((dualityDoubleFunctor H W).map U.mor₂)
          ((dualityDoubleFunctor H W).map U.mor₃ ≫
            (s.commShiftIso (1 : ℤ)).hom.app U.obj₁),
        t.hom₁ = δ U.obj₁ ∧ t.hom₂ = δ U.obj₂ ∧ t.hom₃ = δ U.obj₃

private noncomputable def homSelfAdjunction
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : Cᵒᵖ ⥤ C ⥤ C) (a : curriedTensor C ⊣₂ H) (W : C) :
    (H.flip.obj W).rightOp ⊣ H.flip.obj W :=
  Adjunction.mkOfHomEquiv
    { homEquiv X M :=
        { toFun f := a.homEquiv ((β_ M.unop X).hom ≫ a.homEquiv.symm f.unop)
          invFun g := (a.homEquiv ((β_ M.unop X).inv ≫ a.homEquiv.symm g)).op
          left_inv f := by simp
          right_inv g := by simp }
      homEquiv_naturality_left_symm := by
        intro X X' M f g
        apply Quiver.Hom.unop_inj
        apply a.homEquiv.symm.injective
        dsimp only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Functor.rightOp_map,
          Functor.flip_obj_map]
        simp only [Quiver.Hom.unop_op, unop_comp]
        rw [a.homEquiv_symm_naturality_one, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply, a.homEquiv_symm_naturality_two]
        change (β_ M.unop X).inv ≫ M.unop ◁ f ≫ _ =
          f ▷ M.unop ≫ (β_ M.unop X').inv ≫ _
        rw [BraidedCategory.braiding_inv_naturality_left_assoc]
      homEquiv_naturality_right := by
        intro X M M' f g
        apply a.homEquiv.symm.injective
        dsimp only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Functor.rightOp_map,
          Functor.flip_obj_map]
        simp only [unop_comp]
        rw [Equiv.symm_apply_apply]
        change (β_ M'.unop X).hom ≫ a.homEquiv.symm (g.unop ≫ f.unop) =
          a.homEquiv.symm (a.homEquiv
            ((β_ M.unop X).hom ≫ a.homEquiv.symm f.unop) ≫
              (H.map g.unop.op).app W)
        rw [a.homEquiv_symm_naturality_one, Equiv.symm_apply_apply,
          a.homEquiv_symm_naturality_two]
        change (β_ M'.unop X).hom ≫ X ◁ g.unop ≫ _ =
          g.unop ▷ X ≫ (β_ M.unop X).hom ≫ _
        rw [BraidedCategory.braiding_naturality_left_assoc] }

set_option backward.isDefEq.respectTransparency false in
private theorem parametrizedPairing
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (H : Cᵒᵖ ⥤ C ⥤ C) (a : curriedTensor C ⊣₂ H) (W : C)
    (hs : ∃ s : (H.flip.obj W).CommShift ℤ, let := s
      (H.flip.obj W).IsTriangulated) :
    ∃ e : ∀ K : C, (H.obj (op K)).obj W ⊗ K ⟶ W,
      (∀ K : C, (a.adj K).homEquiv ((H.obj (op K)).obj W) W
        ((β_ K ((H.obj (op K)).obj W)).hom ≫ e K) = 𝟙 _) ∧
      ∃ δ : ∀ K : C, K ⟶ (dualityDoubleFunctor H W).obj K,
        (∀ K : C, δ K = (a.adj ((H.obj (op K)).obj W)).homEquiv K W (e K)) ∧
        DualityPairingCompatibility (curriedTensor C) H W e δ := by
  let ev (K : C) := (a.adj K).homEquiv _ W |>.symm (𝟙 _)
  let e (K : C) := (β_ K ((H.obj (op K)).obj W)).inv ≫ ev K
  have he : ∀ (K L : C) (f : K ⟶ L),
      ((curriedTensor C).map ((H.map f.op).app W)).app K ≫ e K =
        ((curriedTensor C).obj ((H.obj (op L)).obj W)).map f ≫ e L := by
    intro K L f
    change (H.map f.op).app W ▷ K ≫ e K = ((H.obj (op L)).obj W) ◁ f ≫ e L
    dsimp only [e]
    rw [BraidedCategory.braiding_inv_naturality_right_assoc,
      BraidedCategory.braiding_inv_naturality_left_assoc]
    congr 1
    apply a.homEquiv.injective
    change a.homEquiv (((curriedTensor C).obj K).map ((H.map f.op).app W) ≫ ev K) =
      a.homEquiv (((curriedTensor C).map f).app _ ≫ ev L)
    rw [a.homEquiv_naturality_two, a.homEquiv_naturality_one]
    simp only [ev, ParametrizedAdjunction.homEquiv_eq, Equiv.apply_symm_apply,
      Category.id_comp, Category.comp_id]
  refine ⟨e, ?_, ?_⟩
  · intro K
    dsimp only [e]
    rw [Iso.hom_inv_id_assoc]
    exact Equiv.apply_symm_apply _ _
  · obtain ⟨s, htri⟩ := hs
    let := s
    let := htri
    let := reverseBraiding C
    let adj := homSelfAdjunction H a W
    let := adj.leftAdjointCommShift ℤ
    let := adj.commShift_of_rightAdjoint ℤ
    let := adj.isTriangulated_leftAdjoint
    let : (dualityDoubleFunctor H W).CommShift ℤ := Functor.CommShift.comp _ _
    let : (dualityDoubleFunctor H W).IsTriangulated :=
      inferInstanceAs ((H.flip.obj W).rightOp ⋙ H.flip.obj W).IsTriangulated
    refine ⟨adj.unit.app, ?_, ?_, ?_, inferInstance, ?_, ?_⟩
    · intro K
      rfl
    · exact he
    · intro K L f
      exact adj.unit.naturality f
    · intro n K
      have h := (NatTrans.shift_app_comm adj.unit n K).symm
      simp only [Functor.commShiftIso_id_hom_app, Functor.id_obj] at h
      exact h.trans (Category.id_comp _)
    · intro U hU
      refine ⟨(dualityDoubleFunctor H W).map_distinguished U hU, ?_⟩
      refine ⟨Triangle.homMk _ _ (adj.unit.app U.obj₁) (adj.unit.app U.obj₂)
        (adj.unit.app U.obj₃) ?_ ?_ ?_, rfl, rfl, rfl⟩
      · exact adj.unit.naturality U.mor₁
      · exact adj.unit.naturality U.mor₂
      · symm
        change adj.unit.app U.obj₃ ≫ ((dualityDoubleFunctor H W).map U.mor₃ ≫ _) =
          U.mor₃ ≫ (adj.unit.app U.obj₁)⟦(1 : ℤ)⟧'
        have hn : U.mor₃ ≫ adj.unit.app (U.obj₁⟦(1 : ℤ)⟧) =
            adj.unit.app U.obj₃ ≫ (dualityDoubleFunctor H W).map U.mor₃ :=
          adj.unit.naturality U.mor₃
        rw [← Category.assoc, ← hn, Category.assoc]
        congr 1
        have h := (NatTrans.shift_app_comm adj.unit (1 : ℤ) U.obj₁).symm
        simp only [Functor.commShiftIso_id_hom_app, Functor.id_obj] at h
        exact h.trans (Category.id_comp _)

private noncomputable def parametrizedRightAdjointIso
    {C : Type u} [Category.{v} C] (T : C ⥤ C ⥤ C)
    (H G : Cᵒᵖ ⥤ C ⥤ C) (a : T ⊣₂ H) (b : T ⊣₂ G) (W : C) :
    H.flip.obj W ≅ G.flip.obj W :=
  NatIso.ofComponents
    (fun K ↦ ((a.adj K.unop).rightAdjointUniq (b.adj K.unop)).app W) (by
      intro K K' f
      apply ((b.adj K'.unop).homEquiv _ _).symm.injective
      change b.homEquiv.symm ((H.map f.unop.op).app W ≫
          ((a.adj K'.unop).rightAdjointUniq (b.adj K'.unop)).hom.app W) =
        b.homEquiv.symm
          (((a.adj K.unop).rightAdjointUniq (b.adj K.unop)).hom.app W ≫
            (G.map f.unop.op).app W)
      rw [b.homEquiv_symm_naturality_two, b.homEquiv_symm_naturality_one]
      simp only [ParametrizedAdjunction.homEquiv_eq,
        Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
      exact (NatTrans.congr_app (a.whiskerLeft_map_counit f.unop) W).symm)

private theorem parametrizedHom_exact
    (B : Type c) [Category.{v} B] [Abelian B]
    [IsGrothendieckAbelian.{v} B] [HasDerivedCategory.{v} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : _root_.DerivedCategory B ⥤ _root_.DerivedCategory B ⥤ _root_.DerivedCategory B)
    (H : (_root_.DerivedCategory B)ᵒᵖ ⥤
      _root_.DerivedCategory B ⥤ _root_.DerivedCategory B) (a : T ⊣₂ H)
    (hT : T = @curriedTensor _ _
      (DerivedMonoidal.instMonoidalCategory _root_.DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (.up ℤ))))
    (W : _root_.DerivedCategory B) :
    ∃ s : (H.flip.obj W).CommShift ℤ, let := s
      (H.flip.obj W).IsTriangulated := by
  subst T
  obtain ⟨s, htri⟩ := _root_.DerivedCategory.nativeInternalHom_contravariant_exact B W
  let := s
  let := htri
  let e := parametrizedRightAdjointIso _ MonoidalClosed.internalHom H
    MonoidalClosed.internalHomAdjunction₂ a W
  let : (H.flip.obj W).CommShift ℤ := Functor.CommShift.ofIso e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso e⟩

private theorem nativeTensorRaw
    (B : Type c) [Category.{v} B] [Abelian B]
    [IsGrothendieckAbelian.{v} B] [HasDerivedCategory.{v} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [BraidedCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] :
    curriedTensor (_root_.DerivedCategory B) =
      @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory _root_.DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (.up ℤ))) := by
  rfl

/-- Evaluation and biduality with specified tensor, Hom, adjunction and interchange.
The predicate P fixes the interchange by its components; the remaining clauses are the
normalizations, naturality, integral shift coherence and triangle morphism. -/
private def NormalizedDualityPairing {C : Type u} [Category.{v} C]
    [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (a : ∀ K, T.obj K ⊣ H.obj (op K)) (P : (T ≅ T.flip) → Prop) (W : C) : Prop :=
  ∃ b : T ≅ T.flip, P b ∧
    ∃ e : ∀ K : C, (T.obj ((H.obj (op K)).obj W)).obj K ⟶ W,
      (∀ K : C, (a K).homEquiv ((H.obj (op K)).obj W) W
        ((b.hom.app K).app ((H.obj (op K)).obj W) ≫ e K) = 𝟙 _) ∧
      ∃ δ : ∀ K : C, K ⟶ (dualityDoubleFunctor H W).obj K,
        (∀ K : C, δ K = (a ((H.obj (op K)).obj W)).homEquiv K W (e K)) ∧
        DualityPairingCompatibility T H W e δ

private theorem localizedPairing
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    [MonoidalCategory C] [BraidedCategory C]
    (L : C ⥤ D) (S : MorphismProperty C)
    [L.IsLocalization S] [S.ContainsIdentities] [L.HasDerivedMonoidalCategory S]
    [S.RespectsIso] [S.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    [S.HasTwoOutOfThreeProperty]
    [HasShift D ℤ] [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : D ⥤ D ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D) (a : T ⊣₂ H)
    (a₁ : ∀ K, T.obj K ⊣ H.obj (op K)) (ha : ∀ K, a₁ K = a.adj K)
    (hT : T = @curriedTensor _ _ (DerivedMonoidal.instMonoidalCategory L S))
    (W : D)
    (hs : ∃ s : (H.flip.obj W).CommShift ℤ, let := s
      (H.flip.obj W).IsTriangulated) :
    NormalizedDualityPairing T H a₁
      (fun b ↦ ∀ K N : D, HEq ((b.hom.app K).app N)
        (DerivedMonoidal.braiding' L S K N).hom) W := by
  have h : a₁ = a.adj := funext ha
  subst a₁
  subst T
  let : MonoidalCategory D := DerivedMonoidal.instMonoidalCategory L S
  let : BraidedCategory D := DerivedMonoidal.braidedCategory' L S
  refine ⟨BraidedCategory.curriedBraidingNatIso _, ?_, parametrizedPairing H a W hs⟩
  intro K N
  rfl

end CategoryTheory

namespace AlgebraicGeometry

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

namespace Etale

/-- Evaluation and its adjoint double-dual arrow with their canonical normalizations.
The tensor symmetry is the descended Koszul symmetry. After interchanging its factors,
evaluation corresponds to the identity under tensor-Hom adjunction. The arrow δ is its
transpose. -/
def AmbientDualityPairing
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  ∃ b : derivedTensor A X ≅ (derivedTensor A X).flip,
    (∀ K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
      HEq ((b.hom.app K).app L)
        (DerivedMonoidal.braiding'
          (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A))
          (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) K L).hom) ∧
    ∃ e : ∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
        ((derivedTensor A X).obj (((derivedHom A X).obj (op K)).obj W)).obj K ⟶ W,
      (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
        (derivedTensorHomAdjunction A K).homEquiv
          (((derivedHom A X).obj (op K)).obj W) W
          (((b.hom.app K).app (((derivedHom A X).obj (op K)).obj W)) ≫ e K) =
            𝟙 (((derivedHom A X).obj (op K)).obj W)) ∧
      ∃ δ : ∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
          K ⟶ (dualityDoubleFunctor (derivedHom A X) W).obj K,
        (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
          δ K = (derivedTensorHomAdjunction A
            (((derivedHom A X).obj (op K)).obj W)).homEquiv K W (e K)) ∧
        DualityPairingCompatibility (derivedTensor A X) (derivedHom A X) W e δ

end Etale

namespace ProEtale

/-- Evaluation and its adjoint double-dual arrow with their canonical normalizations.
The tensor symmetry is the descended Koszul symmetry. After interchanging its factors,
evaluation corresponds to the identity under tensor-Hom adjunction. The arrow δ is its
transpose. -/
def AmbientDualityPairing
    (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Prop :=
  let T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) := curriedTensor _
  let H : (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
    MonoidalClosed.internalHom
  ∃ b : T ≅ (T).flip,
    (∀ K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
      HEq ((b.hom.app K).app L)
        (DerivedMonoidal.braiding'
          (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X) A))
          (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A)
            (ComplexShape.up ℤ)) K L).hom) ∧
    ∃ e : ∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
        ((T).obj (((H).obj (op K)).obj W)).obj K ⟶ W,
      (∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
        (MonoidalClosed.internalHomAdjunction₂.adj K).homEquiv
          (((H).obj (op K)).obj W) W
          (((b.hom.app K).app (((H).obj (op K)).obj W)) ≫ e K) =
            𝟙 (((H).obj (op K)).obj W)) ∧
      ∃ δ : ∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
          K ⟶ (dualityDoubleFunctor H W).obj K,
        (∀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A),
          δ K = (MonoidalClosed.internalHomAdjunction₂.adj
            (((H).obj (op K)).obj W)).homEquiv K W (e K)) ∧
        DualityPairingCompatibility (T) H W e δ

end ProEtale

namespace Etale

/-- Evaluation and its transpose are natural and compatible with shifts and distinguished
triangles, on the entire ambient derived category. The dualizing object is the ordinary
ambient exceptional inverse image of A. -/
theorem ambient_duality_pairing
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    AmbientDualityPairing (ModuleCat.{u + 1} Λ) Y
      (dualizingComplex Λ aY) ∧
    ∀ W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)),
      ProEtale.AmbientDualityPairing (ModuleCat.{u + 1} Λ) Y W := by
  -- The proof uses the native adjunction and its unit.
  constructor
  · change NormalizedDualityPairing
      (derivedTensor (ModuleCat.{u + 1} Λ) Y) (derivedHom (ModuleCat.{u + 1} Λ) Y)
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)) _ _
    -- Retain the goal's localization instances to avoid expanding the concrete closed
    -- structure during kernel checking. The resulting term is checked normally by Lean.
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      unless target.isAppOf ``CategoryTheory.NormalizedDualityPairing do
        throwError "normalized pairing goal expected"
      let xs := target.getAppArgs
      let T := xs[7]!
      let H := xs[8]!
      let a₁ := xs[9]!
      let P := xs[10]!
      let W := xs[11]!
      let some a₁' ← Lean.Meta.unfoldDefinition? a₁ | throwError "no adjoint expansion"
      let some a := a₁'.find? (fun e =>
        e.isAppOf ``AlgebraicGeometry.Etale.derivedTensorHomAdjunction₂) |
        throwError "adjunction absent"
      let some raw := P.find? (fun e => e.isAppOf ``DerivedMonoidal.braiding') |
        throwError "braiding absent"
      let rs := raw.getAppArgs
      let ts := T.getAppArgs
      let B := rs[7]!.getAppArgs[0]!
      let hT ← Lean.Meta.mkAppM ``AlgebraicGeometry.Etale.etaleTensorRaw #[ts[0]!, ts[7]!]
      let hs ← Lean.Meta.mkAppM
        ``CategoryTheory.parametrizedHom_exact #[B, T, H, a, hT, W]
      let Kty := xs[0]!
      Lean.Meta.withLocalDeclD `K Kty fun K => do
        let lhs ← Lean.Meta.mkAppM' a₁ #[K]
        let ha ← Lean.Meta.mkEqRefl lhs
        let ha ← Lean.Meta.mkLambdaFVars #[K] ha
        let ls := raw.getAppFn.constLevels!
        let f := Lean.mkAppN (Lean.mkConst ``CategoryTheory.localizedPairing
          [ls[2]!, ls[0]!, ls[1]!, ls[3]!]) (rs[:11].toArray)
        let proof ← Lean.Meta.mkAppM' f #[T, H, a, a₁, ha, hT, W, hs]
        (← Lean.Elab.Tactic.getMainGoal).assign proof
  · intro W
    change NormalizedDualityPairing (curriedTensor _) MonoidalClosed.internalHom
      MonoidalClosed.internalHomAdjunction₂.adj _ _
    -- Retain the goal's localization instances to avoid expanding the concrete closed
    -- structure during kernel checking. The resulting term is checked normally by Lean.
    run_tac Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      unless target.isAppOf ``CategoryTheory.NormalizedDualityPairing do
        throwError "normalized pairing goal expected"
      let xs := target.getAppArgs
      let T := xs[7]!
      let H := xs[8]!
      let a₁ := xs[9]!
      let P := xs[10]!
      let W := xs[11]!
      let some a := a₁.find? (fun e =>
        e.isAppOf ``MonoidalClosed.internalHomAdjunction₂) |
        throwError "adjunction absent"
      let some raw := P.find? (fun e => e.isAppOf ``DerivedMonoidal.braiding') |
        throwError "braiding absent"
      let rs := raw.getAppArgs
      let B := rs[7]!.getAppArgs[0]!
      let .succ bc ← Lean.Meta.getLevel B | throwError "coefficient universe"
      let catTy ← Lean.Meta.inferType xs[1]!
      let bv := catTy.getAppFn.constLevels![0]!
      let hT ← Lean.Meta.mkAppOptM'
        (Lean.mkConst ``CategoryTheory.nativeTensorRaw [bv, bc])
        #[some B, none, none, none, none, none, none, none, none, none]
      let hs ← Lean.Meta.mkAppM
        ``CategoryTheory.parametrizedHom_exact #[B, T, H, a, hT, W]
      let Kty := xs[0]!
      Lean.Meta.withLocalDeclD `K Kty fun K => do
        let lhs ← Lean.Meta.mkAppM' a₁ #[K]
        let ha ← Lean.Meta.mkEqRefl lhs
        let ha ← Lean.Meta.mkLambdaFVars #[K] ha
        let ls := raw.getAppFn.constLevels!
        let f := Lean.mkAppN (Lean.mkConst ``CategoryTheory.localizedPairing
          [ls[2]!, ls[0]!, ls[1]!, ls[3]!]) (rs[:11].toArray)
        let proof ← Lean.Meta.mkAppM' f #[T, H, a, a₁, ha, hT, W, hs]
        (← Lean.Elab.Tactic.getMainGoal).assign proof

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (A : Type a) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (X : Scheme.{u})

/-- The double-dual morphism `K ⟶ D(D(K))` specified by an étale evaluation pairing. -/
noncomputable def Etale.AmbientDualityPairing.bidualityMap
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (h : Etale.AmbientDualityPairing A X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ (dualityDoubleFunctor (Etale.derivedHom A X) W).obj K :=
  h.choose_spec.2.choose_spec.2.choose K

/-- The double-dual morphism `K ⟶ D(D(K))` specified by a pro-étale evaluation pairing. -/
noncomputable def ProEtale.AmbientDualityPairing.bidualityMap
    {W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : ProEtale.AmbientDualityPairing A X W)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ (dualityDoubleFunctor MonoidalClosed.internalHom W).obj K :=
  h.choose_spec.2.choose_spec.2.choose K

end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The isomorphism `b : M ⊗ N ≅ N ⊗ M` agrees componentwise with the descended Koszul
symmetry. -/
def IsEtaleKoszulSymmetry (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (b : ∀ M N : DerivedCategoryModule A X,
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ≅
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj N).obj M) : Prop :=
  ∀ M N : DerivedCategoryModule A X,
    HEq (b M N).hom
      (DerivedMonoidal.braiding'
        (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
          (ComplexShape.up ℤ)) M N).hom

end AlgebraicGeometry.Etale
