/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Homology.Embedding.Extend
import WeilConjectures.AlgebraicGeometry.PicardExternalRightRectangleSymmetry
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Adjunction.Additive
@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
private local instance cech_zero
    {k : Type w} [Field k] {Z : TopCat.{w}} {α : Type w}
    (W : α → TopologicalSpace.Opens Z) :
    (cechComplexFunctor (A := ModuleCat.{w} k) W).PreservesZeroMorphisms := by
  constructor
  intro P Q
  apply HomologicalComplex.Hom.ext
  funext n
  apply TopCat.Presheaf.cechComplexFunctor_hom_ext W Q
  intro y
  rw [TopCat.Presheaf.cechComplexFunctor_map_f_π]
  simp

private theorem cech_shortExact
    {k : Type w} [Field k] {Z : TopCat.{w}} {α : Type w}
    (W : α → TopologicalSpace.Opens Z)
    (T : ShortComplex ((TopologicalSpace.Opens Z)ᵒᵖ ⥤ ModuleCat.{w} k))
    (hT : ∀ n (y : Fin (n + 1) → α),
      (T.map ((CategoryTheory.evaluation _ _).obj (Opposite.op (∏ᶜ fun l ↦ W (y l))))).ShortExact) :
    (T.map (cechComplexFunctor W)).ShortExact := by
  classical
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro n
  let D := (T.map (cechComplexFunctor W)).map
    (HomologicalComplex.eval (ModuleCat.{w} k) (.up ℕ) n)
  have hp (i : Fin (n + 1) → α) := hT n i
  have comm₁ (x : D.X₁) (i : Fin (n + 1) → α) :
      TopCat.Presheaf.cechComplexFunctorπ W T.X₂ n i (D.f x) =
        T.f.app _ (TopCat.Presheaf.cechComplexFunctorπ W T.X₁ n i x) := by
    exact ConcreteCategory.congr_hom
      (TopCat.Presheaf.cechComplexFunctor_map_f_π W T.X₁ T.f n i) x
  have comm₂ (x : D.X₂) (i : Fin (n + 1) → α) :
      TopCat.Presheaf.cechComplexFunctorπ W T.X₃ n i (D.g x) =
        T.g.app _ (TopCat.Presheaf.cechComplexFunctorπ W T.X₂ n i x) := by
    exact ConcreteCategory.congr_hom
      (TopCat.Presheaf.cechComplexFunctor_map_f_π W T.X₂ T.g n i) x
  have lift (P : (TopologicalSpace.Opens Z)ᵒᵖ ⥤ ModuleCat.{w} k)
      (c : ∀ i : Fin (n + 1) → α, P.obj (Opposite.op (∏ᶜ fun l ↦ W (i l)))) :
      ∃ x : ((cechComplexFunctor W).obj P).X n,
        ∀ i, TopCat.Presheaf.cechComplexFunctorπ W P n i x = c i := by
    exact ⟨(ModuleCat.piIsoPi _).inv c,
      TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv W P c⟩
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply D.moduleCat_exact_iff.mpr
    intro x hx
    have h (i : Fin (n + 1) → α) :
        ∃ z, T.f.app _ z = TopCat.Presheaf.cechComplexFunctorπ W T.X₂ n i x := by
      apply (T.map ((CategoryTheory.evaluation _ _).obj _)).moduleCat_exact_iff.mp (hp i).exact
      change T.g.app _ (TopCat.Presheaf.cechComplexFunctorπ W T.X₂ n i x) = 0
      rw [← comm₂, hx]
      exact map_zero _
    choose z hz using h
    obtain ⟨a, ha⟩ := lift T.X₁ z
    refine ⟨a, TopCat.Presheaf.cechComplexFunctor_ext W T.X₂ fun i ↦ ?_⟩
    rw [comm₁, ha, hz]
  · apply (ModuleCat.mono_iff_injective D.f).mpr
    intro a b hab
    apply TopCat.Presheaf.cechComplexFunctor_ext W T.X₁
    intro i
    apply (hp i).moduleCat_injective_f
    change T.f.app _ _ = T.f.app _ _
    rw [← comm₁, ← comm₁, hab]
  · apply (ModuleCat.epi_iff_surjective D.g).mpr
    intro x
    choose z hz using fun i ↦
      (hp i).moduleCat_surjective_g (TopCat.Presheaf.cechComplexFunctorπ W T.X₃ n i x)
    obtain ⟨a, ha⟩ := lift T.X₂ z
    refine ⟨a, TopCat.Presheaf.cechComplexFunctor_ext W T.X₃ fun i ↦ ?_⟩
    rw [comm₂, ha]
    exact hz i

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem extend_shortExact {k : Type w} [Field k]
    (S : ShortComplex (CochainComplex (ModuleCat.{w} k) ℕ)) (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{w} k))).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro j
  by_cases hj : 0 ≤ j
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    let e : ((S.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{w} k))).map
        (HomologicalComplex.eval _ (.up ℤ) (n : ℤ))) ≅
        S.map (HomologicalComplex.eval _ (.up ℕ) n) :=
      ShortComplex.isoMk (S.X₁.extendXIso ComplexShape.embeddingUpNat rfl)
        (S.X₂.extendXIso ComplexShape.embeddingUpNat rfl)
        (S.X₃.extendXIso ComplexShape.embeddingUpNat rfl)
        (by dsimp; simp [HomologicalComplex.extendMap_f])
        (by dsimp; simp [HomologicalComplex.extendMap_f])
    exact ShortComplex.shortExact_of_iso e.symm
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n)
  · have hz (K : CochainComplex (ModuleCat.{w} k) ℕ) :
        IsZero ((K.extend ComplexShape.embeddingUpNat).X j) :=
      HomologicalComplex.isZero_extend_X K _ j (by intro n hn; dsimp at hn; omega)
    let T := (S.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{w} k))).map
      (HomologicalComplex.eval _ (.up ℤ) j)
    have : IsIso T.g := by
      rw [(hz S.X₂).eq_of_src T.g 0]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hz S.X₂, hz S.X₃⟩
    exact (ShortComplex.Splitting.ofIsZeroOfIsIso T (hz S.X₁) inferInstance).shortExact

private theorem affine_tuple {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsAffineHom (pullback.diagonal f)]
    {α : Type w} (U : α → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    {n : ℕ} (y : Fin (n + 1) → α) : IsAffineOpen (⨅ l, U (y l)) := by
  apply InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) ?_
    (fun l ↦ hU (y l))
  intro A hA B hB
  exact (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
    A (by simp) B (by simp) hA hB

/-- The product-cover Cech sequence is short exact in the right coefficient.
Source: Stacks Project, Varieties, Tag 0BED, the coefficient diagram following
equation-kunneth-on-cech, applied in the right variable.
(blueprint: lem-sc-picard-external-right-cech-exact-product).

Proof: A tuple of pairs in degree n specifies a nonempty finite intersection A
of the U opens and B of the V opens. Both are affine by the affine diagonal
criterion, and the product-cover intersection is A times B over Spec k.
Write A=Spec R and B=Spec T. If M is the R-module of F-sections on A and Nᵢ
is the T-module of S.Xᵢ-sections on B, the affine pullback and tensor formulas
identify the external coefficient sections on this product with M tensor_k Nᵢ.
These identifications are natural in S, so the coefficient maps become tensor
products of the section maps. The sequence of Nᵢ is short exact: sections
preserve kernels, and affine quasi-coherent vanishing of H^1 of S.X₁ gives
surjectivity. Tensoring with M preserves it because k is a field. Taking the
finite product over all degree-n tuples proves degreewise short exactness of
the product-cover Cech sequence. Extension by zero places zero sequences in
negative degrees; degreewise short exactness then gives short exactness of
complexes. Empty index families have zero Cech terms, and zero coefficients
likewise cause no exception. No cover condition or flatness over O_X is used. -/
theorem picardExternal_right_cech_product_exact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (picardRightProductCechFunctor f g U V F)).ShortExact := by
  classical
  let : (tensorPullback (pullback.snd f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction _)).left_adjoint_additive
  let : (CategoryTheory.MonoidalCategory.tensorLeft
      ((tensorPullback (pullback.fst f g)).obj F)).Additive := by
    have : PreservesColimitsOfSize.{0, 0}
        (CategoryTheory.MonoidalCategory.tensorLeft
          ((tensorPullback (pullback.fst f g)).obj F)) :=
      (SheafOfModules.tensorHomAdjunction (Limits.pullback f g).sheaf
        ((tensorPullback (pullback.fst f g)).obj F)).leftAdjoint_preservesColimits
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (CategoryTheory.MonoidalCategory.tensorLeft
        ((tensorPullback (pullback.fst f g)).obj F))
    exact Functor.additive_of_preservesBinaryBiproducts _
  let E := tensorPullback (pullback.snd f g) ⋙
    CategoryTheory.MonoidalCategory.tensorLeft
      ((tensorPullback (pullback.fst f g)).obj F) ⋙
    scalarFunctor (pullback.fst f g ≫ f) ⋙ sheafToPresheaf _ _
  let : E.PreservesZeroMorphisms := by
    constructor
    intro A B
    change (scalarHom (pullback.fst f g ≫ f)
      ((CategoryTheory.MonoidalCategory.tensorLeft
        ((tensorPullback (pullback.fst f g)).obj F)).map
          ((tensorPullback (pullback.snd f g)).map (0 : A ⟶ B)))).hom = 0
    rw [Functor.map_zero, Functor.map_zero]
    ext W x
    rfl
  let W := fun ij : ι × κ ↦
    pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2
  have hT : ((S.map E).map (cechComplexFunctor W)).ShortExact := by
    apply cech_shortExact
    intro n y
    have hW : (∏ᶜ fun l ↦ W (y l)) =
        pullback.fst f g ⁻¹ᵁ (⨅ l, U (y l).1) ⊓
          pullback.snd f g ⁻¹ᵁ (⨅ l, V (y l).2) := by
      have heq : (∏ᶜ fun l ↦ W (y l)) = ⨅ l, W (y l) :=
        le_antisymm (le_iInf fun l ↦ (Pi.π _ l).le)
          (Pi.lift fun l ↦ homOfLE (iInf_le _ l)).le
      rw [heq]
      ext z
      simp [W, TopologicalSpace.Opens.coe_iInf, forall_and]
    obtain ⟨e⟩ := picardExternal_right_rectangle_symmetry f g
      (⨅ l, U (y l).1) (⨅ l, V (y l).2) F
    have hleft := picardExternal_affine_rectangle_exact g f
      (⨅ l, V (y l).2) (⨅ l, U (y l).1)
      (affine_tuple g V hV (fun l ↦ (y l).2))
      (affine_tuple f U hU (fun l ↦ (y l).1)) S hS F
    have hr := ShortComplex.shortExact_of_iso (S.mapNatIso e).symm hleft
    change (S.map (tensorPullback (pullback.snd f g) ⋙
      CategoryTheory.MonoidalCategory.tensorLeft ((tensorPullback (pullback.fst f g)).obj F) ⋙
      picardScalarSectionsFunctor (pullback.fst f g ≫ f)
        (∏ᶜ fun l ↦ W (y l)))).ShortExact
    rw [hW]
    exact hr
  exact extend_shortExact _ hT
end AlgebraicGeometry.Scheme.Modules
