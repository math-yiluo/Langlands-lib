/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
import WeilConjectures.AlgebraicGeometry.PicardExternalAffineRectangleExact
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Exactness of the explicit left-coefficient Cech sequences

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the short exact
coefficient diagram after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-cech-exact).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The genuine finite subcover of the affine cover, as a family of opens.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardFiniteAffineOpens (X : Scheme.{w}) [CompactSpace X] :
    X.affineCover.finiteSubcover.I₀ → X.Opens :=
  fun i ↦ (X.affineCover.finiteSubcover.f i).opensRange

/-- Scalar-valued Cech cochains, functorially in the coefficient sheaf.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardScalarCechFunctor (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type w} (U : ι → X.Opens) : X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℕ :=
  scalarFunctor f ⋙ sheafToPresheaf _ _ ⋙ cechComplexFunctor U

private instance scalarCech_zero (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type w} (U : ι → X.Opens) : (picardScalarCechFunctor f U).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply HomologicalComplex.hom_ext
    intro n
    dsimp [picardScalarCechFunctor, cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Limits.FormalCoproduct.evalOp]
    apply Pi.hom_ext
    intro t
    simp only [Pi.map_π, zero_comp]
    change _ ≫ (0 : _ ⟶ _) = 0
    exact comp_zero

/-- Tensor with a fixed integer-index complex.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardCechTensorRight (C : CochainComplex (ModuleCat.{w} k) ℤ) :
    CochainComplex (ModuleCat.{w} k) ℤ ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  ((curriedTensor (ModuleCat.{w} k)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj C

private instance cechTensorRight_zero (C : CochainComplex (ModuleCat.{w} k) ℤ) :
    (picardCechTensorRight C).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply HomologicalComplex.hom_ext
    intro n
    change (HomologicalComplex.mapBifunctorMap (0 : P ⟶ Q) (𝟙 C) _ _).f n = 0
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp

/-- Tensor-total Cech model for the left coefficient, extended by zero.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardLeftTensorCechFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  picardScalarCechFunctor f (picardFiniteAffineOpens X) ⋙
    ComplexShape.embeddingUpNat.extendFunctor _ ⋙
    picardCechTensorRight
      (((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G).extend
        ComplexShape.embeddingUpNat)

/-- Product cover, indexed by pairs from the two finite affine covers.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardProductAffineOpens
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] :
    X.affineCover.finiteSubcover.I₀ × Y.affineCover.finiteSubcover.I₀ →
      (Limits.pullback f g).Opens :=
  fun i ↦ pullback.fst f g ⁻¹ᵁ picardFiniteAffineOpens X i.1 ⊓
    pullback.snd f g ⁻¹ᵁ picardFiniteAffineOpens Y i.2

/-- Product-cover Cech model of the external coefficient, extended by zero.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardLeftProductCechFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  tensorPullback (pullback.fst f g) ⋙
    tensorRight ((tensorPullback (pullback.snd f g)).obj G) ⋙
    picardScalarCechFunctor (pullback.fst f g ≫ f) (picardProductAffineOpens f g) ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- The tensor Cech functor sends zero coefficient morphisms to zero.
Source: termwise tensor maps (blueprint: lem-sc-picard-external-cup-left-cech-exact).
Proof: Scalar Cech maps, tensor maps and extension by zero all preserve zero. -/
instance picardLeftTensorCechFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    (picardLeftTensorCechFunctor f g G).PreservesZeroMorphisms := by
  unfold picardLeftTensorCechFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency.types true in
/-- The product Cech functor sends zero coefficient morphisms to zero.
Source: termwise coefficient maps (blueprint: lem-sc-picard-external-cup-left-cech-exact).
Proof: Pullback, tensor, scalar Cech and extension functors preserve zero. -/
instance picardLeftProductCechFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    (picardLeftProductCechFunctor f g G).PreservesZeroMorphisms := by
  have : (tensorPullback (pullback.fst f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).left_adjoint_additive
  unfold picardLeftProductCechFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_shortExact
    (C : CochainComplex (ModuleCat.{w} k) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{w} k) ℤ)) (hS : S.ShortExact) :
    (S.map (picardCechTensorRight C)).ShortExact := by
  classical
  let t (p : ℤ) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS p).splittingOfProjective
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r := HomologicalComplex.mapBifunctorDesc (K₁ := S.X₂) (K₂ := C)
    (F := curriedTensor (ModuleCat.{w} k)) (c := ComplexShape.up ℤ)
    (fun p q hpq ↦ (t p).r ▷ C.X q ≫ HomologicalComplex.ιMapBifunctor
      S.X₁ C (curriedTensor _) (ComplexShape.up ℤ) p q n hpq)
  let s := HomologicalComplex.mapBifunctorDesc (K₁ := S.X₃) (K₂ := C)
    (F := curriedTensor (ModuleCat.{w} k)) (c := ComplexShape.up ℤ)
    (fun p q hpq ↦ (t p).s ▷ C.X q ≫ HomologicalComplex.ιMapBifunctor
      S.X₂ C (curriedTensor _) (ComplexShape.up ℤ) p q n hpq)
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := s, f_r := ?_, s_g := ?_, id := ?_ }
  · change (HomologicalComplex.mapBifunctorMap S.f (𝟙 C) _ _).f n ≫ r = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [curriedTensor_obj_obj, ComplexShape.π_def,
      HomologicalComplex.ι_mapBifunctorMap_assoc, curriedTensor_map_app,
      HomologicalComplex.id_f, curriedTensor_obj_map, whiskerLeft_id,
      HomologicalComplex.ι_mapBifunctorDesc, Category.id_comp, Category.comp_id, r]
    rw [← Category.assoc, ← comp_whiskerRight]
    change ((S.map (HomologicalComplex.eval _ _ p)).f ≫ (t p).r) ▷ _ ≫ _ = _
    rw [(t p).f_r, id_whiskerRight, Category.id_comp]
  · change s ≫ (HomologicalComplex.mapBifunctorMap S.g (𝟙 C) _ _).f n = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [curriedTensor_obj_obj, ComplexShape.π_def,
      HomologicalComplex.ι_mapBifunctorDesc_assoc, Category.assoc,
      HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app, HomologicalComplex.id_f,
      curriedTensor_obj_map, whiskerLeft_id, Category.id_comp, Category.comp_id, s]
    rw [← Category.assoc, ← comp_whiskerRight]
    change ((t p).s ≫ (S.map (HomologicalComplex.eval _ _ p)).g) ▷ _ ≫ _ = _
    rw [(t p).s_g, id_whiskerRight, Category.id_comp]
  · change r ≫ (HomologicalComplex.mapBifunctorMap S.f (𝟙 C) _ _).f n +
      (HomologicalComplex.mapBifunctorMap S.g (𝟙 C) _ _).f n ≫ s = 𝟙 _
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp only [curriedTensor_obj_obj, ComplexShape.π_def, Preadditive.comp_add,
      HomologicalComplex.ι_mapBifunctorDesc_assoc, Category.assoc,
      HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app, HomologicalComplex.id_f,
      curriedTensor_obj_map, whiskerLeft_id, Category.id_comp,
      HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorDesc,
      Category.comp_id, r, s]
    rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight,
      ← comp_whiskerRight, ← Preadditive.add_comp, ← MonoidalPreadditive.add_whiskerRight]
    change ((t p).r ≫ (S.map (HomologicalComplex.eval _ _ p)).f +
      (S.map (HomologicalComplex.eval _ _ p)).g ≫ (t p).s) ▷ _ ≫ _ = _
    rw [(t p).id, id_whiskerRight, Category.id_comp]

private theorem extend_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{w} k) ℕ)) (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingUpNat.extendFunctor _)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : ∃ i, ComplexShape.embeddingUpNat.f i = n
  · obtain ⟨i, hi⟩ := hn
    let e : ((S.map (ComplexShape.embeddingUpNat.extendFunctor _)).map
        (HomologicalComplex.eval _ _ n)) ≅ S.map (HomologicalComplex.eval _ _ i) :=
      ShortComplex.isoMk
      (S.X₁.extendXIso ComplexShape.embeddingUpNat hi)
      (S.X₂.extendXIso ComplexShape.embeddingUpNat hi)
      (S.X₃.extendXIso ComplexShape.embeddingUpNat hi)
      (by
        symm
        change (HomologicalComplex.extendMap S.f _).f n ≫ _ = _
        rw [HomologicalComplex.extendMap_f _ _ hi]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl)
      (by
        symm
        change (HomologicalComplex.extendMap S.g _).f n ≫ _ = _
        rw [HomologicalComplex.extendMap_f _ _ hi]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl)
    exact ShortComplex.shortExact_of_iso e.symm
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i)
  · have h (j : ℕ) : ComplexShape.embeddingUpNat.f j ≠ n := fun hj ↦ hn ⟨j, hj⟩
    have h₁ := S.X₁.isZero_extend_X ComplexShape.embeddingUpNat n h
    have h₂ := S.X₂.isZero_extend_X ComplexShape.embeddingUpNat n h
    have h₃ := S.X₃.isZero_extend_X ComplexShape.embeddingUpNat n h
    apply ShortComplex.Splitting.shortExact
    exact
      { r := 0
        s := 0
        f_r := h₁.eq_of_src _ _
        s_g := h₃.eq_of_src _ _
        id := h₂.eq_of_src _ _ }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cech_shortExact
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens)
    (S : ShortComplex X.Modules)
    (h : ∀ (n : ℕ) (y : Fin (n + 1) → ι),
      (S.map (picardScalarSectionsFunctor f (∏ᶜ fun l ↦ U (y l)))).ShortExact) :
    (S.map (picardScalarCechFunctor f U)).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let P := scalarFunctor f ⋙ sheafToPresheaf _ _
  let t (y : Fin (n + 1) → ι) := (h n y).splittingOfProjective
  let r : (∏ᶜ fun y : Fin (n + 1) → ι ↦
      (P.obj S.X₂).obj (Opposite.op (∏ᶜ fun l ↦ U (y l)))) ⟶
      (∏ᶜ fun y : Fin (n + 1) → ι ↦
        (P.obj S.X₁).obj (Opposite.op (∏ᶜ fun l ↦ U (y l)))) := Pi.lift fun y : Fin (n + 1) → ι ↦
    Pi.π (fun y : Fin (n + 1) → ι ↦ (P.obj S.X₂).obj
      (Opposite.op (∏ᶜ fun l ↦ U (y l)))) y ≫ (t y).r
  let s : (∏ᶜ fun y : Fin (n + 1) → ι ↦
      (P.obj S.X₃).obj (Opposite.op (∏ᶜ fun l ↦ U (y l)))) ⟶
      (∏ᶜ fun y : Fin (n + 1) → ι ↦
        (P.obj S.X₂).obj (Opposite.op (∏ᶜ fun l ↦ U (y l)))) := Pi.lift fun y : Fin (n + 1) → ι ↦
    Pi.π (fun y : Fin (n + 1) → ι ↦ (P.obj S.X₃).obj
      (Opposite.op (∏ᶜ fun l ↦ U (y l)))) y ≫ (t y).s
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := s, f_r := ?_, s_g := ?_, id := ?_ }
  · apply Pi.hom_ext
    intro y
    change (Limits.Pi.map fun y : Fin (n + 1) → ι ↦
      (P.map S.f).app (Opposite.op (∏ᶜ fun l ↦ U (y l)))) ≫ r ≫ Pi.π _ y = _
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map,
      ObjectProperty.ι_map, picardScalarSectionsFunctor, Functor.rightOp_obj,
      limit.lift_π, Fan.mk_pt, Fan.mk_π_app, ← Category.assoc, Pi.map_π,
      Category.id_comp, P, r]
    change _ ≫ ((S.map (picardScalarSectionsFunctor f (∏ᶜ fun l ↦ U (y l)))).f ≫ (t y).r) = _
    rw [(t y).f_r]
    simp only [Category.comp_id]
    rfl
  · apply Pi.hom_ext
    intro y
    change s ≫ (Limits.Pi.map fun y : Fin (n + 1) → ι ↦
      (P.map S.g).app (Opposite.op (∏ᶜ fun l ↦ U (y l)))) ≫ Pi.π _ y = _
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, picardScalarSectionsFunctor,
      Functor.comp_map, ObjectProperty.ι_map, Functor.rightOp_obj, Pi.map_π,
      ← Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Category.id_comp, P, s]
    change _ ≫ ((t y).s ≫ (S.map (picardScalarSectionsFunctor f (∏ᶜ fun l ↦ U (y l)))).g) = _
    rw [(t y).s_g]
    simp only [Category.comp_id]
    rfl
  · apply Pi.hom_ext
    intro y
    change (r ≫ (Limits.Pi.map fun y : Fin (n + 1) → ι ↦
      (P.map S.f).app (Opposite.op (∏ᶜ fun l ↦ U (y l)))) +
      (Limits.Pi.map fun y : Fin (n + 1) → ι ↦
      (P.map S.g).app (Opposite.op (∏ᶜ fun l ↦ U (y l)))) ≫ s) ≫ Pi.π _ y = _
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, picardScalarSectionsFunctor,
      Functor.comp_map, ObjectProperty.ι_map, Functor.rightOp_obj, Preadditive.add_comp,
      Category.assoc, Pi.map_π, limit.lift_π_assoc, Fan.mk_pt, Discrete.functor_obj_eq_as,
      Fan.mk_π_app, limit.lift_π, Pi.map_π_assoc, Category.id_comp, P, r, s]
    rw [← Preadditive.comp_add]
    change _ ≫ ((t y).r ≫ (S.map (picardScalarSectionsFunctor f (∏ᶜ fun l ↦ U (y l)))).f +
      (S.map (picardScalarSectionsFunctor f (∏ᶜ fun l ↦ U (y l)))).g ≫ (t y).s) = _
    rw [(t y).id]
    simp only [Category.comp_id]
    rfl

private theorem opens_pi_eq_iInf {Z : Scheme.{w}} {ι : Type*} (U : ι → Z.Opens) :
    (∏ᶜ U) = ⨅ i, U i := by
  apply le_antisymm
  · exact le_iInf fun i ↦ (Pi.π U i).le
  · exact (Pi.lift fun i ↦ homOfLE (iInf_le U i)).le

private theorem affine_intersection
    (f : X ⟶ Spec (CommRingCat.of k)) [IsAffineHom (pullback.diagonal f)]
    {ι : Type w} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (n : ℕ) (y : Fin (n + 1) → ι) : IsAffineOpen (∏ᶜ fun l ↦ U (y l)) := by
  rw [opens_pi_eq_iInf]
  have hinf : InfClosed (Set.ofPred (IsAffineOpen (X := X))) := by
    intro A hA B hB
    exact (isAffineHom_diagonal_iff (f := f)).mp inferInstance ⊤ (isAffineOpen_top _)
      A (by simp) B (by simp) hA hB
  exact hinf.iInf_mem_of_nonempty (fun l ↦ hU (y l))

private theorem finite_affine_opens (Z : Scheme.{w}) [CompactSpace Z]
    (i : Z.affineCover.finiteSubcover.I₀) : IsAffineOpen (picardFiniteAffineOpens Z i) := by
  dsimp [picardFiniteAffineOpens, Scheme.OpenCover.finiteSubcover_f]
  exact isAffineOpen_opensRange _

/-- Both explicit Cech sequences are short exact in the left coefficient.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the short exact
coefficient diagram after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-cech-exact).

Proof: The finite affine covers have affine finite intersections by the affine
relative diagonals over Spec k. On each intersection a quasi-coherent short exact
sequence has an exact sequence of sections: kernels are sectionwise, and the
quasi-coherent affine cokernel formula gives surjectivity. Scalar restriction to k
preserves this sequence. Tensoring with each section space of G is exact over the
field. Products indexed by cover tuples and the finite sums in each tensor-total
degree preserve short exactness, proving the tensor assertion degreewise. On each
intersection of the product cover, affine pullback and tensor section formulas
identify external coefficient sections with the tensor of the corresponding factor
sections, naturally in the left coefficient. Hence the product-cover sequence is
also degreewise short exact; no flatness of G over O_Y is needed. Extension by zero
preserves these sequences, and degreewise exactness, monicity and epicity give
short exactness of cochain complexes. Empty schemes and zero coefficients yield
zero terms and cause no exception. No cup map or cohomology comparison is used. -/
theorem picardExternalCup_left_cech_exact
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] :
    (S.map (picardLeftTensorCechFunctor f g G)).ShortExact ∧
      (S.map (picardLeftProductCechFunctor f g G)).ShortExact := by
  have hcech : (S.map (picardScalarCechFunctor f (picardFiniteAffineOpens X))).ShortExact := by
    apply cech_shortExact
    intro n y
    exact picardScalar_affine_sections_exact f _
      (affine_intersection f _ (finite_affine_opens X) n y) S hS
  have ht := tensor_shortExact
    (((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G).extend
      ComplexShape.embeddingUpNat) _ (extend_shortExact _ hcech)
  have hp : ((S.map (picardExternalCoefficientFunctor f g G)).map
      (picardScalarCechFunctor (pullback.fst f g ≫ f)
        (picardProductAffineOpens f g))).ShortExact := by
    apply cech_shortExact
    intro n y
    have hrect : (∏ᶜ fun l ↦ picardProductAffineOpens f g (y l)) =
        pullback.fst f g ⁻¹ᵁ (∏ᶜ fun l ↦ picardFiniteAffineOpens X (y l).1) ⊓
          pullback.snd f g ⁻¹ᵁ (∏ᶜ fun l ↦ picardFiniteAffineOpens Y (y l).2) := by
      simp only [opens_pi_eq_iInf]
      ext x
      simp [picardProductAffineOpens, TopologicalSpace.Opens.coe_iInf, forall_and]
    rw [hrect]
    exact picardExternal_affine_rectangle_exact f g _ _
      (affine_intersection f _ (finite_affine_opens X) n (fun l ↦ (y l).1))
      (affine_intersection g _ (finite_affine_opens Y) n (fun l ↦ (y l).2)) S hS G
  exact ⟨ht, extend_shortExact _ hp⟩

end
end AlgebraicGeometry.Scheme.Modules
