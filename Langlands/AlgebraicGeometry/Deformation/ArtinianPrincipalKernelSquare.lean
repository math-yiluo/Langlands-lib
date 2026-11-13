import Langlands.AlgebraicGeometry.Deformation.ArtinianAugmentationArrow
import Langlands.AlgebraicGeometry.Deformation.ArtinianTestPullbacks
import Langlands.AlgebraicGeometry.Deformation.ArtinianDualNumbers
import Langlands.AlgebraicGeometry.Deformation.ArtinianElementaryKernel
import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelSubspaceQuotient

/-! # The self fibre product of a principal elementary surjection over the dual numbers -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianTest.PrincipalKernel

open ElementaryKernel

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {A B : ArtinianTest k K} (q : A ⟶ B)

/-- The augmentation of a test as an arrow to the residue test. -/
abbrev augArrow (A : ArtinianTest k K) : A ⟶ residue k K :=
  Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianChartVersality.augmentationArrow A

/-- The augmentations of the two coordinates of a compatible pair agree. -/
lemma augmentation_fst_eq_snd (x : Pullback.algebra q q) :
    A.augmentation x.val.1 = A.augmentation x.val.2 := by
  have hx : toAlgHom q x.val.1 = toAlgHom q x.val.2 := x.property
  rw [← augmentation_comp q]
  change B.augmentation (toAlgHom q x.val.1) = B.augmentation (toAlgHom q x.val.2)
  rw [hx]

/-- The difference of the two coordinates of a compatible pair, in the kernel. -/
def diff (x : Pullback.algebra q q) : Kernel q :=
  ⟨x.val.2 - x.val.1, by
    have hx : toAlgHom q x.val.1 = toAlgHom q x.val.2 := x.property
    rw [RingHom.mem_ker]
    change toAlgHom q (x.val.2 - x.val.1) = 0
    rw [map_sub, hx, sub_self]⟩

@[simp]
lemma diff_val (x : Pullback.algebra q q) : (diff q x).val = x.val.2 - x.val.1 := rfl

variable (c : Kernel q ≃+ K)
  (hc : ∀ (a : A.algebra) (x : Kernel q), c (a • x) = A.augmentation a * c x)

include hc in
lemma diff_mul (x y : Pullback.algebra q q) :
    c (diff q (x * y)) =
      A.augmentation x.val.1 * c (diff q y) + c (diff q x) * A.augmentation y.val.1 := by
  have h : diff q (x * y) = x.val.2 • diff q y + y.val.1 • diff q x := by
    apply Subtype.ext
    change x.val.2 * y.val.2 - x.val.1 * y.val.1 =
      x.val.2 * (y.val.2 - y.val.1) + y.val.1 * (x.val.2 - x.val.1)
    ring
  rw [h, map_add, hc, hc, augmentation_fst_eq_snd q x, mul_comm (A.augmentation y.val.1)]

/-- The map from the self fibre product to the dual numbers:
`(a, a') ↦ (ε(a), c(a' - a))`. -/
def dualMap : Pullback.algebra q q →ₐ[k] DualNumber K where
  toFun x := (A.augmentation x.val.1, c (diff q x))
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one A.augmentation
    · change c (diff q 1) = 0
      have : diff q 1 = 0 := Subtype.ext (sub_self _)
      rw [this, map_zero]
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul A.augmentation _ _
    · change c (diff q (x * y)) = _
      rw [diff_mul q c hc]
      change _ = A.augmentation x.val.1 * c (diff q y) + c (diff q x) * A.augmentation y.val.1
      rfl
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero A.augmentation
    · change c (diff q 0) = 0
      have : diff q 0 = 0 := Subtype.ext (sub_self _)
      rw [this, map_zero]
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · exact map_add A.augmentation _ _
    · change c (diff q (x + y)) = c (diff q x) + c (diff q y)
      have : diff q (x + y) = diff q x + diff q y := by
        apply Subtype.ext
        change (x.val.2 + y.val.2) - (x.val.1 + y.val.1) = (x.val.2 - x.val.1) + (y.val.2 - y.val.1)
        ring
      rw [this, map_add]
  commutes' r := by
    apply TrivSqZeroExt.ext
    · exact A.augmentation.commutes r
    · change c (diff q (algebraMap k _ r)) = 0
      have : diff q (algebraMap k _ r) = 0 := Subtype.ext (sub_self _)
      rw [this, map_zero]

@[simp]
lemma dualMap_fst (x : Pullback.algebra q q) :
    (dualMap q c hc x).fst = A.augmentation x.val.1 := rfl

@[simp]
lemma dualMap_snd (x : Pullback.algebra q q) :
    (dualMap q c hc x).snd = c (diff q x) := rfl

/-- The comparison map from the self fibre product to the fibre product of the
augmentation with the dual-number augmentation. -/
def comparison : Pullback.algebra q q →+* Pullback.algebra (augArrow A) (dualReduction k K) :=
  Pullback.liftRingHom (augArrow A) (dualReduction k K)
    (AlgHom.pullbackFst (toAlgHom q) (toAlgHom q)).toRingHom (dualMap q c hc).toRingHom
    (RingHom.ext fun _ ↦ rfl)

lemma comparison_fst (x : Pullback.algebra q q) :
    (comparison q c hc x).val.1 = x.val.1 := rfl

lemma comparison_snd (x : Pullback.algebra q q) :
    (comparison q c hc x).val.2 = dualMap q c hc x := rfl

lemma comparison_bijective : Function.Bijective (comparison q c hc) := by
  constructor
  · intro x y hxy
    have h₁ : x.val.1 = y.val.1 := congrArg (fun z ↦ z.val.1) hxy
    have h₂ : c (diff q x) = c (diff q y) :=
      congrArg (fun z : Pullback.algebra (augArrow A) (dualReduction k K) ↦
        TrivSqZeroExt.snd (z.val.2 : DualNumber K)) hxy
    have h₃ : diff q x = diff q y := c.injective h₂
    have h₄ : x.val.2 - x.val.1 = y.val.2 - y.val.1 := congrArg Subtype.val h₃
    apply Subtype.ext
    apply Prod.ext h₁
    rw [h₁] at h₄
    exact sub_left_injective h₄
  · intro z
    let κ : Kernel q := c.symm z.val.2.snd
    have hmem : toAlgHom q z.val.1 = toAlgHom q (z.val.1 + κ.val) := by
      have hκ : toAlgHom q κ.val = 0 := κ.property
      rw [map_add, hκ, add_zero]
    refine ⟨⟨(z.val.1, z.val.1 + κ.val), hmem⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply TrivSqZeroExt.ext
    · exact z.property
    · change c (diff q ⟨(z.val.1, z.val.1 + κ.val), hmem⟩) = z.val.2.snd
      have : diff q ⟨(z.val.1, z.val.1 + κ.val), hmem⟩ = κ :=
        Subtype.ext (add_sub_cancel_left _ _)
      rw [this]
      exact c.apply_symm_apply _

/-- The self fibre product of a principal elementary surjection is the fibre product of
the augmentation with the dual-number augmentation, as commutative rings. -/
lemma isPullback_dual :
    IsPullback
      (CommRingCat.ofHom (AlgHom.pullbackFst (toAlgHom q) (toAlgHom q)).toRingHom)
      (CommRingCat.ofHom (dualMap q c hc).toRingHom)
      (CommRingCat.ofHom A.augmentation.toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom k K K).toRingHom) := by
  let E := RingEquiv.ofBijective (comparison q c hc) (comparison_bijective q c hc)
  refine (Pullback.ring_isPullback (augArrow A) (dualReduction k K)).of_iso
    E.toCommRingCatIso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro y
    change y.val.1 = (E.symm y).val.1
    conv_lhs => rw [← E.apply_symm_apply y]
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro y
    change y.val.2 = dualMap q c hc (E.symm y)
    conv_lhs => rw [← E.apply_symm_apply y]
    rfl
  · rfl
  · rfl

variable (hq : IsElementarySurjection q)

/-- The actual test arrow from the self fibre product to the dual numbers. -/
def dualArrow : Pullback.test q q hq.1 ⟶ dualNumbers k K :=
  homMk (dualMap q c hc) (by
    ext x
    exact augmentation_fst_eq_snd q x)

lemma toAlgHom_dualArrow : toAlgHom (dualArrow q c hc hq) = dualMap q c hc := rfl

section Factor

open ElementaryKernelSubspaceQuotient

variable {A' B' : ArtinianTest k K} (q' : A' ⟶ B') [he : Fact (IsElementarySurjection q')]

local instance : Module K (Kernel q') := residueModule q' he.out

/-- The kernel of the projection to a subspace quotient is the subspace, additively. -/
def projectionKernelEquiv (W : Submodule K (Kernel q')) :
    Kernel (projection q' W) ≃+ W where
  toFun x :=
    have hx : x.val ∈ subspaceIdeal q' W := Ideal.Quotient.eq_zero_iff_mem.mp x.property
    ⟨⟨x.val, subspaceIdeal_le_kernel q' W hx⟩, (mem_subspaceIdeal q' W ⟨x.val, _⟩).mp hx⟩
  invFun y := ⟨(y : Kernel q').val,
    Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_subspaceIdeal q' W y).mpr y.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

lemma projectionKernelEquiv_smul (W : Submodule K (Kernel q')) (a : A'.algebra)
    (x : Kernel (projection q' W)) :
    projectionKernelEquiv q' W (a • x) = A'.augmentation a • projectionKernelEquiv q' W x := by
  apply Subtype.ext
  rw [SetLike.val_smul, augmentation_smul q' he.out]
  rfl

/-- A nonzero kernel vector gives a principal elementary first step. -/
def principalEquiv (ε₀ : Kernel q') (hε₀ : ε₀ ≠ 0) :
    Kernel (projection q' (K ∙ ε₀)) ≃+ K :=
  (projectionKernelEquiv q' (K ∙ ε₀)).trans
    (LinearEquiv.toSpanNonzeroSingleton K (Kernel q') ε₀ hε₀).symm.toAddEquiv

lemma principalEquiv_smul (ε₀ : Kernel q') (hε₀ : ε₀ ≠ 0) (a : A'.algebra)
    (x : Kernel (projection q' (K ∙ ε₀))) :
    principalEquiv q' ε₀ hε₀ (a • x) = A'.augmentation a * principalEquiv q' ε₀ hε₀ x := by
  change (LinearEquiv.toSpanNonzeroSingleton K (Kernel q') ε₀ hε₀).symm
      (projectionKernelEquiv q' (K ∙ ε₀) (a • x)) =
    A'.augmentation a * (LinearEquiv.toSpanNonzeroSingleton K (Kernel q') ε₀ hε₀).symm
      (projectionKernelEquiv q' (K ∙ ε₀) x)
  rw [projectionKernelEquiv_smul, LinearEquiv.map_smul, smul_eq_mul]

/-- The remaining step after a principal quotient has kernel dimension one less. -/
lemma finrank_reduction_add_one (ε₀ : Kernel q') (hε₀ : ε₀ ≠ 0)
    [FiniteDimensional K (Kernel q')] :
    letI := residueModule (ElementaryKernelSubspaceQuotient.reduction q' (K ∙ ε₀))
      (reduction_elementary q' (K ∙ ε₀))
    Module.finrank K (Kernel (ElementaryKernelSubspaceQuotient.reduction q' (K ∙ ε₀))) + 1 =
      Module.finrank K (Kernel q') := by
  let := residueModule (ElementaryKernelSubspaceQuotient.reduction q' (K ∙ ε₀))
    (reduction_elementary q' (K ∙ ε₀))
  rw [← (quotientKernelEquiv q' (K ∙ ε₀)).finrank_eq,
    ← Submodule.finrank_quotient_add_finrank (K ∙ ε₀), finrank_span_singleton hε₀]

end Factor

end Langlands.AlgebraicGeometry.Deformation.ArtinianTest.PrincipalKernel
