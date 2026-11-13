import Langlands.AlgebraicGeometry.Picard.FlatPicardSquareGluing
import Langlands.AlgebraicGeometry.Picard.ArtinianChartTestReduction
import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Langlands.AlgebraicGeometry.Deformation.ArtinianPrincipalKernelSquare

/-! # Actual Picard lifting along principal elementary surjections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPrincipalLifting

open Langlands.AlgebraicGeometry.Deformation
open Langlands.CategoryTheory
open Langlands.CategoryTheory.PseudofunctorSquareGluing
open ArtinianChartLifting ArtinianChartVersality ArtinianChartTestReduction

section Glue

variable {k R A B C H : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing H] [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  [Algebra k H]

/-- Maps of affine bases into an affine base glue along the spectrum of a ring pullback. -/
theorem exists_affineBase_glue (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C)
    (b : B →ₐ[k] C)
    (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (g₁ : affineBase k A ⟶ affineBase k H) (g₂ : affineBase k B ⟶ affineBase k H)
    (hg : affineBaseMap a ≫ g₁ = affineBaseMap b ≫ g₂) :
    ∃ g : affineBase k R ⟶ affineBase k H, affineBaseMap p ≫ g = g₁ ∧ affineBaseMap q ≫ g = g₂ := by
  let φ₁ : CommRingCat.of H ⟶ CommRingCat.of A := Spec.preimage g₁.left
  let φ₂ : CommRingCat.of H ⟶ CommRingCat.of B := Spec.preimage g₂.left
  have e₁ : Spec.map φ₁ = g₁.left := Spec.map_preimage _
  have e₂ : Spec.map φ₂ = g₂.left := Spec.map_preimage _
  have hφ : φ₁ ≫ CommRingCat.ofHom a.toRingHom = φ₂ ≫ CommRingCat.ofHom b.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, e₁, e₂]
    exact congrArg CommaMorphism.left hg
  have hk₁ : CommRingCat.ofHom (algebraMap k H) ≫ φ₁ = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, e₁]
    exact Over.w g₁
  have hk₂ : CommRingCat.ofHom (algebraMap k H) ≫ φ₂ = CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, e₂]
    exact Over.w g₂
  let ψ := h.lift φ₁ φ₂ hφ
  have hk : CommRingCat.ofHom (algebraMap k H) ≫ ψ = CommRingCat.ofHom (algebraMap k R) := by
    apply h.hom_ext
    · rw [Category.assoc, h.lift_fst, hk₁]
      apply CommRingCat.hom_ext
      exact (p.comp_algebraMap).symm
    · rw [Category.assoc, h.lift_snd, hk₂]
      apply CommRingCat.hom_ext
      exact (q.comp_algebraMap).symm
  refine ⟨Over.homMk (Spec.map ψ) (by
    change Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k H)) =
      Spec.map (CommRingCat.ofHom (algebraMap k R))
    rw [← Spec.map_comp, hk]), ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom p.toRingHom) ≫ Spec.map ψ = g₁.left
    rw [← Spec.map_comp, h.lift_fst, e₁]
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom q.toRingHom) ≫ Spec.map ψ = g₂.left
    rw [← Spec.map_comp, h.lift_snd, e₂]

end Glue

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Flat f]
  {H : Type u} [CommRing H] [Algebra k H]
  (L : LineBundle ((relativeSpace f).obj (affineBase k H)))
  (p : ArtinianTest.residueBase k K ⟶ affineBase k H)

/-- Elementary surjections have nilpotent kernels. -/
lemma isNilpotent_ker {A B : ArtinianTest k K} {q : A ⟶ B}
    (hq : ArtinianTest.IsElementarySurjection q) :
    IsNilpotent (RingHom.ker (ArtinianTest.toAlgHom q).toRingHom) :=
  ⟨2, hq.ker_sq.trans Ideal.zero_eq_bot.symm⟩

/-- Lifting along a principal elementary surjection, from ring-map lifting and lifting
along the dual numbers (the lifting step of Stacks Lemma 90.13.2). -/
theorem hasBaseLiftingForAt_of_principal {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : ArtinianTest.IsElementarySurjection q)
    (c : ArtinianTest.ElementaryKernel.Kernel q ≃+ K)
    (hc : ∀ (a : A.algebra) (x : ArtinianTest.ElementaryKernel.Kernel q),
      c (a • x) = A.augmentation a * c x)
    (hRL : ∀ (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
      (y : FiberPoints f L N (Over.mk (ArtinianTest.baseMap q))),
      ArtinianTest.reduction B ≫ y.1 = p →
        ∃ u : ArtinianTest.base A ⟶ affineBase k H, ArtinianTest.baseMap q ≫ u = y.1)
    (hTL : HasLiftingForAt f L p (ArtinianTest.dualReduction k K)) :
    HasBaseLiftingForAt f L p q := by
  intro N y hy
  obtain ⟨u, hu⟩ := hRL N y hy
  let fst := ArtinianTest.Pullback.fst q q hq.1
  let snd := ArtinianTest.Pullback.snd q q hq.1
  let π := ArtinianTest.PrincipalKernel.dualArrow q c hc hq
  have w₁ : ArtinianTest.baseMap q ≫ ArtinianTest.baseMap fst =
      ArtinianTest.baseMap q ≫ ArtinianTest.baseMap snd := by
    rw [ArtinianTest.baseMap_comp, ArtinianTest.baseMap_comp,
      ArtinianTest.Pullback.condition]
  have w₂ : ArtinianTest.reduction A ≫ ArtinianTest.baseMap fst =
      ArtinianTest.reduction (ArtinianTest.dualNumbers k K) ≫ ArtinianTest.baseMap π := by
    rw [ArtinianTest.reduction_baseMap, ArtinianTest.reduction_baseMap]
  have hE : IsSquareEffective (relative f) w₁ :=
    affine_isSquareEffective f (ArtinianTest.toAlgHom fst) (ArtinianTest.toAlgHom snd)
      (ArtinianTest.toAlgHom q) (ArtinianTest.toAlgHom q)
      (ArtinianTest.Pullback.ring_isPullback q q) hq.1 (isNilpotent_ker hq)
  have hG : IsSquareHomGluing (relative f) w₂ :=
    affine_isSquareHomGluing f (ArtinianTest.toAlgHom fst)
      (ArtinianTest.PrincipalKernel.dualMap q c hc) A.augmentation
      (TrivSqZeroExt.fstHom k K K) (ArtinianTest.PrincipalKernel.isPullback_dual q c hc)
      (ArtinianTest.dualReduction_elementary k K).1
      (isNilpotent_ker (ArtinianTest.dualReduction_elementary k K))
  have hU : ∀ (g₁ : ArtinianTest.base A ⟶ affineBase k H)
      (g₂ : ArtinianTest.base (ArtinianTest.dualNumbers k K) ⟶ affineBase k H),
      ArtinianTest.reduction A ≫ g₁ = ArtinianTest.reduction (ArtinianTest.dualNumbers k K) ≫ g₂ →
        ∃ g, ArtinianTest.baseMap fst ≫ g = g₁ ∧ ArtinianTest.baseMap π ≫ g = g₂ :=
    fun g₁ g₂ hg ↦ exists_affineBase_glue (ArtinianTest.toAlgHom fst)
      (ArtinianTest.PrincipalKernel.dualMap q c hc) A.augmentation (TrivSqZeroExt.fstHom k K K)
      (ArtinianTest.PrincipalKernel.isPullback_dual q c hc) g₁ g₂ hg
  have hT : ∀ (Z : (relative f).obj (.mk (op (ArtinianTest.base
      (ArtinianTest.Pullback.test q q hq.1)))))
      (y' : PseudofunctorPointFiber.Points (relative f) (Core.mk L) Z
        (Over.mk (ArtinianTest.reduction (ArtinianTest.dualNumbers k K) ≫
          ArtinianTest.baseMap π))),
      y'.1 = p → ∃ x : PseudofunctorPointFiber.Points (relative f) (Core.mk L) Z
        (Over.mk (ArtinianTest.baseMap π)),
        PseudofunctorPointFiber.restrict (relative f) (Core.mk L) Z
          (Over.homMk (ArtinianTest.reduction (ArtinianTest.dualNumbers k K)) rfl :
            Over.mk (ArtinianTest.reduction (ArtinianTest.dualNumbers k K) ≫
              ArtinianTest.baseMap π) ⟶ Over.mk (ArtinianTest.baseMap π)) x = y' := by
    intro Z y' hy'
    exact hTL _ Z.of (ArtinianTest.baseMap π) _ rfl y'
      (by rw [reduction_residue, Category.id_comp]; exact hy')
  exact exists_lift_of_square_gluing (Core.mk L) p (ArtinianTest.baseMap q)
    (ArtinianTest.reduction A) (ArtinianTest.reduction B) (ArtinianTest.reduction_baseMap q)
    (ArtinianTest.reduction (ArtinianTest.dualNumbers k K)) (ArtinianTest.baseMap fst)
    (ArtinianTest.baseMap snd) (ArtinianTest.baseMap π) w₁ w₂ hE hG hU hT (Core.mk N) y hy u hu

/-- The same conclusion in the form of the actual lifting predicate. -/
theorem hasLiftingForAt_of_principal {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : ArtinianTest.IsElementarySurjection q)
    (c : ArtinianTest.ElementaryKernel.Kernel q ≃+ K)
    (hc : ∀ (a : A.algebra) (x : ArtinianTest.ElementaryKernel.Kernel q),
      c (a • x) = A.augmentation a * c x)
    (hRL : ∀ (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
      (y : FiberPoints f L N (Over.mk (ArtinianTest.baseMap q))),
      ArtinianTest.reduction B ≫ y.1 = p →
        ∃ u : ArtinianTest.base A ⟶ affineBase k H, ArtinianTest.baseMap q ≫ u = y.1)
    (hTL : HasLiftingForAt f L p (ArtinianTest.dualReduction k K)) :
    HasLiftingForAt f L p q :=
  (hasLiftingForAt_iff_base f L p q).mpr
    (hasBaseLiftingForAt_of_principal f L p q hq c hc hRL hTL)

omit [Flat f] in
/-- Lifting along a test arrow whose algebra map is bijective. -/
lemma hasLiftingForAt_of_bijective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Bijective (ArtinianTest.toAlgHom q)) : HasLiftingForAt f L p q := by
  let e := AlgEquiv.ofBijective (ArtinianTest.toAlgHom q) hq
  let r : B ⟶ A := ArtinianTest.homMk e.symm.toAlgHom (by
    ext x
    conv_rhs => rw [← e.apply_symm_apply x]
    exact (DFunLike.congr_fun (ArtinianTest.augmentation_comp q) (e.symm x)).symm)
  have hrq : r ≫ q = 𝟙 B := ArtinianTest.hom_ext (by
    ext x
    exact e.apply_symm_apply x)
  have hqr : q ≫ r = 𝟙 A := ArtinianTest.hom_ext (by
    ext x
    exact e.symm_apply_apply x)
  intro T M a b w y _
  have hw' : ArtinianTest.baseMap r ≫ b = a := by
    rw [← w, ← Category.assoc, ArtinianTest.baseMap_comp, hqr, ArtinianTest.baseMap_id,
      Category.id_comp]
  refine ⟨restrict f L r M hw' y, ?_⟩
  change PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M) (testArrow q w)
      (PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk M)
        (testArrow r hw') y) = y
  rw [← PseudofunctorPointFiber.restrict_comp]
  have h1 : testArrow q w ≫ testArrow r hw' = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change ArtinianTest.baseMap q ≫ ArtinianTest.baseMap r = 𝟙 _
    rw [ArtinianTest.baseMap_comp, hrq, ArtinianTest.baseMap_id]
  rw [h1, PseudofunctorPointFiber.restrict_id]

omit [Flat f] in
open ArtinianTest.ElementaryKernel in
/-- Lifting along every elementary surjection follows from lifting along the principal
ones, by induction on the dimension of the kernel. -/
theorem hasLiftingForAt_of_elementary_of_principal
    (hP : ∀ {A B : ArtinianTest k K} (q : A ⟶ B), ArtinianTest.IsElementarySurjection q →
      ∀ (c : Kernel q ≃+ K), (∀ (a : A.algebra) (x : Kernel q),
        c (a • x) = A.augmentation a * c x) → HasLiftingForAt f L p q)
    (n : ℕ) : ∀ {A B : ArtinianTest k K} (q : A ⟶ B)
      (hq : ArtinianTest.IsElementarySurjection q),
      (letI := residueModule q hq; Module.finrank K (Kernel q) = n) →
        HasLiftingForAt f L p q := by
  induction n with
  | zero =>
    intro A B q hq hn
    let := residueModule q hq
    have := finiteDimensional q hq
    have : Subsingleton (Kernel q) := Module.finrank_zero_iff.mp hn
    apply hasLiftingForAt_of_bijective
    refine ⟨fun x y hxy ↦ ?_, hq.1⟩
    have hmem : x - y ∈ RingHom.ker (ArtinianTest.toAlgHom q).toRingHom := by
      rw [RingHom.mem_ker]
      change ArtinianTest.toAlgHom q (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have h0 := congrArg Subtype.val (Subsingleton.elim (⟨x - y, hmem⟩ : Kernel q) 0)
    exact sub_eq_zero.mp h0
  | succ n ih =>
    intro A B q hq hn
    let := residueModule q hq
    have := finiteDimensional q hq
    have : Fact (ArtinianTest.IsElementarySurjection q) := ⟨hq⟩
    have hn' : Module.finrank K (Kernel q) = n + 1 := hn
    obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : Kernel q, ε₀ ≠ 0 :=
      Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hn']; exact Nat.succ_pos n)
    rw [← ArtinianTest.ElementaryKernelSubspaceQuotient.projection_reduction q (K ∙ ε₀)]
    apply hasLiftingForAt_comp
    · exact hP _ (ArtinianTest.ElementaryKernelSubspaceQuotient.projection_elementary q _)
        (ArtinianTest.PrincipalKernel.principalEquiv q ε₀ hε₀)
        (ArtinianTest.PrincipalKernel.principalEquiv_smul q ε₀ hε₀)
    · apply ih _ (ArtinianTest.ElementaryKernelSubspaceQuotient.reduction_elementary q _)
      have h₁ := ArtinianTest.PrincipalKernel.finrank_reduction_add_one q ε₀ hε₀
      omega

omit [Flat f] in
/-- Formal versality from lifting along principal elementary surjections. -/
theorem isFormallyVersalAt_of_principal
    (hP : ∀ {A B : ArtinianTest k K} (q : A ⟶ B), ArtinianTest.IsElementarySurjection q →
      ∀ (c : ArtinianTest.ElementaryKernel.Kernel q ≃+ K),
        (∀ (a : A.algebra) (x : ArtinianTest.ElementaryKernel.Kernel q),
          c (a • x) = A.augmentation a * c x) → HasLiftingForAt f L p q) :
    IsFormallyVersalAt f L p := by
  rw [isFormallyVersalAt_iff_elementary]
  intro A B q hq
  exact hasLiftingForAt_of_elementary_of_principal f L p hP _ q hq rfl

/-- Formal versality of an actual family over an affine base from ring-map lifting along
principal elementary surjections and lifting along the dual numbers (Stacks Lemma 90.13.2,
in the form used here). -/
theorem isFormallyVersalAt_of_ringLifting
    (hRL : ∀ {A B : ArtinianTest k K} (q : A ⟶ B), ArtinianTest.IsElementarySurjection q →
      ∀ (c : ArtinianTest.ElementaryKernel.Kernel q ≃+ K),
        (∀ (a : A.algebra) (x : ArtinianTest.ElementaryKernel.Kernel q),
          c (a • x) = A.augmentation a * c x) →
      ∀ (N : LineBundle ((relativeSpace f).obj (ArtinianTest.base A)))
        (y : FiberPoints f L N (Over.mk (ArtinianTest.baseMap q))),
        ArtinianTest.reduction B ≫ y.1 = p →
          ∃ u : ArtinianTest.base A ⟶ affineBase k H, ArtinianTest.baseMap q ≫ u = y.1)
    (hTL : HasLiftingForAt f L p (ArtinianTest.dualReduction k K)) :
    IsFormallyVersalAt f L p :=
  isFormallyVersalAt_of_principal f L p fun q hq c hc ↦
    hasLiftingForAt_of_principal f L p q hq c hc (hRL q hq c hc) hTL

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPrincipalLifting
