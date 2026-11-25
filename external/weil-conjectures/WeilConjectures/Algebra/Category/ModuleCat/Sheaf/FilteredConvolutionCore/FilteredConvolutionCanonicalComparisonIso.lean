/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore
public import Mathlib.CategoryTheory.Category.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionTensorCokernel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionFlatMono
public import WeilConjectures.Algebra.Homology.FilteredComplexGradedProjection
import WeilConjectures.Algebra.Homology.DegreewiseMonoCriterion
public import Mathlib.Data.Int.Interval

/-! Isomorphism of the canonical convolution graded comparison. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.FilteredConvolutionCore
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- The tensor product of two maps of complexes on a summand of the total tensor. -/
theorem ι_tensorHom_f {K₁ K₂ L₁ L₂ : Complex R} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ i j n h ≫ (f ⊗ₘ g).f n =
      (f.f i ⊗ₘ g.f j) ≫ HomologicalComplex.ιTensorObj L₁ L₂ i j n h := by
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp [tensorHom_def]

/-- A smaller filtration step dies in the quotient by a larger one. -/
theorem arrow_comp_cokernelπ_eq_zero {K : Complex R} (G : DecreasingFiltration K) {k l : ℤ}
    (h : l ≤ k) : (G.F k).arrow ≫ cokernel.π (G.F l).arrow = 0 := by
  rw [← Subobject.ofLE_arrow (G.antitone h), Category.assoc, cokernel.condition, comp_zero]

/-- The summand `grᵗ P ⊗ Q / Gʳ⁻ᵗ⁺¹ Q` of the target of the degreewise test map. -/
abbrev testTarget {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (r t : ℤ) : Complex R :=
  F.gradedPiece t ⊗ cokernel (G.F (r - t + 1)).arrow

/-- The degree `n` test map `(P ⊗ Q)ⁿ ⟶ (∐ₜ grᵗ P ⊗ Q / Gʳ⁻ᵗ⁺¹ Q)ⁿ` built from
degreewise graded projections `s t i : Pⁱ ⟶ (grᵗ P)ⁱ`, summed over `t ∈ [a, b]`. It is not a map of
complexes, since the projections need not commute with the differential. -/
def testMap {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (s : ∀ t i : ℤ, P.X i ⟶ (F.gradedPiece t).X i) (a b r n : ℤ) :
    (P ⊗ Q).X n ⟶ (∐ testTarget F G r).X n :=
  ∑ t ∈ Finset.Icc a b, HomologicalComplex.mapBifunctorDesc (fun i j h ↦
    (s t i ⊗ₘ (cokernel.π (G.F (r - t + 1)).arrow).f j) ≫
      HomologicalComplex.ιTensorObj _ _ i j n h) ≫ (Sigma.ι (testTarget F G r) t).f n

theorem ι_testMap {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (s : ∀ t i : ℤ, P.X i ⟶ (F.gradedPiece t).X i) (a b r n i j : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj P Q i j n h ≫ testMap F G s a b r n =
      ∑ t ∈ Finset.Icc a b, (s t i ⊗ₘ (cokernel.π (G.F (r - t + 1)).arrow).f j) ≫
        HomologicalComplex.ιTensorObj _ _ i j n h ≫ (Sigma.ι (testTarget F G r) t).f n := by
  simp [testMap, Preadditive.comp_sum]

/-- The test map kills the generators `Fᵖ P ⊗ G^q Q` with `p + q > r`. -/
theorem tensorHom_f_comp_testMap_eq_zero {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (s : ∀ t i : ℤ, P.X i ⟶ (F.gradedPiece t).X i)
    (hs : ∀ t i p, t < p → (F.F p).arrow.f i ≫ s t i = 0) (a b r n p q : ℤ)
    (hpq : r + 1 ≤ p + q) :
    ((F.F p).arrow ⊗ₘ (G.F q).arrow).f n ≫ testMap F G s a b r n = 0 := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j h ↦ ?_
  rw [comp_zero, reassoc_of% (ι_tensorHom_f _ _ i j n h), ι_testMap, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun t _ ↦ ?_
  rw [tensorHom_comp_tensorHom_assoc]
  rcases lt_or_ge t p with hlt | hle
  · rw [hs t i p hlt, MonoidalPreadditive.zero_tensor, zero_comp]
  · rw [← HomologicalComplex.comp_f, arrow_comp_cokernelπ_eq_zero G (by omega),
      HomologicalComplex.zero_f, MonoidalPreadditive.tensor_zero, zero_comp]

/-- On the generator `Fᵖ P ⊗ Gʳ⁻ᵖ Q` the test map is the tensor of the graded projections,
followed by the inclusion `grʳ⁻ᵖ Q ⟶ Q / Gʳ⁻ᵖ⁺¹ Q` and the summand `p`. -/
theorem tensorHom_f_comp_testMap {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (s : ∀ t i : ℤ, P.X i ⟶ (F.gradedPiece t).X i) (a b : ℤ)
    (hPa : F.F a = ⊤) (hPb : F.F (b + 1) = ⊥)
    (hs₁ : ∀ t i, (F.F t).arrow.f i ≫ s t i = (F.gradedπ t).f i)
    (hs₂ : ∀ t i p, t < p → (F.F p).arrow.f i ≫ s t i = 0) (r n p : ℤ) :
    ((F.F p).arrow ⊗ₘ (G.F (r - p)).arrow).f n ≫ testMap F G s a b r n =
      ((F.gradedπ p ⊗ₘ G.gradedπ (r - p)) ≫
          (F.gradedPiece p ◁ G.gradedPieceToQuotient (r - p)) ≫
            Sigma.ι (testTarget F G r) p).f n := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j h ↦ ?_
  rw [reassoc_of% (ι_tensorHom_f _ _ i j n h), ι_testMap, Preadditive.comp_sum]
  have hterm : ∀ t ∈ Finset.Icc a b, t ≠ p →
      ((F.F p).arrow.f i ≫ s t i) ⊗ₘ ((G.F (r - p)).arrow.f j ≫
        (cokernel.π (G.F (r - t + 1)).arrow).f j) = 0 := by
    intro t _ hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [hs₂ t i p hlt, MonoidalPreadditive.zero_tensor]
    · rw [← HomologicalComplex.comp_f, arrow_comp_cokernelπ_eq_zero G (by omega),
        HomologicalComplex.zero_f, MonoidalPreadditive.tensor_zero]
  simp_rw [tensorHom_comp_tensorHom_assoc]
  by_cases hp : p ∈ Finset.Icc a b
  · rw [Finset.sum_eq_single_of_mem p hp (fun t ht hne ↦ by rw [hterm t ht hne, zero_comp])]
    rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id,
      HomologicalComplex.comp_f]
    erw [reassoc_of% (ι_tensorHom_f _ _ i j n h)]
    rw [← HomologicalComplex.comp_f (G.F (r - p)).arrow,
      ← G.gradedπ_gradedPieceToQuotient (r - p), hs₁ p i]
  · rw [Finset.sum_eq_zero (fun t ht ↦ by
      rw [hterm t ht (by rintro rfl; exact hp ht), zero_comp])]
    have hz : IsZero (F.gradedPiece p) := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hp
      rcases hp with hp | hp
      · exact F.isZero_gradedPiece_of_eq_top
          (top_unique (by rw [← hPa]; exact F.antitone (by omega)))
      · exact F.isZero_gradedPiece_of_eq_bot
          (le_bot_iff.1 (by rw [← hPb]; exact F.antitone (by omega)))
    have h0 : (F.gradedπ p).f i = 0 := by
      rw [hz.eq_of_tgt (F.gradedπ p) 0, HomologicalComplex.zero_f]
    rw [HomologicalComplex.comp_f]
    erw [reassoc_of% (ι_tensorHom_f _ _ i j n h)]
    rw [h0, MonoidalPreadditive.zero_tensor, zero_comp]

-- The bounds `hQc`, `hQd` on the second filtration are not needed for the proof.
set_option linter.unusedVariables false in
/-- Under finite bounds, termwise split projections in the first filtration and flat
first graded terms identify the canonical comparison with the associated graded
isomorphism.  The proof is the degreewise finite split calculation and exactness of
flat tensoring, followed by totalization and the Koszul differential check.
Source: Steps 3--6 of the proof of `lem-trf-filtered-convolution-graded-quotient`.
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
theorem canonical_comparison_isIso
    {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (a b c d : ℤ) (hPa : F.F a = ⊤) (hPb : F.F (b + 1) = ⊥)
    (hQc : G.F c = ⊤) (hQd : G.F (d + 1) = ⊥)
    (hSplit : ∀ p n : ℤ,
      IsSplitEpi ((F.complexQuotientπ p (p + 1) (by omega)).f n))
    (hFlat : ∀ p n : ℤ, IsFlatOnSite (R := R) ((F.gradedPiece p).X n))
    (H : DecreasingFiltration (P ⊗ Q)) (hH : ∀ r : ℤ, H.F r = level F G r)
    (r : ℤ) (α : gradedSource F G r ⟶ H.gradedPiece r)
    (hα : IsCanonical F G H r α) : IsIso α := by
  choose t ht₁ ht₂ using hα
  -- graded projections with the graded pieces as targets
  let πF (p : ℤ) := F.gradedπ p
  let πG (q : ℤ) := G.gradedπ q
  let πH := H.gradedπ r
  have ht₂' (p : ℤ) : (πF p ⊗ₘ πG (r - p)) ≫
      Sigma.ι (fun p : ℤ ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p)) p ≫ α = t p ≫ πH :=
    ht₂ p
  let u : (∐ fun p : ℤ ↦ (F.F p : Complex R) ⊗ (G.F (r - p) : Complex R)) ⟶
      gradedSource F G r :=
    Limits.Sigma.map fun p ↦ πF p ⊗ₘ πG (r - p)
  have : Epi u := by
    have (p : ℤ) : Epi (πF p ⊗ₘ πG (r - p)) := epi_tensorHom _ _
    exact ⟨fun g h w ↦ Sigma.hom_ext _ _ fun p ↦ (cancel_epi (πF p ⊗ₘ πG (r - p))).1
      (by simpa [u] using Sigma.ι _ p ≫= w)⟩
  have he : Sigma.desc t ≫ (H.F r).arrow =
      Sigma.desc fun p ↦ (F.F p).arrow ⊗ₘ (G.F (r - p)).arrow :=
    Sigma.hom_ext _ _ fun p ↦ by simp [ht₁]
  have hu : u ≫ α = Sigma.desc t ≫ πH :=
    Sigma.hom_ext _ _ fun p ↦ by simp [u, ← ht₂' p]
  have hepi : Epi α := by
    have : Epi (Sigma.desc t) := Abelian.epi_of_comp_arrow_eq (hH r) _ he
    have : Epi (u ≫ α) := by rw [hu]; exact epi_comp _ _
    exact epi_of_epi u α
  suffices hmono : Mono α from isIso_of_mono_of_epi α
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ ?_
  -- the degreewise graded projections of `P`
  choose s hs₁ hs₂ using F.exists_gradedProjection a hPa hSplit
  let mc : gradedSource F G r ⟶ ∐ testTarget F G r :=
    Limits.Sigma.map fun p ↦ F.gradedPiece p ◁ G.gradedPieceToQuotient (r - p)
  have : Mono mc := by
    have (p : ℤ) : Mono (F.gradedPiece p ◁ G.gradedPieceToQuotient (r - p)) :=
      mono_whiskerLeft_of_isFlatOnSite _ (hFlat p) _
    exact mono_sigmaMap_complex _
  have : Mono (mc.f n) := (HomologicalComplex.eval _ _ n).map_mono mc
  have : Epi (u.f n) := (HomologicalComplex.eval _ _ n).map_epi u
  refine Abelian.mono_of_comp_eq (u.f n) ((Sigma.desc t).f n)
    ((Subobject.ofLE _ _ (H.F_succ_le r)).f n) (πH.f n) _
    (HomologicalComplex.isColimitCokernelCoforkF (Subobject.ofLE _ _ (H.F_succ_le r)) n) (α.f n)
    (by rw [← HomologicalComplex.comp_f, hu, HomologicalComplex.comp_f])
    ((H.F r).arrow.f n) (testMap F G s a b r n) (mc.f n) ?_ ?_
  · rw [← Category.assoc, ← HomologicalComplex.comp_f, he, ← HomologicalComplex.comp_f]
    refine HomologicalComplex.sigma_X_hom_ext fun p ↦ ?_
    rw [← Category.assoc, ← HomologicalComplex.comp_f, Sigma.ι_comp_desc,
      tensorHom_f_comp_testMap F G s a b hPa hPb hs₁ hs₂, ← HomologicalComplex.comp_f]
    have hmc : Sigma.ι (fun p ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p)) p ≫ mc =
        (F.gradedPiece p ◁ G.gradedPieceToQuotient (r - p)) ≫ Sigma.ι (testTarget F G r) p :=
      Limits.Sigma.ι_map _ _
    congr 1
    simp only [u, Limits.Sigma.ι_map_assoc, hmc]
    rfl
  · rw [← Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow, hH (r + 1), level]
    let Φ' := Sigma.desc fun p : ℤ ↦ (F.F p).arrow ⊗ₘ (G.F (r + 1 - p)).arrow
    have : Epi ((factorThruImageSubobject Φ').f n) :=
      (HomologicalComplex.eval _ _ n).map_epi (factorThruImageSubobject Φ')
    rw [← cancel_epi ((factorThruImageSubobject Φ').f n), comp_zero, ← Category.assoc,
      ← HomologicalComplex.comp_f]
    erw [imageSubobject_arrow_comp]
    refine HomologicalComplex.sigma_X_hom_ext fun p ↦ ?_
    rw [comp_zero, ← Category.assoc, ← HomologicalComplex.comp_f, Sigma.ι_comp_desc]
    exact tensorHom_f_comp_testMap_eq_zero F G s hs₂ a b r n p _ (by omega)

end SheafOfModules.FilteredConvolutionCore
