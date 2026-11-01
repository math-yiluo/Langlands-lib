import Langlands.Representation.Derivative.RightMixedLevel
import Langlands.Representation.Derivative.RestrictionBridge
import Langlands.Representation.Derivative.MirabolicProductRestrictionStatement

/-!
# Homogeneity of the restriction of a binary product

BZ77 4.13(a) gives a short exact sequence
`0 → (D|P) × P' → (D × P')|P → D × (P'|P) → 0`. If the restriction of `D` has a
single nonzero derivative, of order `s + 1`, and `D^(s+1) × P'|P` is homogeneous,
then every nonzero subrepresentation meeting the first term has the level of the
first term, and the last term has no larger level (BZ77 4.14(a)). A nonzero
subrepresentation that does not meet the first term injects into the last term;
excluding this situation (the second case of Zelevinsky's 6.3) gives homogeneity.
All lower inputs are explicit hypotheses.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

namespace RestrictedProductLevel

open LevelCalculus RightMixedLevel MirabolicProductRestriction

/-! ## Comparisons across ranks and casts -/

section Comparison

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem level_le_of_imp_of_rank {N M : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic M F.Carrier)),
      (∀ k, HasNonzeroDerivative T ψ A k → HasNonzeroDerivative T ψ B k) →
        level T ψ A ≤ level T ψ B := by
  intro A B h
  by_cases h0 : level T ψ A = 0
  · rw [h0]
    exact Nat.zero_le _
  · exact le_level_of_hasNonzeroDerivative T ψ B (h _ (hasNonzeroDerivative_level T ψ A h0))

end Comparison

/-! ## Levels of left mixed products (BZ77 4.14(a)) -/

section LeftLevel

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hLD : LeftMixedProductDerivative.{uF, uV} F T)
include hLD

/-- A nonzero derivative of `ρ × τ` comes from a nonzero derivative of `τ`. -/
theorem hasNonzeroDerivative_of_leftMixed {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)) (i : ℕ),
      HasNonzeroDerivative T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) i →
        HasNonzeroDerivative T ψ τ i := by
  let _ := T.topology
  rintro ρ τ i ⟨hi, h⟩
  by_cases hir : i ≤ r + 1
  · obtain ⟨e⟩ := hLD.1 ψ k r i ⟨hi.1, hir⟩
    have h1 : Nontrivial ((T.binaryNormalizedProductFunctor k (r + 1 - i)).obj
        (ρ, (mirabolicDerivativeOfOrder T ψ r i ⟨hi.1, hir⟩).obj τ)) :=
      (nontrivial_iff_of_iso (e.app (ρ, τ))).mp
        ((RestrictionBridge.nontrivial_generalLinearRankCast_iff T _ _).mpr h)
    refine ⟨⟨hi.1, hir⟩, ?_⟩
    by_contra h2
    rw [not_nontrivial_iff_subsingleton] at h2
    exact not_subsingleton _ (ProductVanishing.subsingleton_binary T
      (ρ, (mirabolicDerivativeOfOrder T ψ r i ⟨hi.1, hir⟩).obj τ) (Or.inr h2))
  · exact absurd h (not_nontrivial_iff_subsingleton.mpr (hLD.2 ψ k r i hi (by omega) ρ τ))

/-- If `ρ ≠ 0`, every nonzero derivative of `τ` gives one of `ρ × τ`. -/
theorem hasNonzeroDerivative_leftMixed {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)), Nontrivial ρ → ∀ i : ℕ,
      HasNonzeroDerivative T ψ τ i →
        HasNonzeroDerivative T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) i := by
  let _ := T.topology
  rintro ρ τ hρ i ⟨hi, h⟩
  obtain ⟨e⟩ := hLD.1 ψ k r i hi
  have h1 : Nontrivial ((T.binaryNormalizedProductFunctor k (r + 1 - i)).obj
      (ρ, (mirabolicDerivativeOfOrder T ψ r i hi).obj τ)) :=
    ProductVanishing.nontrivial_binary T _
  refine ⟨⟨hi.1, by omega⟩, ?_⟩
  exact (RestrictionBridge.nontrivial_generalLinearRankCast_iff T
    (show k + r + 1 - i = k + (r + 1 - i) by omega) _).mp
      ((nontrivial_iff_of_iso (e.app (ρ, τ))).mpr h1)

theorem level_leftMixed_le {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)),
      level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) ≤ level T ψ τ :=
  fun ρ τ => level_le_of_imp_of_rank T ψ _ _ (hasNonzeroDerivative_of_leftMixed T ψ hLD ρ τ)

theorem le_level_leftMixed {k r : ℕ} :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)), Nontrivial ρ →
      level T ψ τ ≤ level T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)) :=
  fun ρ τ hρ => level_le_of_imp_of_rank T ψ _ _ (hasNonzeroDerivative_leftMixed T ψ hLD ρ τ hρ)

end LeftLevel

/-! ## The restricted binary product -/

section Main

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
  (hD : RightMixedProductPhiMinusDetection.{uF, uV} F T)
  (hS : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
  (hB : MirabolicProductMinus.RightPhiBoundary.{uF, uV} F T)
  (hR : MirabolicProductRestrictionStatement.{uF, uV} F T)
  (hLD : LeftMixedProductDerivative.{uF, uV} F T)
include hE hD hS hB hR hLD

/-- If `D|P` has a single nonzero derivative, of order `s + 1`, and
`D^(s+1) × P'|P` is homogeneous, then `(D × P')|P` is homogeneous unless some
nonzero representation injects both into `(D × P')|P` and into `D × (P'|P)`. -/
theorem isHomogeneous_restrictedProduct (m n n' s : ℕ) (hm : m = n' + s) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))
      (P : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
      (∀ j, HasNonzeroDerivative T ψ ((generalLinearRestriction T m).obj D) j → j = s + 1) →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor n' n).obj
        ((mirabolicDerivative T ψ n' s).obj
          ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D)),
          (generalLinearRestriction T n).obj P)) →
      (∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
          (f : W ⟶ (restrictedProduct T m n).obj (D, P))
          (g : W ⟶ (restrictionQuotient T m n).obj (D, P)),
          Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
            Nontrivial W → False) →
      IsHomogeneous T ψ ((restrictedProduct T m n).obj (D, P)) := by
  let _ := T.topology
  intro D P hDj hY hC2
  obtain ⟨i, q, hiq⟩ := hR m n
  obtain ⟨hi, hex, hq⟩ := hiq (D, P)
  have hσ : ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
      (f : W ⟶ (restrictionSubobject T m n).obj (D, P)), Function.Injective (SmoothRep.hom f) →
        Nontrivial W → level T ψ W = level T ψ ((T.leftMixedProductFunctor n' n).obj
          ((mirabolicDerivative T ψ n' s).obj
            ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D)),
            (generalLinearRestriction T n).obj P)) + (s + 1) :=
    fun W f hf hW => level_of_injective_rightMixed T ψ hE hD hS hB n n' s m hm P
      ((generalLinearRestriction T m).obj D) hDj hY (m + n + 1) _ W f hf hW
  apply isHomogeneous_of_forall_injective T ψ _ (level T ψ ((T.leftMixedProductFunctor n' n).obj
    ((mirabolicDerivative T ψ n' s).obj
      ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D)),
      (generalLinearRestriction T n).obj P)) + (s + 1))
  intro W f hf hW
  by_cases h1 : comap f (SmoothRep.hom (i.app (D, P))).range = ⊥
  · exfalso
    refine hC2 W f (f ≫ q.app (D, P)) hf ?_ hW
    intro x y hxy
    have h2 : x - y ∈ (comap f (SmoothRep.hom (i.app (D, P))).range).toSubmodule := by
      rw [mem_comap]
      change SmoothRep.hom f (x - y) ∈ LinearMap.range (SmoothRep.hom (i.app (D, P))).toLinearMap
      rw [hex, LinearMap.mem_ker]
      change SmoothRep.hom (q.app (D, P)) (SmoothRep.hom f (x - y)) = 0
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr hxy
    rw [h1] at h2
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp h2)
  · have hW1 := subrepresentation_nontrivial _ h1
    let g := comapMap f (SmoothRep.hom (i.app (D, P))).range ≫ (isoRange (i.app (D, P)) hi).inv
    have hg : Function.Injective (SmoothRep.hom g) :=
      (iso_hom_injective (isoRange (i.app (D, P)) hi).symm).comp (comapMap_injective f _ hf)
    have hlev1 := hσ _ g hg hW1
    have hσne : Nontrivial ((restrictionSubobject T m n).obj (D, P)) :=
      nontrivial_of_injective g hg
    have hlevσ := hσ _ (𝟙 _) (fun _ _ h => h) hσne
    have hlow := level_le_of_injective T ψ hE (SmoothRep.subtype W _)
      (SmoothRep.subtype_injective W (comap f (SmoothRep.hom (i.app (D, P))).range))
    have hup1 := level_le_of_injective T ψ hE f hf
    have hup2 := level_le_max_of_isShortExact T ψ hE
      (⟨hi, hq, hex⟩ : IsShortExact (i.app (D, P)) (q.app (D, P)))
    have hDne : Nontrivial ((generalLinearRestriction T m).obj D) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have h' := mirabolicRankCast_obj_subsingleton T (show (n + 1) + m = m + n + 1 by omega) _
        (ProductVanishing.subsingleton_rightMixed T ((generalLinearRestriction T m).obj D, P)
          (Or.inl h))
      exact (not_nontrivial_iff_subsingleton.mpr h') hσne
    have hQ : Nontrivial ((mirabolicDerivative T ψ n' s).obj
        ((mirabolicRankCast T hm).obj ((generalLinearRestriction T m).obj D))) := by
      have hpos := level_pos T ψ ((generalLinearRestriction T m).obj D)
      have hl := hasNonzeroDerivative_level T ψ _ hpos.ne'
      rw [hDj _ hl] at hl
      exact (hasNonzeroDerivative_succ_iff_cast T ψ hm _).mp hl
    have hτ1 : level T ψ ((restrictionQuotient T m n).obj (D, P)) ≤
        level T ψ ((generalLinearRestriction T n).obj P) :=
      (level_mirabolicRankCast T ψ (show (m + 1) + n = m + n + 1 by omega)
        ((T.leftMixedProductFunctor (m + 1) n).obj
          (D, (generalLinearRestriction T n).obj P))).le.trans
        (level_leftMixed_le T ψ hLD _ _)
    have hτ2 := le_level_leftMixed T ψ hLD _ ((generalLinearRestriction T n).obj P) hQ
    have hup3 := hup2.trans (max_le hlevσ.le (hτ1.trans (hτ2.trans (Nat.le_add_right _ _))))
    omega

end Main

end RestrictedProductLevel

end Langlands.Derivative
