import Langlands.AllFieldBZ.Representation.Derivative.LevelCalculus
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.AllFieldBZ.Representation.Derivative.MixedProductDerivativeStatement
import Langlands.AllFieldBZ.Representation.Derivative.ProductVanishing
import Langlands.Representation.Derivative.RightMixedLevel

/-!
# All-field port of `Langlands.Representation.Derivative.RightMixedLevel`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.RightMixedLevel` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding HasNonzeroDerivative IsHomogeneous LeftMixedProductDerivative LeftMixedProductDerivativeIso LeftMixedProductDerivativeVanishing MirabolicDerivativeDetection MirabolicProductMinusCompatibilityStatement RightMixedProductPhiMinusDetection generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton le_level_of_hasNonzeroDerivative level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeDetection mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

variable {F : LocalFieldPackage.{uF}}

namespace RightMixedLevel
open Langlands.Derivative.RightMixedLevel hiding isHomogeneous_mirabolicRankCast level_eq_of_phiMinus_injective level_eq_succ_of_phiMinus level_of_injective_rightMixed level_of_injective_rightMixed_zero mirabolicDerivative_zero_cast_obj nontrivial_phiMinus_of_injective phiMinus_cast_map_injective
open Langlands.Derivative.LevelCalculus hiding hasNonzeroDerivative_iff_of_iso hasNonzeroDerivative_level hasNonzeroDerivative_of_injective hasNonzeroDerivative_succ_iff hasNonzeroDerivative_succ_iff_cast isHomogeneous_of_forall_injective isHomogeneous_of_iso level_eq_level_phiMinus_succ level_eq_of_isHomogeneous level_eq_of_iso level_le_level_phiMinus_succ level_le_max_of_isShortExact level_le_of_imp level_le_of_injective level_le_one_of_subsingleton_phiMinus level_mirabolicRankCast level_pos mapsShortExact_mirabolicDerivative mapsShortExact_mirabolicDerivativeOfOrder mapsShortExact_mirabolicRankCast mapsShortExact_phiMinusIterate mirabolicDerivative_succ_cast_obj nontrivial_mirabolicDerivative_cast_congr nontrivial_of_hasNonzeroDerivative nontrivial_phiMinus_iff
open Langlands.AllFieldBZ.Derivative.LevelCalculus
/-! ## Short exact sequences with a zero end -/

section Maps
variable {G : Type*} [Group G] [TopologicalSpace G]

end Maps
/-! ## Rank casts and one `Φ⁻` step -/

section Cast
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem isHomogeneous_mirabolicRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      IsHomogeneous T ψ X → IsHomogeneous T ψ ((mirabolicRankCast T h).obj X) := by
  subst h
  exact fun _ hX => hX

theorem mirabolicDerivative_zero_cast_obj {r : ℕ} (h : r = r + 0) :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier),
      (mirabolicDerivative T ψ r 0).obj ((mirabolicRankCast T h).obj B) =
        (Mirabolic.psiMinus T r).obj B :=
  fun _ => rfl

/-- The level drops by one under `Φ⁻` once the `Φ⁻`-image is nonzero. -/
theorem level_eq_succ_of_phiMinus {a M : ℕ} (h : a = M + 1) :
    letI := T.topology
    ∀ W : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      Nontrivial ((Mirabolic.phiMinus T ψ M).obj ((mirabolicRankCast T h).obj W)) →
        level T ψ W = level T ψ ((Mirabolic.phiMinus T ψ M).obj ((mirabolicRankCast T h).obj W)) + 1 := by
  intro W hW
  rw [← Langlands.AllFieldBZ.Derivative.LevelCalculus.level_mirabolicRankCast T ψ h W]
  exact Langlands.AllFieldBZ.Derivative.LevelCalculus.level_eq_level_phiMinus_succ T ψ _ (Langlands.AllFieldBZ.Derivative.LevelCalculus.level_pos T ψ _)

theorem phiMinus_cast_map_injective (hE : Mirabolic.MinusExactnessStatement.{uF, uV} F T)
    {a M : ℕ} (h : a = M + 1) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier)} (f : X ⟶ Y),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective
          (SmoothRep.hom ((Mirabolic.phiMinus T ψ M).map ((mirabolicRankCast T h).map f))) := by
  let _ := T.topology
  intro X Y f hf
  exact map_injective_of_exact
    (mapsShortExact_comp (Langlands.AllFieldBZ.Derivative.LevelCalculus.mapsShortExact_mirabolicRankCast T h) (hE.2.2.2 M ψ)) f hf

/-- BZ77 4.13(d), transported from an invariant subspace to an injective
intertwiner. -/
theorem nontrivial_phiMinus_of_injective (hD : RightMixedProductPhiMinusDetection.{uF, uV} F T)
    {k r : ℕ} :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
      {W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + 1 + r) F.Carrier)}
      (f : W ⟶ (T.rightMixedProductFunctor (k + 1) r).obj (B, A)),
      Function.Injective (SmoothRep.hom f) → Nontrivial W →
        Nontrivial ((Mirabolic.phiMinus T ψ (k + r)).obj
          ((mirabolicRankCast T (Nat.add_right_comm k 1 r)).obj W)) := by
  let _ := T.topology
  intro B A W f hf hW
  have := hD ψ k r B A _ (range_ne_bot f hf)
  exact (nontrivial_iff_of_iso ((mirabolicRankCast T (Nat.add_right_comm k 1 r) ⋙
    Mirabolic.phiMinus T ψ (k + r)).mapIso (isoRange f hf))).mpr this

end Cast
/-! ## The level of subrepresentations of `B × A` -/

section Level
variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The common last step: if `Φ⁻ W` injects into a homogeneous representation
`X`, then `λ(W) = λ(X) + 1`. -/
theorem level_eq_of_phiMinus_injective {a M : ℕ} (h : a = M + 1) :
    letI := T.topology
    ∀ (W : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier))
      (X : SmoothRep.{0, uF, uV} ℂ (mirabolic M F.Carrier)),
      IsHomogeneous T ψ X →
      ∀ g : (Mirabolic.phiMinus T ψ M).obj ((mirabolicRankCast T h).obj W) ⟶ X,
        Function.Injective (SmoothRep.hom g) →
        Nontrivial ((Mirabolic.phiMinus T ψ M).obj ((mirabolicRankCast T h).obj W)) →
          level T ψ W = level T ψ X + 1 := by
  let _ := T.topology
  intro W X hX g hg hW
  rw [level_eq_succ_of_phiMinus T ψ h W hW, Langlands.AllFieldBZ.Derivative.LevelCalculus.level_eq_of_isHomogeneous T ψ hX g hg hW]

variable (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
  (hD : RightMixedProductPhiMinusDetection.{uF, uV} F T)
  (hS : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
  (hB : MirabolicProductMinus.RightPhiBoundary.{uF, uV} F T)
include hE hD hS hB

/-- If the only nonzero derivative of `B` is the order-one one, every nonzero
subrepresentation of `B × A` has level `1 + λ(Ψ⁻B × A|P)`, provided this left
mixed product is homogeneous. -/
theorem level_of_injective_rightMixed_zero (k n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)),
      (∀ j, HasNonzeroDerivative T ψ B j → j = 1) →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor n k).obj
        ((Mirabolic.psiMinus T n).obj B, (generalLinearRestriction T k).obj A)) →
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + 1 + n) F.Carrier))
        (f : W ⟶ (T.rightMixedProductFunctor (k + 1) n).obj (B, A)),
        Function.Injective (SmoothRep.hom f) → Nontrivial W →
          level T ψ W = level T ψ ((T.leftMixedProductFunctor n k).obj
            ((Mirabolic.psiMinus T n).obj B, (generalLinearRestriction T k).obj A)) + 1 := by
  let _ := T.topology
  intro A B hBj hY W f hf hW
  have hW' := nontrivial_phiMinus_of_injective T ψ hD B A f hf hW
  have hf' := phiMinus_cast_map_injective T ψ hE (Nat.add_right_comm k 1 n) f hf
  have hY' := isHomogeneous_mirabolicRankCast T ψ (Nat.add_comm n k) _ hY
  rw [← Langlands.AllFieldBZ.Derivative.LevelCalculus.level_mirabolicRankCast T ψ (Nat.add_comm n k) ((T.leftMixedProductFunctor n k).obj
    ((Mirabolic.psiMinus T n).obj B, (generalLinearRestriction T k).obj A))]
  cases n with
  | zero =>
    obtain ⟨e⟩ := hB ψ k
    exact level_eq_of_phiMinus_injective T ψ (Nat.add_right_comm k 1 0) W _ hY'
      ((Mirabolic.phiMinus T ψ (k + 0)).map
        ((mirabolicRankCast T (Nat.add_right_comm k 1 0)).map f) ≫ (e.app (B, A)).hom)
      ((iso_hom_injective (e.app (B, A))).comp hf') hW'
  | succ R =>
    obtain ⟨i, q, hiq⟩ := hS ψ k R
    obtain ⟨-, hex, -⟩ := hiq (B, A)
    have hB0 : Subsingleton ((Mirabolic.phiMinus T ψ R).obj B) := by
      rw [← not_nontrivial_iff_subsingleton, Langlands.AllFieldBZ.Derivative.LevelCalculus.nontrivial_phiMinus_iff T ψ B]
      intro hlt
      have := hBj _ (Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_level T ψ B (by omega))
      omega
    have : Subsingleton ((MirabolicProductMinus.rightPhiSubobject T ψ k R).obj (B, A)) :=
      mirabolicRankCast_obj_subsingleton T _ _
        (ProductVanishing.subsingleton_rightMixed T _ (Or.inl hB0))
    exact level_eq_of_phiMinus_injective T ψ (Nat.add_right_comm k 1 (R + 1)) W _ hY'
      ((Mirabolic.phiMinus T ψ (k + (R + 1))).map
        ((mirabolicRankCast T (Nat.add_right_comm k 1 (R + 1))).map f) ≫ q.app (B, A))
      ((injective_of_range_eq_ker _ _ hex).comp hf') hW'

/-- If the only nonzero derivative of `B` on `P_r`, with `r = n + s`, has order
`s + 1`, every nonzero subrepresentation of `B × A` (read through any rank
cast) has level `λ(B^(s+1) × A|P) + s + 1`, provided this left mixed product
is homogeneous. -/
theorem level_of_injective_rightMixed (k n : ℕ) :
    letI := T.topology
    ∀ (s r : ℕ) (hr : r = n + s) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier)),
      (∀ j, HasNonzeroDerivative T ψ B j → j = s + 1) →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor n k).obj
        ((mirabolicDerivative T ψ n s).obj ((mirabolicRankCast T hr).obj B),
          (generalLinearRestriction T k).obj A)) →
      ∀ (L : ℕ) (hL : k + 1 + r = L)
        (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic L F.Carrier))
        (f : W ⟶ (mirabolicRankCast T hL).obj
          ((T.rightMixedProductFunctor (k + 1) r).obj (B, A))),
        Function.Injective (SmoothRep.hom f) → Nontrivial W →
          level T ψ W = level T ψ ((T.leftMixedProductFunctor n k).obj
            ((mirabolicDerivative T ψ n s).obj ((mirabolicRankCast T hr).obj B),
              (generalLinearRestriction T k).obj A)) + (s + 1) := by
  let _ := T.topology
  intro s
  induction s with
  | zero =>
    intro r hr A B hBj hY L hL W f hf hW
    have hn : r = n := hr
    subst hn hL
    rw [mirabolicDerivative_zero_cast_obj T ψ hr B] at hY ⊢
    exact level_of_injective_rightMixed_zero T ψ hE hD hS hB k _ A B hBj hY W f hf hW
  | succ s ih =>
    intro r hr A B hBj hY L hL W f hf hW
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hr' : r = n + s := by omega
    subst hL
    obtain ⟨i, q, hiq⟩ := hS ψ k r
    obtain ⟨hi, hex, -⟩ := hiq (B, A)
    have hpsi : Subsingleton ((Mirabolic.psiMinus T (r + 1)).obj B) := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hB1
      have h1 : HasNonzeroDerivative T ψ B 1 := by
        refine ⟨⟨Nat.one_pos, by omega⟩, ?_⟩
        rw [mirabolicDerivativeOfOrder_one]
        exact hB1
      have := hBj 1 h1
      omega
    have hQ : Subsingleton ((MirabolicProductMinus.rightPhiQuotient T k (r + 1)).obj (B, A)) :=
      mirabolicRankCast_obj_subsingleton T _ _
        (ProductVanishing.subsingleton_leftMixed T _ (Or.inl hpsi))
    have := isIso_of_bijective (i.app (B, A)) hi (surjective_of_range_eq_ker _ _ hex)
    have hW' := nontrivial_phiMinus_of_injective T ψ hD B A f hf hW
    have hf' := phiMinus_cast_map_injective T ψ hE (Nat.add_right_comm k 1 (r + 1)) f hf
    have hB' : ∀ j, HasNonzeroDerivative T ψ ((Mirabolic.phiMinus T ψ r).obj B) j →
        j = s + 1 := by
      intro j hj
      have hj0 : 0 < j := hj.1.1
      have := hBj (j + 1) ((Langlands.AllFieldBZ.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff (M := r) T ψ B hj0).mpr hj)
      omega
    let g₁ : (Mirabolic.phiMinus T ψ (k + (r + 1))).obj
        ((mirabolicRankCast T (Nat.add_right_comm k 1 (r + 1))).obj W) ⟶
          (MirabolicProductMinus.rightPhiProduct T ψ k (r + 1)).obj (B, A) :=
      (Mirabolic.phiMinus T ψ (k + (r + 1))).map
        ((mirabolicRankCast T (Nat.add_right_comm k 1 (r + 1))).map f)
    let g : (Mirabolic.phiMinus T ψ (k + (r + 1))).obj
        ((mirabolicRankCast T (Nat.add_right_comm k 1 (r + 1))).obj W) ⟶
          (MirabolicProductMinus.rightPhiSubobject T ψ k r).obj (B, A) :=
      g₁ ≫ inv (i.app (B, A))
    have hg : Function.Injective (SmoothRep.hom g) :=
      (iso_hom_injective (asIso (i.app (B, A))).symm).comp hf'
    rw [Langlands.AllFieldBZ.Derivative.LevelCalculus.mirabolicDerivative_succ_cast_obj T ψ hr hr' B] at hY ⊢
    have key := ih r hr' A ((Mirabolic.phiMinus T ψ r).obj B) hB' hY (k + r + 1)
      (Nat.succ_add k r) _ g hg hW'
    rw [level_eq_succ_of_phiMinus T ψ (Nat.add_right_comm k 1 (r + 1)) W hW', key]
    omega

end Level
end RightMixedLevel
end Langlands.AllFieldBZ.Derivative
