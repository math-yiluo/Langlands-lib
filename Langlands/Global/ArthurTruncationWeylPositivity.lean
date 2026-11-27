import Langlands.Global.ArthurTruncationRadicalInvariance
import Langlands.Global.AdelicEisensteinDoubleCosetsProof
import Langlands.GroupScheme.Rational.TitsStandardParabolic

/-! # Positivity of the transported weight on a Bruhat integration orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily AdelicGroupPoints ArthurParabolicSpaces
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "H" => height hi hK hρ
local notation "λ₀" => fundamentalWeight hG hi hν D
local notation "W" => relativeWeylGroup i
local notation "N₀" => AdelicSubgroupPoints.adelicPoints F G
  (SubgroupFunctor.range (Standard.unipotentHom i ν ∅))
local notation "aPoint" => innerAdelicPoint F G

/-- Rational left translation by a standard parabolic preserves every full
fundamental weight indexed outside its simple roots. -/
theorem pair_fundamentalWeight_parabolicRational_mul {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν) (β : SimpleRoot i ν) (hβ : β.val ∉ S)
    {r : A} (hr : r ∈ rationalImage F (Standard.parabolicHom i ν S)) (x : A) :
    pair T (λ₀ β) (H (r * x)) = pair T (λ₀ β) (H x) := by
  simp only [pair_fundamentalWeight hG hi hν D]
  have hz := fullWeight_eq_zero_of_mem_corootSpan hG hi hν D hS ⟨β.2, hβ⟩
    (height_sub_mem_span hG hi hν D hK hρ hS ((mem_parabolicRationalImage_iff _ _).mpr hr) x)
  rwa [map_sub, sub_eq_zero] at hz

/-- Sufficient regularity absorbs the bounded Weyl height error except for terms
in the stabilizing maximal parabolic Weyl subgroup, where covariance is exact. -/
theorem exists_regular_weylPositivity [Fintype (SimpleRoot i ν)] [Fintype W]
    (n : W → normalizerPoints i) (hn : ∀ w, (QuotientGroup.mk (n w) : W) = w)
    (hbound : ∀ (β : SimpleRoot i ν) (w : W), ∃ B : ℝ, 0 ≤ B ∧
      ∀ (v : N₀) (y : A), pair T (λ₀ β) (H y) ≤
        pair T (relativeWeylFullRealAction i w⁻¹ (λ₀ β))
          (H ((aPoint (n w).val)⁻¹ * (v : A) * y)) + B) :
    ∃ C : ℝ, ∀ Tp : V T, (∀ a ∈ simpleRelativeRoots i ν, C < eval T a Tp) →
      ∀ (β : SimpleRoot i ν) (w : W) (v : N₀) (y : A),
        0 < pair T (λ₀ β) (H y - Tp) →
        0 < pair T (relativeWeylFullRealAction i w⁻¹ (λ₀ β))
          (H ((aPoint (n w).val)⁻¹ * (v : A) * y) - Tp) := by
  classical
  choose B hB hineq using hbound
  let C : ℝ := ∑ a : SimpleRoot i ν × W, B a.1 a.2
  have hC : 0 ≤ C := Finset.sum_nonneg fun a _ => hB a.1 a.2
  have hBC (β : SimpleRoot i ν) (w : W) : B β w ≤ C :=
    Finset.single_le_sum (f := fun a : SimpleRoot i ν × W => B a.1 a.2)
      (fun a _ => hB a.1 a.2) (Finset.mem_univ (β, w))
  refine ⟨C, fun Tp hTp β w v y hy => ?_⟩
  let S := simpleRelativeRoots i ν \ {β.val}
  let W₁ := standardRelativeWeylGroup i ν S
  let x := λ₀ β
  let z := (aPoint (n w).val)⁻¹ * (v : A) * y
  by_cases hw : w⁻¹ ∈ W₁
  · have hS : S ⊆ simpleRelativeRoots i ν := Set.sdiff_subset
    have hβ : β.val ∉ S := fun h => h.2 rfl
    have hf := fundamentalWeight_fixed_of_mem_maximalWeyl hG hi hν D β hw
    have hnr : (n w).val ∈ standardParabolicPoints i ν S :=
      coe_mem_standardParabolicPoints_of_mk_mem i ν S
        (by rw [hn]; exact W₁.inv_mem_iff.mp hw)
    have hrat : aPoint (n w).val ∈ rationalImage F (Standard.parabolicHom i ν S) := by
      rw [rationalImage_eq_map_range, (Standard.isRepresentedBy_parabolicHom i ν S).2]
      exact ⟨_, hnr, principalPoint_eq_innerAdelicPoint F G _⟩
    have hp := pair_fundamentalWeight_parabolicRational_mul hG hi hν D hK hρ hS β hβ
      ((rationalImage F (Standard.parabolicHom i ν S)).inv_mem hrat) ((v : A) * y)
    have huv := height_radical_mul hG hi hν hK hρ (S := ∅) (Set.empty_subset _) v y
    have hz : pair T x (H z) = pair T x (H y) := by
      simpa only [z, mul_assoc, huv] using hp
    change 0 < pair T (relativeWeylFullRealAction i w⁻¹ x) (H z - Tp)
    rw [hf, map_sub, hz, ← map_sub]
    exact hy
  · have hd := (fundamentalWeight_displacement hG hi hν D β Tp C hC hTp w⁻¹).2 hw
    have hle := hineq β w v y
    change C < pair T (x - relativeWeylFullRealAction i w⁻¹ x) Tp at hd
    change pair T x (H y) ≤ pair T (relativeWeylFullRealAction i w⁻¹ x) (H z) + B β w at hle
    change 0 < pair T x (H y - Tp) at hy
    change 0 < pair T (relativeWeylFullRealAction i w⁻¹ x) (H z - Tp)
    rw [map_sub, LinearMap.sub_apply] at hd
    rw [map_sub] at hy ⊢
    linarith [hBC β w]

end Langlands.Global.ArthurTruncation.Idempotence
