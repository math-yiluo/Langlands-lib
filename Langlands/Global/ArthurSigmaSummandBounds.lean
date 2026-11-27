import Langlands.Global.ArthurTruncationExpansion
import Langlands.Global.ArthurAlternatingConstantTermDecay
import Langlands.Global.ArthurNormOneTruncation

/-! # Selecting and estimating supported representatives in the sigma sum -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory NumberField Set
open scoped Classical CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints ArthurParabolicSpaces AdelicSiegelFactors PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {K : Subgroup (AdelicGroupPoints F G)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i) (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "A" => AdelicGroupPoints F G
local notation "Γ" => rationalSubgroup F G
local notation "PImage(" R ")" => parabolicRationalImage
  (Standard.parabolicHom i ν (R : Set (characterLattice T)))
local notation "PΓ(" R ")" => parabolicRationalSubgroup F
  (Standard.parabolicHom i ν (R : Set (characterLattice T)))
local notation "PQuot(" R ")" => ParabolicRationalCosets F
  (Standard.parabolicHom i ν (R : Set (characterLattice T)))
local notation "H₀(" y ")" => height hi hK hρ y
local notation "σ₀" => ArthurRelative.sigma hG hi ν D

include hν in
private theorem sigma_height_mul_left {R S : J} (hRS : R ⊆ S) (hS : S ⊆ Δ) (Tp : V T)
    {z : A} (hz : z ∈ PImage(R)) (y : A) :
    σ₀ (R : Set (characterLattice T)) S (H₀(z * y) - Tp) =
      σ₀ (R : Set (characterLattice T)) S (H₀(y) - Tp) := by
  rw [arthurRelative_sigma_eq_sum hG hi hν D R S hS, arthurRelative_sigma_eq_sum hG hi hν D R S hS]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  obtain ⟨hQΔ, hSQ⟩ := Finset.mem_filter.mp hQ
  have hR₀ : (R : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun a ha =>
    (mem_simpleFinset hG hi).mp (hS (hRS ha))
  have hQ₀ : (Q : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun a ha =>
    (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hQΔ ha)
  have hzQ : z ∈ PImage(Q) := parabolicRationalImage_mono hG hi hν
    (show (R : Set (characterLattice T)) ⊆ Q from hRS.trans hSQ) hQ₀ hz
  rw [tau_height_mul_left parabolicSpacesComparison hG hi hν D hK hρ Tp _ hR₀ hz y,
    tauHat_height_mul_left hG hi hν D hK hρ (Finset.mem_powerset.mp hQΔ) hzQ Tp y]

include hν in
private theorem alternatingConstantTerm_mul_left {R S : J} (hS : S ⊆ Δ)
    (f : ContinuousRationalFunctions F G) {z : A} (hz : z ∈ PImage(R)) (y : A) :
    alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) (z * y) =
      alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f) y := by
  unfold alternatingConstantTerm
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPS, hRP⟩ := Finset.mem_filter.mp hP
  have hP₀ : (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun a ha =>
    (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp hPS ha))
  have hzP : z ∈ PImage(P) := parabolicRationalImage_mono hG hi hν
    (show (R : Set (characterLattice T)) ⊆ P from hRP) hP₀ hz
  rw [constantTerm_rationalImage_mul hG hi hν ((Finset.mem_powerset.mp hPS).trans hS) f hzP y]

variable (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
  (T₁ Tp : V T)

local notation "Ω" => compactPrefix F G T i ν (canonicalStandardFactors F G T i ν) C
local notation "P₀" => MonoidHom.range
  (ContinuousMonoidHom.toMonoidHom (map F _ G (Standard.parabolicHom i ν ∅)))
local notation "coeff" => siegelSigmaCoefficient hG hi D hK hρ C T₁ Tp

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem compactPrefix_subset_minimalParabolic : Ω ⊆ P₀ := by
  let Q := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
  rintro _ ⟨_, ⟨n, _, rfl⟩, _, ⟨m, _, rfl⟩, rfl⟩
  apply (mem_range_map_iff_of_isRepresentedBy F (Standard.isRepresentedBy_parabolicHom i ν ∅) _).mpr
  apply Subgroup.mul_mem
  · exact standardUnipotent_le_standardParabolic i ν ∅ Q
      (unipotent_mem_standard F G T i ν (canonicalStandardFactors F G T i ν) n)
  · exact standardLevi_le_standardParabolic i ν ∅ Q
      (levi_mem_standard F G T i ν (canonicalStandardFactors F G T i ν) m.val)

include hν in
private theorem exists_sigmaTorusRegion_of_mem {R S : J} (hC : C.compactSubgroup = K) {y : A}
    (hy : y ∈ truncatedSiegelSet hG hi D hK hρ C R T₁ Tp)
    (hσ : σ₀ (R : Set (characterLattice T)) S (H₀(y) - Tp) = 1) (hyN : y ∈ normOneSubgroup F G) :
    ∃ p ∈ Ω, ∃ a ∈ sigmaTorusRegion hG hi D hK hρ R S T₁ Tp, ∃ k ∈ C.compactSubgroup,
      p * positiveTorusMap F i a * k = y := by
  obtain ⟨n, hn, m, hm, a, ha, k, hk, he⟩ := (mem_siegelSet_iff hi hK hρ C R T₁ y).mp hy.1
  let nG := map F _ G (Standard.unipotentHom i ν ∅) n
  let mG := map F _ G (Standard.leviHom i ν ∅) m.val
  let H₁ := normOneSubgroup F G
  let aG := positiveTorusMap F i a
  have hnG : nG ∈ H₁ := unipotentPoints_le_normOne hG hi hν (empty_subset _)
    (show nG ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range
      (Standard.unipotentHom i ν ∅)) from ⟨n, rfl⟩)
  have hmG : mG ∈ H₁ := map_normOneSubgroup_le F _ G (Standard.leviHom i ν ∅) ⟨m.val, m.2, rfl⟩
  have hkG : k ∈ H₁ := compactSubgroup_le_normOneSubgroup F G C.compactSubgroup C.compact_compactSubgroup hk
  have haG : aG ∈ H₁ := by
    have hY : (nG * mG * aG) * k ∈ H₁ := he.symm ▸ hyN
    have hY' := H₁.mul_mem (H₁.inv_mem (H₁.mul_mem hnG hmG)) (H₁.mul_mem hY (H₁.inv_mem hkG))
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at hY'
  have hHy : H₀(y) = H₀(aG) := he ▸ height_siegel_product hG hi hν hK hρ n m a (hC ▸ hk)
  refine ⟨nG * mG, Set.mem_mul.mpr ⟨nG, ⟨n, hn, rfl⟩, mG, ⟨m, hm, rfl⟩, rfl⟩,
    a, ⟨ha, ?_, ?_, haG⟩, k, hk, he⟩
  · rw [← hHy]
    exact hy.2
  · rw [← hHy]
    exact hσ

include hν in
/-- Choose distinct rational representatives of the rational cosets for one
pair of standard parabolic indices, with a termwise height bound on the
corresponding translates of the input. -/
theorem exists_sigmaCoset_representatives_with_bound {N d : ℕ}
    (ρ : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hSmooth : SmoothOfRelativeDimension d G.X.hom)
    (hC : C.compactSubgroup = K) (R S : J) (hRS : R ⊆ S) (hS : S ⊆ Δ)
    (f : FinitePlotSmoothRationalFunctions F G) (hf : HasAdelicUniformModerateGrowth F G ρ hSmooth
      (adelicDifferentialCommutator_of_smooth F G hSmooth) f) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ normOneSubgroup F G,
      ∃ e : PQuot(R) ↪ RationalGroupPoints F G,
        ∀ c : PQuot(R),
          let y := ((Quotient.out c : Γ) : A) * x
          ‖(coeff R S y : ℂ) * alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f.val) y‖ *
            adelicHeight F G ρ (rational F G (e c) * x) ^ m ≤ B := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨B, hB, hDecay⟩ := alternatingConstantTerm_rapidDecay hG hi hν D hK hρ hSmooth ρ hN
    R S hRS hS T₁ Tp Ω (C.compactSubgroup : Set A) (isCompact_compactPrefix F G T i ν
      (canonicalStandardFactors F G T i ν) C) C.compact_compactSubgroup
    (compactPrefix_subset_minimalParabolic C) f hf m
  refine ⟨B, hB, fun x hx => ?_⟩
  let y (c : PQuot(R)) := ((Quotient.out c : Γ) : A) * x
  let g := alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G f.val)
  let b (c : PQuot(R)) := (coeff R S (y c) : ℂ) * g (y c)
  let H := adelicHeight F G ρ
  have hrep (c : PQuot(R)) : ∃ δ : Γ, Quotient.mk _ δ = c ∧ ‖b c‖ * H (δ.val * x) ^ m ≤ B := by
    by_cases hzero : coeff R S (y c) = 0
    · exact ⟨Quotient.out c, Quotient.out_eq c, by simpa only [b, hzero, Int.cast_zero, zero_mul, norm_zero] using hB⟩
    · have hF₁ : siegelIndicator hG hi D hK hρ C R T₁ Tp (y c) = 1 := by
        rcases siegelIndicator_eq_zero_or_one hG hi D hK hρ C T₁ Tp R (y c) with hz | hz
        · exact (hzero (by simp only [siegelSigmaCoefficient, hz, zero_mul])).elim
        · exact hz
      have hσ₁ : σ₀ (R : Set (characterLattice T)) S (H₀(y c) - Tp) = 1 := by
        rcases arthurRelative_sigma_eq_zero_or_one hG hi hν D R S hRS (H₀(y c) - Tp) with hz | hz
        · exact (hzero (by simp only [siegelSigmaCoefficient, hz, mul_zero])).elim
        · exact hz
      have hcoeff : coeff R S (y c) = 1 := by simp only [siegelSigmaCoefficient, hF₁, hσ₁, mul_one]
      have he : ∃ z ∈ PImage(R), z * y c ∈ truncatedSiegelSet hG hi D hK hρ C R T₁ Tp := by
        by_contra hn
        exact zero_ne_one (by simpa only [siegelIndicator, ite_eq_right hn] using hF₁)
      obtain ⟨z, hz, hzY⟩ := he
      let zΓ : Γ := ⟨z, rationalImage_le_rationalSubgroup _ ((mem_parabolicRationalImage_iff _ _).mp hz)⟩
      have hzΓ : zΓ ∈ PΓ(R) :=
        (mem_parabolicRationalSubgroup_iff_mem_parabolicRationalImage zΓ).mpr hz
      let δ := zΓ * (Quotient.out c : Γ)
      have hδ : Quotient.mk _ δ = c := by
        rw [← Quotient.out_eq c]
        apply Quotient.sound
        change QuotientGroup.rightRel (PΓ(R)) δ (Quotient.out c)
        rw [QuotientGroup.rightRel_apply]
        simpa only [δ, mul_inv_rev, mul_inv_cancel_left] using (PΓ(R)).inv_mem hzΓ
      have hδY : δ.val * x = z * y c := mul_assoc _ _ _
      have hN₁ : δ.val * x ∈ normOneSubgroup F G := (normOneSubgroup F G).mul_mem
        (rationalSubgroup_le_normOneSubgroup F G δ.2) hx
      have hσ₂ : σ₀ (R : Set (characterLattice T)) S (H₀(δ.val * x) - Tp) = 1 := by
        rw [hδY, sigma_height_mul_left hG hi hν D hK hρ hRS hS Tp hz, hσ₁]
      obtain ⟨p, hp, a, ha, k, hk, hpak⟩ := exists_sigmaTorusRegion_of_mem hG hi hν D hK hρ C T₁ Tp
        hC (hδY ▸ hzY) hσ₂ hN₁
      refine ⟨δ, hδ, ?_⟩
      have hb : b c = g (δ.val * x) := by
        simp only [b, hcoeff, Int.cast_one, one_mul, hδY, g]
        exact (alternatingConstantTerm_mul_left hG hi hν hS f.val hz _).symm
      rw [hb, ← hpak]
      exact hDecay p hp a ha k hk
  choose δ hδ hδB using hrep
  choose q hq using fun c => (δ c).property
  let e : PQuot(R) ↪ RationalGroupPoints F G :=
    ⟨q, fun c c' hc => by
      have hδeq : δ c = δ c' := Subtype.ext ((hq c).symm.trans ((congrArg (rational F G) hc).trans (hq c')))
      exact (hδ c).symm.trans ((congrArg (Quotient.mk _) hδeq).trans (hδ c'))⟩
  refine ⟨e, fun c => ?_⟩
  change ‖b c‖ * H (rational F G (q c) * x) ^ m ≤ B
  rw [hq]
  exact hδB c

end Langlands.Global.ArthurTruncation
