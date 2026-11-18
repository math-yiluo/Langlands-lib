import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientTwistXi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviCompactIntegralComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd

/-! # Original twisted coefficients with an arbitrary source Levi compact -/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

section Xi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hK : IsCompact (K : Set G)) {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (hν : ∀ i, Continuous (ν i))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)]

/-- Uniform unitary-twist coefficient control using any displayed compact
source Levi Iwasawa subgroup, retaining the exact original ambient compact
picture, coefficient map, Haar normalization and spherical function. -/
theorem norm_twist_coefficientMap_le_xi_arbitraryCompact [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (KM : Subgroup M) [CompactSpace KM]
    (hMK : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    (F₀ : ProductInducedCompactPicture h K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : unramifiedCharacters ν, (∀ m, ‖(χ.val m : ℂ)‖ = 1) → ∀ g : G,
      ‖CompactInduction.coefficientMap h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hm hPK hG hδP
          ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA)
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ F₀) g‖ ≤
        C * xi hP₀K δ₀ g := by
  obtain ⟨C, hC, hb⟩ := integrand_twist_bound h hU A K ν hP hK hν hm (factorization_subtype hPK)
    hδ (xi hMK δ₀M) (fun m => integral_nonneg fun k => iwasawaWeight_nonneg _) hcoeff F₀
  refine ⟨C * sourceLeviXiComparisonConstant hP₀K KM hδ₀ K.isOpen,
    mul_pos hC (sourceLeviXiComparisonConstant_pos hP₀K KM hδ₀ K.isOpen), fun χ hχ g => ?_⟩
  set B := A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)
  set F := twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ F₀
  have hΦ : ∀ (k : K) (x : G), ‖inducedIntegrandKernel h hU B K F k x‖ ≤
      C * arbitraryCompactLeviXiWeight (mP := h.projection)
        (δP := HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
        (δ₀M := δ₀M) KM (hP₀K.mono hL.le_P₀) hMK x := by
    intro k x
    obtain ⟨k₁, hk₁, hx⟩ := exists_iwasawaFactor (hP₀K.mono hL.le_P₀) x
    have he : (k : G) * ((k : G)⁻¹ * x) = (iwasawaFactor (hP₀K.mono hL.le_P₀) x : G) *
        ((⟨k₁, hk₁⟩ : K) : G) := by
      rw [mul_inv_cancel_left]
      exact hx
    refine (hb χ hχ _ k ⟨k₁, hk₁⟩ _ he).trans (le_of_eq ?_)
    unfold arbitraryCompactLeviXiWeight leviComponent
    ring
  have hint : CompactInduction.coefficientMap h hU B K hK hP hm hPK hG hδP
      ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA) F g =
      compactIntegral (K : Subgroup G) (inducedIntegrandKernel h hU B K F) g := by
    rw [CompactInduction.coefficientMap_integral, CompactInduction.measure_eq_normalizedHaar K hK]
    unfold compactIntegral
    simp_rw [inducedIntegrandKernel_mul]
    rfl
  rw [hint]
  have hδPKM : ∀ m : M, m ∈ KM →
      HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m = 1 := fun m hm =>
    eq_one_of_isOpen_ker_of_isCompact _
      (HaarModulus.isOpen_ker_closedRestrictCharacter U hU M h.levi_le_normalizer)
      (isCompact_iff_compactSpace.mpr inferInstance) hm
  exact hL.norm_compactIntegral_le_xi_arbitraryCompact hP₀K KM hδ₀ K.isOpen
    hMK hKMo hδ₀M hδPKM hC.le hΦ g

set_option maxRecDepth 10000 in
/-- The same arbitrary-source compact bound for every finite smooth
family in the original compact picture. -/
theorem norm_family_coefficientMap_le_xi_arbitraryCompact [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (KM : Subgroup M) [CompactSpace KM]
    (hMK : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    {J : Type uJ} [Fintype J] (Ψ : (J → Circle) → ProductInducedCompactPicture h K A)
    (hΨ : Ψ ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K A))
    (e : unramifiedCharacters ν → (J → Circle)) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : unramifiedCharacters ν, (∀ m, ‖(χ.val m : ℂ)‖ = 1) → ∀ g : G,
      ‖CompactInduction.coefficientMap h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hm hPK hG hδP
          ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA)
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ (Ψ (e χ))) g‖ ≤
        C * xi hP₀K δ₀ g := by
  obtain ⟨n, f, v, hF⟩ := (mem_finiteSmoothFamilies_iff J _ Ψ).mp hΨ
  choose B hB0 hB using fun i => exists_norm_le_of_smoothFiniteTorusFunction (f i)
  choose C hC0 hC using fun i => norm_twist_coefficientMap_le_xi_arbitraryCompact h hU A K hK ν hν hP hm hPK hG
    hδP hA hδ hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff (v i)
  refine ⟨1 + ∑ i, B i * C i, add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) (hC0 i).le), fun χ hχ g => ?_⟩
  let E := productInducedCompactEquiv ν h K hP hK hν hm hU (factorization_subtype hPK) χ A
  let L := (LocallyConstant.evalₗ ℂ g).comp
    ((CompactInduction.coefficientMap h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hm hPK hG hδP
      ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA)).comp E.symm.toLinearMap)
  have hxi : 0 ≤ xi hP₀K δ₀ g := integral_nonneg fun k => iwasawaWeight_nonneg _
  change ‖L (Ψ (e χ))‖ ≤ _
  rw [hF (e χ), map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖L ((f i).val (e χ) • v i)‖
      ≤ ∑ i, B i * (C i * xi hP₀K δ₀ g) := Finset.sum_le_sum fun i _ => by
        have hCi : ‖L (v i)‖ ≤ C i * xi hP₀K δ₀ g := hC i χ hχ g
        rw [map_smul, norm_smul]
        exact mul_le_mul (hB i _) hCi (norm_nonneg _) (hB0 i)
    _ = (∑ i, B i * C i) * xi hP₀K δ₀ g := by rw [Finset.sum_mul]; simp only [mul_assoc]
    _ ≤ (1 + ∑ i, B i * C i) * xi hP₀K δ₀ g := by nlinarith

/-- A positive coefficient constant selected before every unitary twist
and every original ambient group point. -/
def arbitraryCompactFamilyXiConstant [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (KM : Subgroup M) [CompactSpace KM]
    (hMK : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    {J : Type uJ} [Fintype J] (Ψ : (J → Circle) → ProductInducedCompactPicture h K A)
    (hΨ : Ψ ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K A))
    (e : unramifiedCharacters ν → (J → Circle)) : ℝ :=
  Classical.choose (norm_family_coefficientMap_le_xi_arbitraryCompact
    h hU A K hK ν hν hP hm hPK hG hδP hA hδ hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff Ψ hΨ e)

/-- The selected constant is positive and bounds every original coefficient. -/
theorem arbitraryCompactFamilyXiConstant_spec [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (KM : Subgroup M) [CompactSpace KM]
    (hMK : IsIwasawaPair (P₀.subgroupOf M) KM)
    (hKMo : IsOpen (KM : Set M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, (p : M) ∈ KM → δ₀M p = 1)
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    {J : Type uJ} [Fintype J] (Ψ : (J → Circle) → ProductInducedCompactPicture h K A)
    (hΨ : Ψ ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K A))
    (e : unramifiedCharacters ν → (J → Circle)) :
    0 < arbitraryCompactFamilyXiConstant h hU A K hK ν hν hP hm hPK hG hδP hA hδ hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff Ψ hΨ e ∧ ∀ χ : unramifiedCharacters ν, (∀ m, ‖(χ.val m : ℂ)‖ = 1) → ∀ g : G,
      ‖CompactInduction.coefficientMap h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hm hPK hG hδP
          ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA)
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ (Ψ (e χ))) g‖ ≤
        arbitraryCompactFamilyXiConstant h hU A K hK ν hν hP hm hPK hG hδP hA hδ hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff Ψ hΨ e * xi hP₀K δ₀ g :=
  Classical.choose_spec (norm_family_coefficientMap_le_xi_arbitraryCompact
    h hU A K hK ν hν hP hm hPK hG hδP hA hδ hL hP₀K KM hMK hKMo hδ₀M hδ₀ hcoeff Ψ hΨ e)

end Xi

end Langlands.HarishChandraSchwartz
