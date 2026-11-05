import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientXi
import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Representation.Category.Twist
import Langlands.Representation.Plancherel.SmoothTensorFamilies

/-! # Uniform `Ξ`-bound for unramified twists (Waldspurger, Lemma VI.2.2)

Waldspurger, Lemma VI.2.2 (printed pp. 298–299), reduces to: for `(ω, E)`, `v ∈ I_{K∩P}^K E`
and `v̌ ∈ I_{K∩P}^K Ě` there is `C > 0` with `|⟨I_P^G(ω ⊗ χ)(g) v, v̌⟩| ≤ C Ξ(g)` for all
`χ ∈ Im X(M)` and `g ∈ G`, where `v` and `v̌` are read in the induced representations of the
twists through their common restriction to `K`.

This module proves that uniform bound: a fixed section `F₀` of Worker 200's compact picture
`ProductInducedCompactPicture h K A` is transported to the product-induced coefficient space of
every twist `A ⊗ χ` by `productInducedCompactEquiv`, and one constant bounds all the
coefficients `CompactInduction.coefficientMap` of these transports by `C Ξ(g)`, for every
unitary unramified `χ`. It then extends the bound to the smooth families of VI.1 read in the
compact picture, `z ↦ ∑ᵢ fᵢ(z) vᵢ` with smooth `fᵢ` on a torus (`finiteSmoothFamilies`).
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

section Tensor

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- Coefficients of the twist `A ⊗ χ`: `ℓ((A ⊗ χ)(m) v) = χ(m) ℓ(A(m) v)`, where the smooth
functional `ℓ` of the twist is read as a smooth functional of `A` by
`productCompactTwistTensorEquiv`. -/
theorem coefficientTensorMap_twist (χ : unramifiedCharacters ν) (A : SmoothRep.{0, uG, uV} ℂ M)
    (t : CoefficientTensor (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)))
    (m : M) :
    coefficientTensorMap (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) t m =
      (χ.val m : ℂ) * coefficientTensorMap A (productCompactTwistTensorEquiv ν χ A t) m := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    rw [productCompactTwistTensorEquiv_tmul, coefficientTensorMap_tmul, coefficientTensorMap_tmul]
    change ℓ.val ((χ.val.toMonoidHom m : ℂ) • A.representation m v) = _
    rw [map_smul, smul_eq_mul]
    rfl
  | add t s ht hs => simp only [map_add, LocallyConstant.add_apply, ht, hs, mul_add]

end Tensor

section Compact

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- Waldspurger's `v_χ` (proof of Lemma VI.2.2): the element of the product-induced coefficient
space of the twist `A ⊗ χ` whose restriction to `K × K` is the fixed compact section `F₀`, i.e.
the transport of `F₀` by the inverse of `productInducedCompactEquiv`. -/
def twistedSection (χ : unramifiedCharacters ν) (F₀ : ProductInducedCompactPicture h K A) :
    productInducedCoefficientObject h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) :=
  (productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A).symm F₀

/-- The compact values of the transported section are those of the fixed compact section,
read through `productCompactTwistTensorEquiv`. -/
theorem compactValue_twistedSection (χ : unramifiedCharacters ν)
    (F₀ : ProductInducedCompactPicture h K A) (k : K × K) :
    CompactInduction.compactValue h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K
        (twistedSection h hU A K ν hP hK hν hr hPK χ F₀) k =
      (productCompactTwistTensorEquiv ν χ A).symm
        (eval _ _ F₀ ⟨((k.1 : G), (k.2 : G)), k.1.2, k.2.2⟩) := by
  unfold twistedSection
  set E := productInducedCompactEquiv ν h K hP hK hν hr hU hPK χ A
  have h1 := productInducedCompactEquiv_eval ν h K hP hK hν hr hU hPK χ A (E.symm F₀)
    ⟨((k.1 : G), (k.2 : G)), k.1.2, k.2.2⟩
  rw [E.apply_symm_apply F₀] at h1
  rw [LinearEquiv.eq_symm_apply]
  exact h1.symm

include hK in
omit [LocallyCompactSpace G] in
/-- A section of the compact picture takes finitely many values on the compact `K × K`. -/
theorem compactPicture_eval_range_finite (F₀ : ProductInducedCompactPicture h K A) :
    (Set.range (eval _ _ F₀)).Finite := by
  have : CompactSpace (K.prod K) := isCompact_iff_compactSpace.mp (by
    change IsCompact ((K : Set G) ×ˢ (K : Set G))
    exact hK.prod hK)
  exact (eval_isLocallyConstant _ _ F₀).range_finite

variable [SecondCountableTopology G]

include hK in
/-- **The uniform integrand bound**: one constant bounds the diagonal integrands of the
transports of a fixed compact section `F₀` to all the twists `A ⊗ χ`, `χ` unitary, through every
parabolic–compact factorization `k g = q k₁`. -/
theorem integrand_twist_bound (hδ : IsUnimodularModulus U hU) (ξ : M → ℝ)
    (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (F₀ : ProductInducedCompactPicture h K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : unramifiedCharacters ν, (∀ m, ‖(χ.val m : ℂ)‖ = 1) →
      ∀ (g : G) (k k₁ : K) (q : P), (k : G) * g = (q : G) * (k₁ : G) →
      ‖CompactInduction.integrand h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K g
          (twistedSection h hU A K ν hP hK hν hr hPK χ F₀) k‖ ≤
        (NNReal.sqrt
          (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
            (h.projection q) : ℝ≥0) : ℝ) * (C * ξ (h.projection q)) := by
  obtain ⟨C, hC, hb⟩ := coefficientTensorMap_bound_finite A ξ hξ hcoeff
    (Set.range (eval _ _ F₀)) (compactPicture_eval_range_finite h A K hK F₀)
  refine ⟨C, hC, fun χ hχ g k k₁ q he => ?_⟩
  rw [CompactInduction.integrand_factorization h hU _ K _ g k k₁ q he,
    compactValue_twistedSection h hU A K ν hP hK hν hr hPK χ F₀,
    coefficientTensorMap_twist, LinearEquiv.apply_symm_apply, norm_mul, norm_mul, hχ, one_mul]
  have hn : ‖(HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ)‖ =
      (NNReal.sqrt
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (h.projection q) : ℝ≥0) : ℝ) := by
    rw [closedHalfCharacter_eq_comp_projection h hU hδ, MonoidHom.comp_apply]
    change ‖(((NNReal.sqrt
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
        (h.projection q) : ℝ≥0) : ℝ) : ℂ))‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left (hb _ ⟨_, rfl⟩ _) (NNReal.coe_nonneg _)

end Compact

/-- The factorization `G = P K` with subgroup membership gives the subtype form used by
`productInducedCompactEquiv`. -/
theorem factorization_subtype {G : Type uG} [Group G] [TopologicalSpace G] {P : Subgroup G}
    {K : OpenSubgroup G} (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k) :
    ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G) := fun g => by
  obtain ⟨q, hq, k, hk, e⟩ := hPK g
  exact ⟨⟨q, hq⟩, ⟨k, hk⟩, e⟩

section Xi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hK : IsCompact (K : Set G)) {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (hν : ∀ i, Continuous (ν i))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]

/-- **Lemma VI.2.2, uniform over the unitary unramified twists**: for a fixed section `F₀` of
the compact picture, there is `C > 0` such that for every unitary unramified character `χ` of
`M` the coefficient of the twisted normalized induced representation `I_P^G(A ⊗ χ)` attached to
the transport of `F₀` satisfies `|E_P^G(F₀)_χ(g)| ≤ C Ξ(g)` for all `g ∈ G`. -/
theorem norm_twist_coefficientMap_le_xi [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
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
  refine ⟨C, hC, fun χ hχ g => ?_⟩
  set B := A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)
  set F := twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ F₀
  have hΦ : ∀ (k : K) (x : G), ‖inducedIntegrandKernel h hU B K F k x‖ ≤
      C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M x := by
    intro k x
    obtain ⟨k₁, hk₁, hx⟩ := exists_iwasawaFactor (hP₀K.mono hL.le_P₀) x
    have he : (k : G) * ((k : G)⁻¹ * x) = (iwasawaFactor (hP₀K.mono hL.le_P₀) x : G) *
        ((⟨k₁, hk₁⟩ : K) : G) := by
      rw [mul_inv_cancel_left]
      exact hx
    refine (hb χ hχ _ k ⟨k₁, hk₁⟩ _ he).trans (le_of_eq ?_)
    unfold leviXiWeight leviComponent
    ring
  have hint : CompactInduction.coefficientMap h hU B K hK hP hm hPK hG hδP
      ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA) F g =
      compactIntegral (K : Subgroup G) (inducedIntegrandKernel h hU B K F) g := by
    rw [CompactInduction.coefficientMap_integral, CompactInduction.measure_eq_normalizedHaar K hK]
    unfold compactIntegral
    simp_rw [inducedIntegrandKernel_mul]
    rfl
  rw [hint]
  exact hL.norm_compactIntegral_le_xi K.isOpen hP₀K hMK hδ₀ hΦ g

/-- A smooth scalar function on the compact torus `(S¹)^J` is bounded. -/
theorem exists_norm_le_of_smoothFiniteTorusFunction {J : Type uJ} [Fintype J]
    (f : smoothFiniteTorusFunctions J) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖f.val z‖ ≤ B := by
  have hc : Continuous f.val := IsSmoothFiniteTorusFunction.continuous f.property
  obtain ⟨B, hB⟩ := (isCompact_univ.image hc).isBounded.exists_norm_le
  exact ⟨max B 0, le_max_right _ _, fun z =>
    (hB _ ⟨z, Set.mem_univ _, rfl⟩).trans (le_max_left _ _)⟩

set_option maxRecDepth 10000 in
/-- **Lemma VI.2.2 for smooth families in the compact picture**: let `Ψ` be a smooth family
`z ↦ ∑ᵢ fᵢ(z) vᵢ` on the torus `(S¹)^J` with values in the compact picture
(`finiteSmoothFamilies`), and `e` any map from the unramified characters to the torus. There is
`C > 0` such that for every unitary unramified `χ` and every `g ∈ G`, the coefficient of the
twisted section `twistedSection χ (Ψ (e χ))` satisfies `|E(g)| ≤ C Ξ(g)`. -/
theorem norm_family_coefficientMap_le_xi [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
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
  choose C hC0 hC using fun i => norm_twist_coefficientMap_le_xi h hU A K hK ν hν hP hm hPK hG
    hδP hA hδ hL hP₀K hMK hδ₀ hcoeff (v i)
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

end Xi

end Langlands.HarishChandraSchwartz
