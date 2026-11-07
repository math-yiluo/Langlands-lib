import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar
import Langlands.Representation.Category.Twist
import Mathlib.Analysis.Normed.Ring.Finite
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleFitting
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions

/-! # The operators `π(p)` of Waldspurger, Proposition III.7.1

Proposition III.7.1 (printed p. 273): for an orbit `O ⊂ E₂(G)` of `Im X(G)` and a polynomial
`p` on `O`, every admissible tempered `(π, V)` carries an operator `π(p) ∈ End_G V` with
(i) `π₂(p) ∘ f = f ∘ π₁(p)` for intertwiners `f`, (ii) `π(p) = 0` if `π` is irreducible and
`π ∉ O`, (iii) `π(p) = p(π)` if `π ∈ O`. The proof (printed p. 275) takes `π(p) = π[φ]` for a
`φ` with `P_φ|_O = p`.

In the abstract setting of `TraceFamilyScalar` (a surjective `p : G →* Λ` onto a commutative
group with open kernel for `G → G/G¹`, a central `A` for `A_G`), the orbit of `ω` is the set of
classes of `ω ⊗ (χ ∘ p)` with `χ` a unitary character of `Λ`, and a polynomial on `O` is given by
a finitely supported `b : Λ →₀ ℂ`, through `χ ↦ b̂(χ) = Σ_λ b(λ) χ(λ)`, constant on the classes of
`O` (hypothesis `hb`). This module defines `orbitPolynomialOperator … b π = π[φ_b]` with
`φ_b = orbitPolynomialTestFunction … b` and proves (i) `orbitPolynomialOperator_comp`,
(iii) `orbitPolynomialOperator_eq_smul_of_equiv` and (ii) `orbitPolynomialOperator_eq_zero`.

Corollary III.7.2 (printed p. 275): for `ω ∈ E₂(G)` and an admissible tempered `π`, `V = V₁ ⊕ V₂`
with every irreducible subquotient of `V₁` isomorphic to `ω` and none of `V₂`. The proof takes a
polynomial `p` vanishing on the finitely many other points `Σ - {ω}` of the orbit occurring in
`π`, with `p(ω) = 1`, and `V₁ = ⋂ₙ π(p)ⁿ V`, `V₂ = ⋃ₙ Ker π(p)ⁿ`. Here the polynomial is
`exists_orbit_separating` (interpolation by characters, `exists_finsuppCharacterSum_eq`, averaged
over the stabilizer), the decomposition is the Library's Fitting decomposition, and
`exists_isCompl_orbitIsotypic` gives (i) and (ii), with a finite set `F` of characters standing
for `Σ - {ω}`. The finiteness of `Σ` is `exists_orbit_covering` (through the bound
`card_le_finrank_of_hasSubquotientIn` by the dimension of `V^H`), and
`existsUnique_orbitIsotypic_decomposition` is the corollary with existence and uniqueness. -/

noncomputable section

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel
open Langlands.ProductFactorization (subrepresentationInclusion subrepresentationInclusion_injective)

section Twists

variable {G : Type*} [Group G] {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {ω : Representation ℂ G W}

/-- If `π ≃ ω ⊗ (χ₁ ∘ p)`, then `π ⊗ ((χ₁ θ) ∘ p)⁻¹ ≃ ω` if and only if
`ω ⊗ (θ ∘ p)⁻¹ ≃ ω`. -/
theorem nonempty_twist_equiv_iff (χ₁ θ : Λ →* ℂˣ) (e : π.Equiv (twist (χ₁.comp p) ω)) :
    Nonempty ((twist ((χ₁ * θ).comp p)⁻¹ π).Equiv ω) ↔
      Nonempty ((twist (θ.comp p)⁻¹ ω).Equiv ω) := by
  have hchar : ((χ₁ * θ).comp p)⁻¹ * χ₁.comp p = (θ.comp p)⁻¹ := by
    ext g
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, mul_inv_rev]
    group
  let f : (twist ((χ₁ * θ).comp p)⁻¹ π).Equiv (twist (θ.comp p)⁻¹ ω) :=
    (twistEquiv _ e).trans (equivOfRepresentationEq (by rw [twist_twist, hchar]))
  exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩, fun ⟨g⟩ => ⟨f.trans g⟩⟩

/-- `ω ⊗ (θ ∘ p)⁻¹ ≃ ω` implies `ω ⊗ ((χ₁ θ) ∘ p) ≃ ω ⊗ (χ₁ ∘ p)`. -/
theorem nonempty_twist_mul_equiv (χ₁ θ : Λ →* ℂˣ)
    (h : Nonempty ((twist (θ.comp p)⁻¹ ω).Equiv ω)) :
    Nonempty ((twist ((χ₁ * θ).comp p) ω).Equiv (twist (χ₁.comp p) ω)) := by
  obtain ⟨e⟩ := h
  have e' : (twist (θ.comp p) ω).Equiv ω :=
    (twistEquiv (θ.comp p) e).symm.trans (equivOfRepresentationEq (twist_twist_inv _ _))
  have hchar : (χ₁ * θ).comp p = χ₁.comp p * θ.comp p := by
    ext g
    simp
  exact ⟨(equivOfRepresentationEq (by rw [hchar, ← twist_twist])).trans
    (twistEquiv (χ₁.comp p) e')⟩

/-- If `π ⊗ (χ ∘ p)⁻¹ ≃ ω`, then `π ≃ ω ⊗ (χ ∘ p)`. -/
theorem nonempty_equiv_twist_of_twist_inv (χ : Λ →* ℂˣ)
    (h : Nonempty ((twist (χ.comp p)⁻¹ π).Equiv ω)) :
    Nonempty (π.Equiv (twist (χ.comp p) ω)) := by
  obtain ⟨e⟩ := h
  exact ⟨(equivOfRepresentationEq (twist_twist_inv _ _)).symm.trans (twistEquiv _ e)⟩

end Twists

section Characters

variable {Λ : Type*} [CommGroup Λ] (B : Subgroup Λ) [Finite (Λ ⧸ B)]

/-- The characters of the finite group `Λ / B` are unitary. -/
theorem norm_quotientCharacter (η : AddChar (Additive (Λ ⧸ B)) ℂ) (x : Λ) :
    ‖(quotientCharacter B η x : ℂ)‖ = 1 := by
  rw [quotientCharacter_apply, AddChar.norm_apply]

/-- A character of `Λ` whose restriction to `B` is unitary is unitary, when `Λ / B` is finite. -/
theorem norm_eq_one_of_norm_eq_one_on (χ : Λ →* ℂˣ) (hχ : ∀ b ∈ B, ‖(χ b : ℂ)‖ = 1) (x : Λ) :
    ‖(χ x : ℂ)‖ = 1 := by
  have := Fintype.ofFinite (Λ ⧸ B)
  have hn : (x : Λ ⧸ B) ^ Fintype.card (Λ ⧸ B) = 1 := pow_card_eq_one
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn
  have h := hχ _ hn
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h

/-- `φ̂` is linear in `φ`. -/
theorem finsuppCharacterSum_smul (c : ℂ) (φ : Λ →₀ ℂ) (χ : Λ →* ℂˣ) :
    finsuppCharacterSum (c • φ) χ = c * finsuppCharacterSum φ χ := by
  simp only [finsuppCharacterSum]
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Characters

section Operator

universe u v w

open scoped ENNReal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant]
  {K : Subgroup G} [CompactSpace K]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (ν : Measure (G ⧸ A)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {W : Type v} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}
  {cω : A →* ℂˣ} (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x)
  (hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν) (hiω : ω.IsIrreducible)
  [Fintype (Λ ⧸ A.map p)]

open scoped Classical in
/-- The stabilizer of `ω` among the characters `η` of `Q = Λ / p(A)`:
the `η` with `ω ⊗ (η ∘ p)⁻¹ ≃ ω`. -/
def orbitStabilizer (ω : Representation ℂ G W) : Finset (AddChar (Additive (Λ ⧸ A.map p)) ℂ) :=
  Finset.univ.filter fun η =>
    Nonempty ((twist ((quotientCharacter (A.map p) η).comp p)⁻¹ ω).Equiv ω)

/-- The scalar `m |Q|⁻¹ d(ω)⁻¹ |St(ω)|` relating `π[φ]` to `φ̂` on the orbit of `ω`. -/
def orbitPolynomialConstant (m : ℝ≥0∞) : ℂ :=
  m.toReal * (Nat.card (Λ ⧸ A.map p) : ℂ)⁻¹ *
    ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ * (orbitStabilizer p A ω).card

/-- The test function `φ_b = c⁻¹ b` attached to a polynomial `b̂` on the unramified characters,
`c` being `orbitPolynomialConstant`. -/
def orbitPolynomialTestFunction (m : ℝ≥0∞) (b : Λ →₀ ℂ) : Λ →₀ ℂ :=
  (orbitPolynomialConstant p A hA ν hcof hω hsq hiω m)⁻¹ • b

omit [TopologicalSpace G] [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [A.Normal]
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)] in
theorem one_mem_orbitStabilizer : (0 : AddChar (Additive (Λ ⧸ A.map p)) ℂ) ∈
    orbitStabilizer p A ω := by
  classical
  simp only [orbitStabilizer, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : ((quotientCharacter (A.map p) 0).comp p)⁻¹ = 1 := by
    ext g
    simp [quotientCharacter_apply]
  rw [h1, twist_one]
  exact ⟨Representation.Equiv.refl ω⟩

omit [Nonempty (CompactOpenSubgroup G)] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem orbitPolynomialConstant_ne_zero {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0) :
    orbitPolynomialConstant p A hA ν hcof hω hsq hiω m ≠ 0 := by
  have hd := formalDegree_pos A hA ν hω hcof hsq hiω
  have hc : (Nat.card (Λ ⧸ A.map p) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hs : ((orbitStabilizer p A ω).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, one_mem_orbitStabilizer p A⟩)
  have hmr : (m.toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hm0, hm⟩)
  simp only [orbitPolynomialConstant]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hmr (inv_ne_zero hc))
    (inv_ne_zero (Complex.ofReal_ne_zero.2 hd.ne'))) hs

variable {V : Type w} [AddCommGroup V] [Module ℂ V]

/-- **The operator `π(p)` of Waldspurger, Proposition III.7.1**, for the polynomial `b̂` on the
unramified characters: `π[φ_b]`, with `φ_b = orbitPolynomialTestFunction … b`. -/
def orbitPolynomialOperator (hN : IsOpen (p.ker : Set G))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (m : ℝ≥0∞) (b : Λ →₀ ℂ) (π : Representation ℂ G V) (hπa : IsAdmissible π)
    (hT : HasTemperedCoefficients Ξ σ π) : π.IntertwiningMap π :=
  (traceFamily (contragredientRep ω)
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ω hsq.1) hc ht hN hD
    (conj_mk_ker p) hHN (hasCompactSupport_kerLiftFun p hN
      (orbitPolynomialTestFunction p A hA ν hcof hω hsq hiω m b))).operator hw hπa hT

/-- **Proposition III.7.1 (i)**: the operators `π(p)` commute with intertwining maps. -/
theorem orbitPolynomialOperator_comp (hN : IsOpen (p.ker : Set G))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (m : ℝ≥0∞) (b : Λ →₀ ℂ) {π : Representation ℂ G V} (hπa : IsAdmissible π)
    (hTπ : HasTemperedCoefficients Ξ σ π) {V' : Type w} [AddCommGroup V'] [Module ℂ V']
    {τ : Representation ℂ G V'} (hτa : IsAdmissible τ) (hTτ : HasTemperedCoefficients Ξ σ τ)
    (T : π.IntertwiningMap τ) :
    T.comp (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hTπ) =
      (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b τ hτa hTτ).comp T :=
  IdempotentFamily.comp_operator _ hw hπa hτa hTπ hTτ T

/-- **Proposition III.7.1 (iii)**: on `π ≃ ω ⊗ (χ₁ ∘ p)` with `χ₁` unitary, `π(p)` is the
homothety of ratio `b̂(χ₁) = p(π)`, for `b̂` constant on the classes of the orbit (`hb`). -/
theorem orbitPolynomialOperator_eq_smul_of_equiv (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (b : Λ →₀ ℂ)
    (hb : ∀ χ χ' : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → (∀ l, ‖(χ' l : ℂ)‖ = 1) →
      Nonempty ((twist (χ.comp p) ω).Equiv (twist (χ'.comp p) ω)) →
        finsuppCharacterSum b χ = finsuppCharacterSum b χ')
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hiπ : π.IsIrreducible)
    (hT : HasTemperedCoefficients Ξ σ π)
    (hint : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (χ₁ : Λ →* ℂˣ) (hχ₁ : ∀ l, ‖(χ₁ l : ℂ)‖ = 1) (e : π.Equiv (twist (χ₁.comp p) ω)) (v : V) :
    orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT v =
      finsuppCharacterSum b χ₁ • v := by
  classical
  let cπ : A →* ℂˣ := χ₁.comp (p.comp A.subtype) * cω
  have hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x := by
    intro a x
    have h := congrArg (fun T => T (e x)) (e.symm.isIntertwining' (a : G))
    simp only [LinearMap.comp_apply] at h
    change e.symm (twist (χ₁.comp p) ω a (e x)) = π a (e.symm (e x)) at h
    rw [e.symm_apply_apply] at h
    rw [← h]
    change e.symm ((((χ₁.comp p) a : ℂˣ) : ℂ) • ω a (e x)) = _
    rw [hω, smul_smul, map_smul, e.symm_apply_apply]
    simp [cπ]
  have hχ₀ : ∀ a : A, χ₁ (p a) * cω a = cπ a := fun a => rfl
  have hC := orbitPolynomialConstant_ne_zero p A hA ν hcof hω hsq hiω hm hm0
  rw [orbitPolynomialOperator, traceFamily_operator_eq_smul p A hA ν hcof hπc hω hp hN hHN hm
    hcompat hc ht hw hsq hiω hD hπa hiπ hT hint χ₁ hχ₀]
  congr 1
  have hsum : ∀ η : AddChar (Additive (Λ ⧸ A.map p)) ℂ,
      (if Nonempty ((twist ((χ₁ * quotientCharacter (A.map p) η).comp p)⁻¹ π).Equiv ω)
        then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ *
          finsuppCharacterSum (orbitPolynomialTestFunction p A hA ν hcof hω hsq hiω m b)
            (χ₁ * quotientCharacter (A.map p) η)
        else 0) =
      if η ∈ orbitStabilizer p A ω then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ *
        ((orbitPolynomialConstant p A hA ν hcof hω hsq hiω m)⁻¹ * finsuppCharacterSum b χ₁)
      else 0 := by
    intro η
    have hmem : η ∈ orbitStabilizer p A ω ↔
        Nonempty ((twist ((quotientCharacter (A.map p) η).comp p)⁻¹ ω).Equiv ω) := by
      simp [orbitStabilizer]
    by_cases h : Nonempty ((twist ((χ₁ * quotientCharacter (A.map p) η).comp p)⁻¹ π).Equiv ω)
    · have h' := (nonempty_twist_equiv_iff p χ₁ _ e).1 h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h),
        ite_eq_left_of_eq_true _ _ (eq_true (hmem.2 h')), orbitPolynomialTestFunction,
        finsuppCharacterSum_smul,
        hb _ χ₁ (fun l => by
          rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ₁, norm_quotientCharacter, one_mul])
          hχ₁ (nonempty_twist_mul_equiv p χ₁ _ h')]
    · have h' : η ∉ orbitStabilizer p A ω := fun hη =>
        h ((nonempty_twist_equiv_iff p χ₁ _ e).2 (hmem.1 hη))
      rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h')]
  simp_rw [hsum]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]
  calc (m.toReal : ℂ) * (Nat.card (Λ ⧸ A.map p) : ℂ)⁻¹ * ((orbitStabilizer p A ω).card *
        (((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ *
          ((orbitPolynomialConstant p A hA ν hcof hω hsq hiω m)⁻¹ * finsuppCharacterSum b χ₁)))
      = orbitPolynomialConstant p A hA ν hcof hω hsq hiω m *
          (orbitPolynomialConstant p A hA ν hcof hω hsq hiω m)⁻¹ * finsuppCharacterSum b χ₁ := by
        simp only [orbitPolynomialConstant]
        ring
    _ = finsuppCharacterSum b χ₁ := by rw [mul_inv_cancel₀ hC, one_mul]

/-- **Proposition III.7.1 (ii)**: on an irreducible tempered `π` with unitary central character
`cπ` that is not equivalent to any `ω ⊗ (χ ∘ p)` with `χ` unitary, `π(p) = 0`. -/
theorem orbitPolynomialOperator_eq_zero (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (b : Λ →₀ ℂ) {π : Representation ℂ G V} (hπa : IsAdmissible π) (hiπ : π.IsIrreducible)
    (hT : HasTemperedCoefficients Ξ σ π) {cπ : A →* ℂˣ}
    (hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x) (hπu : ∀ a : A, ‖(cπ a : ℂ)‖ = 1)
    (hint : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (hnot : ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → IsEmpty (π.Equiv (twist (χ.comp p) ω)))
    (v : V) :
    orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT v = 0 := by
  classical
  by_cases hcc : ∃ a : A, p a = 1 ∧ cπ a ≠ cω a
  · obtain ⟨a, hpa, hca⟩ := hcc
    obtain ⟨H, hv⟩ := exists_compactOpenSubgroup_fixed hπa.1 v
    refine ext_smoothDual hπa.1 fun ℓ => ?_
    rw [map_zero]
    exact traceFamily_operator_eval_eq_zero p A hcof hπc hω hN hHN hc ht hw hsq.1 hD hπa hT
      a.2 hpa hca _ H hv ℓ
  · push Not at hcc
    obtain ⟨χ₀, hχ₀'⟩ := exists_character_comp_eq p (cπ * cω⁻¹) (fun a ha => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hcc a ha, mul_inv_cancel])
    have hχ₀ : ∀ a : A, χ₀ (p a) * cω a = cπ a := fun a => by
      rw [hχ₀' a, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_right]
    have hωu := norm_character_eq_one A hA ν hω hsq hiω
    have hχ₀u : ∀ l, ‖(χ₀ l : ℂ)‖ = 1 := norm_eq_one_of_norm_eq_one_on (A.map p) χ₀ (by
      rintro _ ⟨a, ha, rfl⟩
      have := hχ₀' ⟨a, ha⟩
      change χ₀ (p a) = _ at this
      rw [this, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul,
        Units.val_inv_eq_inv_val, norm_inv, hπu, hωu, inv_one, one_mul])
    rw [orbitPolynomialOperator, traceFamily_operator_eq_smul p A hA ν hcof hπc hω hp hN hHN hm
      hcompat hc ht hw hsq hiω hD hπa hiπ hT hint χ₀ hχ₀]
    have hzero : ∀ η : AddChar (Additive (Λ ⧸ A.map p)) ℂ,
        (if Nonempty ((twist ((χ₀ * quotientCharacter (A.map p) η).comp p)⁻¹ π).Equiv ω)
          then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ *
            finsuppCharacterSum (orbitPolynomialTestFunction p A hA ν hcof hω hsq hiω m b)
              (χ₀ * quotientCharacter (A.map p) η)
          else 0) = 0 := by
      intro η
      refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ?_)
      obtain ⟨e⟩ := nonempty_equiv_twist_of_twist_inv p _ h
      exact (hnot _ (fun l => by
        rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ₀u, norm_quotientCharacter,
          one_mul])).false e
    simp only [hzero, Finset.sum_const_zero, mul_zero, zero_smul]

end Operator

section Interpolation

variable {Λ : Type*} [CommGroup Λ]

theorem finsuppCharacterSum_add (φ ψ : Λ →₀ ℂ) (χ : Λ →* ℂˣ) :
    finsuppCharacterSum (φ + ψ) χ = finsuppCharacterSum φ χ + finsuppCharacterSum ψ χ := by
  simp only [finsuppCharacterSum]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem finsuppCharacterSum_single (l : Λ) (c : ℂ) (χ : Λ →* ℂˣ) :
    finsuppCharacterSum (Finsupp.single l c) χ = c * χ l := by
  simp only [finsuppCharacterSum]
  exact Finsupp.sum_single_index (zero_mul _)

/-- Polynomials interpolate: for a finite set `S` of characters of `Λ` and any values `f` on `S`,
some `b` has `b̂(χ) = f(χ)` for `χ ∈ S` (Dedekind's independence of characters). -/
theorem exists_finsuppCharacterSum_eq (S : Finset (Λ →* ℂˣ)) (f : (Λ →* ℂˣ) → ℂ) :
    ∃ b : Λ →₀ ℂ, ∀ χ ∈ S, finsuppCharacterSum b χ = f χ := by
  classical
  let E : (Λ →₀ ℂ) →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun b χ => finsuppCharacterSum b χ
      map_add' := fun φ ψ => funext fun χ => finsuppCharacterSum_add φ ψ χ
      map_smul' := fun c φ => funext fun χ => finsuppCharacterSum_smul c φ χ }
  have hE : Function.Surjective E := by
    rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hli := (linearIndependent_monoidHom Λ ℂ).comp
      (fun χ : S => (Units.coeHom ℂ).comp χ.1) (fun χ χ' h => Subtype.ext (MonoidHom.ext
        fun l => Units.ext (DFunLike.congr_fun h l)))
    have hsum : ∑ χ : S, y (Pi.single χ 1) • (fun l => ((χ.1 l : ℂˣ) : ℂ)) = 0 := by
      funext l
      have h := LinearMap.congr_fun hy (Finsupp.single l 1)
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at h
      have hv : E (Finsupp.single l 1) = ∑ χ : S, ((χ.1 l : ℂˣ) : ℂ) • Pi.single χ (1 : ℂ) := by
        funext χ'
        simp [E, finsuppCharacterSum_single, Finset.sum_apply, Pi.single_apply]
      rw [hv, map_sum] at h
      simpa [map_smul, mul_comm] using h
    have hy0 := Fintype.linearIndependent_iff.1 hli (fun χ => y (Pi.single χ 1)) (by
      simpa [Function.comp_def] using hsum)
    refine LinearMap.ext fun v => ?_
    have hv : v = ∑ χ : S, v χ • Pi.single χ (1 : ℂ) := by
      funext χ'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    simp [map_smul, hy0]
  obtain ⟨b, hb⟩ := hE (fun χ => f χ)
  exact ⟨b, fun χ hχ => congrFun hb ⟨χ, hχ⟩⟩

end Interpolation

section Twisting

variable {Λ : Type*} [CommGroup Λ]

/-- Multiplying the coefficients of `b` by a character `s`: `(s b)^(χ) = b̂(χ s)`. -/
def finsuppTwist (s : Λ →* ℂˣ) (b : Λ →₀ ℂ) : Λ →₀ ℂ :=
  b.sum fun l c => Finsupp.single l (c * s l)

theorem finsuppCharacterSum_finsuppTwist (s : Λ →* ℂˣ) (b : Λ →₀ ℂ) (χ : Λ →* ℂˣ) :
    finsuppCharacterSum (finsuppTwist s b) χ = finsuppCharacterSum b (χ * s) := by
  simp only [finsuppTwist, finsuppCharacterSum]
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun l _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _), MonoidHom.mul_apply, Units.val_mul]
  ring

theorem finsuppCharacterSum_sum {ι : Type*} (t : Finset ι) (b : ι → Λ →₀ ℂ) (χ : Λ →* ℂˣ) :
    finsuppCharacterSum (∑ i ∈ t, b i) χ = ∑ i ∈ t, finsuppCharacterSum (b i) χ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [finsuppCharacterSum]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, finsuppCharacterSum_add, ih]

variable (B : Subgroup Λ)

theorem quotientCharacter_add (η η' : AddChar (Additive (Λ ⧸ B)) ℂ) :
    quotientCharacter B (η + η') = quotientCharacter B η * quotientCharacter B η' := by
  ext x
  simp [quotientCharacter_apply, AddChar.add_apply]

theorem quotientCharacter_neg (η : AddChar (Additive (Λ ⧸ B)) ℂ) :
    quotientCharacter B (-η) = (quotientCharacter B η)⁻¹ := by
  ext x
  rw [quotientCharacter_apply, AddChar.neg_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    quotientCharacter_apply, AddChar.map_neg_eq_inv]

theorem quotientCharacter_injective : Function.Injective (quotientCharacter (Λ := Λ) B) := by
  intro η η' h
  ext x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (y : Λ ⧸ B) := by rw [hy]; rfl
  have := congrArg (fun χ : Λ →* ℂˣ => (χ y : ℂ)) h
  simp only [quotientCharacter_apply] at this
  rw [hx]
  exact this

/-- A character of `Λ` trivial on `B` is `quotientCharacter B η` for some `η`. -/
theorem exists_quotientCharacter_eq (θ : Λ →* ℂˣ) (hθ : ∀ b ∈ B, θ b = 1) :
    ∃ η : AddChar (Additive (Λ ⧸ B)) ℂ, quotientCharacter B η = θ := by
  let θ' : Λ ⧸ B →* ℂˣ := QuotientGroup.lift B θ fun b hb => hθ b hb
  let η : AddChar (Additive (Λ ⧸ B)) ℂ :=
    { toFun := fun x => (θ' (Additive.toMul x) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp }
  refine ⟨η, MonoidHom.ext fun x => Units.ext ?_⟩
  rw [quotientCharacter_apply]
  rfl

end Twisting

section Stabilizer

variable {G : Type*} [Group G] {Λ : Type*} [CommGroup Λ] (p : G →* Λ) (A : Subgroup G)
  [Fintype (Λ ⧸ A.map p)]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}

theorem mem_orbitStabilizer_iff (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ) :
    η ∈ orbitStabilizer p A ω ↔
      Nonempty ((twist ((quotientCharacter (A.map p) η).comp p)⁻¹ ω).Equiv ω) := by
  classical
  simp [orbitStabilizer]

/-- `ω ⊗ θ⁻¹ ≃ ω` if and only if `ω ⊗ θ ≃ ω`. -/
theorem nonempty_twist_inv_equiv_iff (θ : G →* ℂˣ) :
    Nonempty ((twist θ⁻¹ ω).Equiv ω) ↔ Nonempty ((twist θ ω).Equiv ω) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(twistEquiv θ e).symm.trans (equivOfRepresentationEq (twist_twist_inv _ _))⟩
  · rintro ⟨e⟩
    exact ⟨(twistEquiv θ⁻¹ e).symm.trans (equivOfRepresentationEq (twist_inv_twist _ _))⟩

/-- `ω ⊗ θ ≃ ω` and `ω ⊗ θ' ≃ ω` give `ω ⊗ θθ' ≃ ω`. -/
theorem nonempty_twist_mul_equiv_self {θ θ' : G →* ℂˣ} (h : Nonempty ((twist θ ω).Equiv ω))
    (h' : Nonempty ((twist θ' ω).Equiv ω)) : Nonempty ((twist (θ * θ') ω).Equiv ω) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨(equivOfRepresentationEq (twist_twist θ θ' ω)).symm.trans ((twistEquiv θ e').trans e)⟩

theorem add_mem_orbitStabilizer {η η' : AddChar (Additive (Λ ⧸ A.map p)) ℂ}
    (h : η ∈ orbitStabilizer p A ω) (h' : η' ∈ orbitStabilizer p A ω) :
    η + η' ∈ orbitStabilizer p A ω := by
  rw [mem_orbitStabilizer_iff, nonempty_twist_inv_equiv_iff] at h h' ⊢
  rw [quotientCharacter_add, MonoidHom.mul_comp]
  exact nonempty_twist_mul_equiv_self h h'

theorem neg_mem_orbitStabilizer {η : AddChar (Additive (Λ ⧸ A.map p)) ℂ}
    (h : η ∈ orbitStabilizer p A ω) : -η ∈ orbitStabilizer p A ω := by
  rw [mem_orbitStabilizer_iff] at h ⊢
  have he : ((quotientCharacter (A.map p) (-η)).comp p)⁻¹ =
      (quotientCharacter (A.map p) η).comp p := by
    rw [quotientCharacter_neg]
    ext g
    simp
  rw [he, ← nonempty_twist_inv_equiv_iff]
  exact h

/-- If `ω ⊗ (χ ∘ p) ≃ ω ⊗ (χ' ∘ p)`, then `χ' = χ η` for some `η` in the stabilizer: the
characters `θ` with `ω ⊗ (θ ∘ p) ≃ ω` are trivial on `p(A)`, since `ω` has a central character on
`A`. -/
theorem exists_mem_orbitStabilizer_of_equiv [Nontrivial W] {cω : A →* ℂˣ}
    (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x) (χ χ' : Λ →* ℂˣ)
    (h : Nonempty ((twist (χ.comp p) ω).Equiv (twist (χ'.comp p) ω))) :
    ∃ η ∈ orbitStabilizer p A ω, χ' = χ * quotientCharacter (A.map p) η := by
  obtain ⟨e⟩ := h
  set θ : Λ →* ℂˣ := χ⁻¹ * χ' with hθ
  -- `ω ≃ ω ⊗ (θ ∘ p)`
  have hθp : (χ.comp p)⁻¹ * χ'.comp p = θ.comp p := by
    ext g
    simp [hθ]
  let e' : ω.Equiv (twist (θ.comp p) ω) :=
    (equivOfRepresentationEq (twist_inv_twist (χ.comp p) ω)).symm.trans
      ((twistEquiv (χ.comp p)⁻¹ e).trans
        (equivOfRepresentationEq (by rw [twist_twist, hθp])))
  have hθA : ∀ b ∈ A.map p, θ b = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    have hex : e' x ≠ 0 := fun h0 => hx (by simpa using congrArg e'.symm h0)
    have h1 := congrArg (fun T => T x) (e'.isIntertwining' a)
    simp only [LinearMap.comp_apply] at h1
    change e' (ω a x) = twist (θ.comp p) ω a (e' x) at h1
    change e' (ω a x) = (((θ.comp p) a : ℂˣ) : ℂ) • ω a (e' x) at h1
    rw [hω ⟨a, ha⟩, hω ⟨a, ha⟩, map_smul, smul_smul] at h1
    have h2 := smul_left_injective ℂ hex (h1.trans (by rw [mul_comm]))
    have hc : ((cω ⟨a, ha⟩ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    apply Units.ext
    simp only [MonoidHom.comp_apply] at h2
    rw [Units.val_one]
    exact mul_left_cancel₀ hc (h2.symm.trans (mul_one _).symm)
  obtain ⟨η, hη⟩ := exists_quotientCharacter_eq (A.map p) θ hθA
  refine ⟨η, ?_, ?_⟩
  · rw [mem_orbitStabilizer_iff, nonempty_twist_inv_equiv_iff, hη]
    exact ⟨e'.symm⟩
  · rw [hη, hθ]
    exact (mul_inv_cancel_left χ χ').symm

end Stabilizer

section Separation

variable {G : Type*} [Group G] {Λ : Type*} [CommGroup Λ] (p : G →* Λ) (A : Subgroup G)
  [Fintype (Λ ⧸ A.map p)]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}

/-- **The polynomial in the proof of Corollary III.7.2**: for a finite set `F` of characters `χ`
with `ω ⊗ (χ ∘ p) ≄ ω`, a polynomial `b̂` invariant under the stabilizer of `ω`, equal to `1` at
the trivial character and vanishing on `F`. -/
theorem exists_orbit_separating (F : Finset (Λ →* ℂˣ))
    (hF : ∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω)) :
    ∃ b : Λ →₀ ℂ,
      (∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ), η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ) ∧
      finsuppCharacterSum b 1 = 1 ∧ ∀ χ ∈ F, finsuppCharacterSum b χ = 0 := by
  classical
  set St := orbitStabilizer p A ω with hSt
  set T : Finset (Λ →* ℂˣ) := St.image (quotientCharacter (A.map p)) with hT
  set S : Finset (Λ →* ℂˣ) := T ∪ (F ×ˢ T).image (fun x => x.1 * x.2) with hS
  obtain ⟨b, hb⟩ := exists_finsuppCharacterSum_eq S (fun χ => if χ ∈ T then 1 else 0)
  have hcard : (St.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, one_mem_orbitStabilizer p A⟩)
  let c : ℂ := (St.card : ℂ)⁻¹
  have hval : ∀ χ, finsuppCharacterSum (c • ∑ η ∈ St, finsuppTwist
      (quotientCharacter (A.map p) η) b) χ =
        c * ∑ η ∈ St, finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) := by
    intro χ
    rw [finsuppCharacterSum_smul, finsuppCharacterSum_sum]
    simp only [finsuppCharacterSum_finsuppTwist]
  refine ⟨c • ∑ η ∈ St, finsuppTwist (quotientCharacter (A.map p) η) b, ?_, ?_, ?_⟩
  · intro χ η₀ hη₀
    rw [hval, hval]
    congr 1
    refine Finset.sum_nbij' (fun η => η₀ + η) (fun η => -η₀ + η)
      (fun η hη => add_mem_orbitStabilizer p A hη₀ hη)
      (fun η hη => add_mem_orbitStabilizer p A (neg_mem_orbitStabilizer p A hη₀) hη)
      (fun η _ => by simp) (fun η _ => by simp) (fun η _ => ?_)
    simp only [quotientCharacter_add]
    exact congrArg _ (mul_assoc χ (quotientCharacter (A.map p) η₀)
      (quotientCharacter (A.map p) η))
  · rw [hval]
    have h1 : ∀ η ∈ St, finsuppCharacterSum b (1 * quotientCharacter (A.map p) η) = 1 := by
      intro η hη
      have hmem : quotientCharacter (A.map p) η ∈ T := Finset.mem_image_of_mem _ hη
      rw [show (1 : Λ →* ℂˣ) * quotientCharacter (A.map p) η = quotientCharacter (A.map p) η
        from one_mul (quotientCharacter (A.map p) η), hb _ (Finset.mem_union_left _ hmem)]
      exact ite_eq_left_of_eq_true _ _ (eq_true hmem)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hcard
  · intro χ hχ
    rw [hval]
    have h0 : ∀ η ∈ St, finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = 0 := by
      intro η hη
      have hmemT : quotientCharacter (A.map p) η ∈ T := Finset.mem_image_of_mem _ hη
      have hmemS : χ * quotientCharacter (A.map p) η ∈ S :=
        Finset.mem_union_right _ (Finset.mem_image.2 ⟨(χ, _), Finset.mem_product.2 ⟨hχ, hmemT⟩,
          rfl⟩)
      have hnT : χ * quotientCharacter (A.map p) η ∉ T := by
        intro hT'
        obtain ⟨η', hη', hq⟩ := Finset.mem_image.1 hT'
        have hχq : χ = quotientCharacter (A.map p) (η' + -η) := by
          rw [quotientCharacter_add, quotientCharacter_neg, hq]
          exact (mul_inv_cancel_right χ _).symm
        have hmem := add_mem_orbitStabilizer p A hη' (neg_mem_orbitStabilizer p A hη)
        rw [mem_orbitStabilizer_iff, nonempty_twist_inv_equiv_iff, ← hχq] at hmem
        exact (hF χ hχ).false hmem.some
      rw [hb _ hmemS]
      exact ite_eq_right_of_eq_false _ _ (eq_false hnT)
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero, mul_zero]

/-- A polynomial invariant under the stabilizer is constant on the classes of the orbit. -/
theorem finsuppCharacterSum_eq_of_equiv [Nontrivial W] {cω : A →* ℂˣ}
    (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x) {b : Λ →₀ ℂ}
    (hb : ∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ),
      η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ)
    (χ χ' : Λ →* ℂˣ) (h : Nonempty ((twist (χ.comp p) ω).Equiv (twist (χ'.comp p) ω))) :
    finsuppCharacterSum b χ = finsuppCharacterSum b χ' := by
  obtain ⟨η, hη, rfl⟩ := exists_mem_orbitStabilizer_of_equiv p A hω χ χ' h
  exact (hb χ η hη).symm

end Separation

section Tempered

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}
  {V X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G V} {τ : Representation ℂ G X}

/-- Tempered coefficients pass to a subrepresentation: smooth functionals extend. -/
theorem hasTemperedCoefficients_of_injective
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hτ : IsSmooth τ) (hπ : IsSmooth π) (i : τ.IntertwiningMap π) (hi : Function.Injective i)
    (hT : HasTemperedCoefficients Ξ σ π) : HasTemperedCoefficients Ξ σ τ := by
  intro x ℓ
  obtain ⟨ℓ', hℓ'⟩ :=
    contragredientMap_surjective_of_injective_of_compact_cofinal hcof hτ hπ i hi ℓ
  have h : (fun g => ℓ.val (τ g x)) = fun g => ℓ'.val (π g (i x)) := by
    funext g
    rw [← hℓ']
    change ℓ'.val (i (τ g x)) = _
    rw [i.isIntertwining]
  rw [h]
  exact hT (i x) ℓ'

/-- Tempered coefficients pass to a quotient. -/
theorem hasTemperedCoefficients_of_surjective (q : π.IntertwiningMap τ)
    (hq : Function.Surjective q) (hT : HasTemperedCoefficients Ξ σ π) :
    HasTemperedCoefficients Ξ σ τ := by
  intro x ℓ
  obtain ⟨v, rfl⟩ := hq x
  have h : (fun g => ℓ.val (τ g (q v))) = fun g => (contragredientMap q ℓ).val (π g v) := by
    funext g
    change _ = ℓ.val (q (π g v))
    rw [q.isIntertwining]
  rw [h]
  exact hT v _

/-- Powers of operators intertwined by `q`. -/
theorem pow_apply_of_comm {A : Module.End ℂ X} {B : Module.End ℂ V} {q : X →ₗ[ℂ] V}
    (h : ∀ x, q (A x) = B (q x)) (n : ℕ) (x : X) : q ((A ^ n) x) = (B ^ n) (q x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Module.End.mul_apply]

end Tempered


section Subquotients

universe u w

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type w} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [IsTopologicalGroup G] in
/-- A nonzero subrepresentation of a smooth representation contains an irreducible
subquotient: an injective `i : C → ρ` with image in `W` and a surjective `q : C → B` onto an
irreducible `B` (Renard III.1.4, `SmoothRep.RenardIrreducibleExistence`). -/
theorem exists_irreducible_subquotient_le (hρ : IsSmooth ρ) (W : Subrepresentation ρ)
    (hW : W ≠ ⊥) :
    ∃ (C B : SmoothRep.{0, u, w} ℂ G) (i : C.representation.IntertwiningMap ρ)
      (q : C.representation.IntertwiningMap B.representation),
      Function.Injective i ∧ (∀ x, i x ∈ W) ∧ Function.Surjective q ∧ B.IsIrreducible := by
  have hWs : IsSmooth W.toRepresentation := isSmooth_of_injective
    (subrepresentationInclusion W) (subrepresentationInclusion_injective W) hρ
  let Aw : SmoothRep.{0, u, w} ℂ G := SmoothRep.of W.toRepresentation hWs
  obtain ⟨v, hvW, hv0⟩ : ∃ v ∈ W, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hW (le_antisymm (fun v hv => h v hv) bot_le)
  have : Nontrivial Aw := ⟨⟨(⟨v, hvW⟩ : W.toSubmodule), 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨B, hB, S, T, ⟨e⟩⟩ :=
    SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient Aw
  let C := SmoothRep.subrepresentation Aw S
  let i : C.representation.IntertwiningMap ρ :=
    (subrepresentationInclusion W).comp (SmoothRep.hom (SmoothRep.subtype Aw S))
  let q : C.representation.IntertwiningMap B.representation :=
    (SmoothRep.equivOfIso e).symm.toIntertwiningMap.comp
      (SmoothRep.hom (SmoothRep.mkQ C T))
  refine ⟨C, B, i, q, ?_, ?_, ?_, hB⟩
  · exact (subrepresentationInclusion_injective W).comp (SmoothRep.subtype_injective Aw S)
  · intro x
    exact (SmoothRep.hom (SmoothRep.subtype Aw S) x).property
  · intro y
    obtain ⟨z, hz⟩ := SmoothRep.mkQ_surjective C T ((SmoothRep.equivOfIso e) y)
    refine ⟨z, ?_⟩
    change (SmoothRep.equivOfIso e).symm (SmoothRep.hom (SmoothRep.mkQ C T) z) = y
    rw [hz, Representation.Equiv.symm_apply_apply]

/-- In a modular lattice, `a ≤ c`, `b ≤ d` with `IsCompl a b` and `IsCompl c d` force
`a = c` and `b = d`. -/
theorem eq_of_le_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    {a b c d : Submodule ℂ M} (hac : a ≤ c) (hbd : b ≤ d) (hab : IsCompl a b)
    (hcd : IsCompl c d) : a = c ∧ b = d := by
  have h1 : c = a := by
    have : c = c ⊓ (a ⊔ b) := by rw [hab.sup_eq_top, inf_top_eq]
    rw [this, inf_comm, sup_inf_assoc_of_le b hac]
    have hbc : b ⊓ c = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf_right c hbd).trans (by rw [inf_comm]; exact hcd.inf_eq_bot.le))
    rw [hbc, sup_bot_eq]
  have h2 : d = b := by
    have : d = d ⊓ (b ⊔ a) := by rw [sup_comm, hab.sup_eq_top, inf_top_eq]
    rw [this, inf_comm, sup_inf_assoc_of_le a hbd]
    have had : a ⊓ d = ⊥ := eq_bot_iff.2 ((inf_le_inf_right d hac).trans hcd.inf_eq_bot.le)
    rw [had, sup_bot_eq]
  exact ⟨h1.symm, h2.symm⟩

/-- Some irreducible subquotient of `ρ` lying in the subspace `W'` is equivalent to `σ'`: there are
an injective `i : τ → ρ` with image in `W'` and a surjective `q : τ → π'` onto an irreducible `π'`
with `π' ≃ σ'`. -/
def HasSubquotientIn (ρ' : Representation ℂ G V) (W' : Submodule ℂ V) {U : Type*}
    [AddCommGroup U] [Module ℂ U] (σ' : Representation ℂ G U) : Prop :=
  ∃ (X : Type w) (_ : AddCommGroup X) (_ : Module ℂ X) (τ : Representation ℂ G X)
    (i : τ.IntertwiningMap ρ'), Function.Injective i ∧ (∀ x, i x ∈ W') ∧
    ∃ (V' : Type w) (_ : AddCommGroup V') (_ : Module ℂ V') (π' : Representation ℂ G V')
      (q : τ.IntertwiningMap π'), Function.Surjective q ∧ π'.IsIrreducible ∧
        Nonempty (π'.Equiv σ')

/-- If an irreducible subquotient of a smooth `ρ` lying in `W'` is equivalent to a representation
with a nonzero vector fixed by a compact open subgroup `H`, then `W'` contains a nonzero
`H`-fixed vector of `ρ`: fixed vectors lift along surjections (averaging over `H`). -/
theorem exists_ne_zero_fixed_of_hasSubquotientIn (hρ : IsSmooth ρ) {W' : Submodule ℂ V}
    {U : Type*} [AddCommGroup U] [Module ℂ U] {σ' : Representation ℂ G U}
    (h : HasSubquotientIn ρ W' σ') (H : OpenSubgroup G) (hH : IsCompact (H : Set G)) {u : U}
    (hu : u ∈ fixedVectors σ' H.toSubgroup) (hu0 : u ≠ 0) :
    ∃ x ∈ W' ⊓ fixedVectors ρ H.toSubgroup, x ≠ 0 := by
  obtain ⟨X, _, _, τ, i, hi, hiW, V', _, _, π', q, hq, -, ⟨e⟩⟩ := h
  have hτs : IsSmooth τ := isSmooth_of_injective i hi hρ
  have hπ's : IsSmooth π' := isSmooth_of_surjective q hq hτs
  have hu' : e.symm u ∈ fixedVectors π' H.toSubgroup := by
    intro k
    have h' := congrArg (fun T => T u) (e.symm.isIntertwining' (k : G))
    simp only [LinearMap.comp_apply] at h'
    change π' k (e.symm u) = e.symm u
    have hk : σ' k u = u := hu k
    have h'' := h'.symm
    rw [hk] at h''
    exact h''
  obtain ⟨y, hy⟩ := Langlands.Compact.fixedVectorSurjectivity G X V' τ π' hτs hπ's H hH q hq
    ⟨e.symm u, hu'⟩
  have hqy : q y.val = e.symm u := congrArg Subtype.val hy
  refine ⟨i y.val, Submodule.mem_inf.2 ⟨hiW _, ?_⟩, ?_⟩
  · intro k
    change ρ k (i y.val) = i y.val
    rw [← i.isIntertwining]
    exact congrArg i (y.property k)
  · intro h0
    apply hu0
    have hy0 : y.val = 0 := hi (h0.trans (map_zero i).symm)
    rw [hy0, map_zero] at hqy
    rw [← Representation.Equiv.apply_symm_apply e u, ← hqy, map_zero]

end Subquotients

section Decomposition

universe u v w

open scoped ENNReal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant]
  {K : Subgroup G} [CompactSpace K]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (ν : Measure (G ⧸ A)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {W : Type v} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}
  {cω : A →* ℂˣ} (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x)
  (hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν) (hiω : ω.IsIrreducible)
  [Fintype (Λ ⧸ A.map p)]
  {V : Type w} [AddCommGroup V] [Module ℂ V]

/-- **The first half of the proof of Corollary III.7.2**: an irreducible subquotient `π'` of the
Fitting range `V₁ = ⋂ₙ π(p)ⁿ V` (given by an injective `i : τ → π` with image in `V₁` and a
surjective `q : τ → π'`) lies in the orbit of `ω` at a point where the polynomial does not
vanish, i.e. `π' ≃ ω ⊗ (χ ∘ p)` with `χ` unitary and `b̂(χ) ≠ 0`. -/
theorem exists_equiv_twist_of_subquotient_fittingRange (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (b : Λ →₀ ℂ)
    (hbSt : ∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ),
      η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
    (i : τ.IntertwiningMap π) (hi : Function.Injective i)
    (hiR : ∀ x, i x ∈ fittingRange
      (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT))
    {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
    (q : τ.IntertwiningMap π') (hq : Function.Surjective q) (hiπ' : π'.IsIrreducible)
    {cπ' : A →* ℂˣ} (hπ'c : ∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x)
    (hπ'u : ∀ a : A, ‖(cπ' a : ℂ)‖ = 1)
    (hint' : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
      (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) :
    ∃ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) ∧ finsuppCharacterSum b χ ≠ 0 ∧
      Nonempty (π'.Equiv (twist (χ.comp p) ω)) := by
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  have hτa : IsAdmissible τ := isAdmissible_of_injective i hi hπa
  have hτT := hasTemperedCoefficients_of_injective hcof hτa.1 hπa.1 i hi hT
  have hπ'a : IsAdmissible π' :=
    Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective hcof q hq hτa
  have hπ'T := hasTemperedCoefficients_of_surjective q hq hτT
  set Tπ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT
  set Tτ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b τ hτa hτT
  set Tπ' :=
    orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π' hπ'a hπ'T
  have hiT : ∀ x, i (Tτ x) = Tπ (i x) := fun x => LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap
      (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
        hπa hT i)) x
  have hqT : ∀ x, q (Tτ x) = Tπ' (q x) := fun x => LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap
      (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
        hπ'a hπ'T q)) x
  have hTτinj : Function.Injective Tτ := by
    intro x y hxy
    apply hi
    refine (bijOn_fittingRange hπa hcof Tπ).injOn (hiR x) (hiR y) ?_
    rw [← hiT, ← hiT, hxy]
  have hTτsurj : Function.Surjective Tτ := by
    intro x
    obtain ⟨H, hx⟩ := exists_compactOpenSubgroup_fixed hτa.1 x
    have : Module.Finite ℂ (fixedVectors τ H.toSubgroup) := hτa.2 H.1
    have finj : Function.Injective (fixedVectorsMap Tτ H.toSubgroup) :=
      fun a b h => Subtype.ext (hTτinj (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 finj) ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  have hV'nt : Nontrivial V' := by
    have := hiπ'
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π'.asModule
  obtain ⟨v', hv'⟩ := exists_ne (0 : V')
  obtain ⟨x, rfl⟩ := hq v'
  obtain ⟨y, rfl⟩ := hTτsurj x
  have hne : Tπ' (q y) ≠ 0 := by rw [← hqT]; exact hv'
  by_contra hcon
  push Not at hcon
  by_cases hO : ∃ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) ∧ Nonempty (π'.Equiv (twist (χ.comp p) ω))
  · obtain ⟨χ, hχu, ⟨e⟩⟩ := hO
    have hb0 : finsuppCharacterSum b χ = 0 := by
      by_contra h
      exact (hcon χ hχu h).false e
    apply hne
    rw [orbitPolynomialOperator_eq_smul_of_equiv p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
      hcompat hc ht hw hD b (fun χ χ' _ _ h => finsuppCharacterSum_eq_of_equiv p A hω hbSt χ χ' h)
      hπ'a hiπ' hπ'T hint' χ hχu e, hb0, zero_smul]
  · push Not at hO
    apply hne
    exact orbitPolynomialOperator_eq_zero p A hA ν hcof hω hsq hiω hp hN hHN hm hcompat hc ht hw
      hD b hπ'a hiπ' hπ'T hπ'c hπ'u hint' hO _

/-- **The second half of the proof of Corollary III.7.2**: if `b̂(1) = 1`, no irreducible
subquotient `π'` of the Fitting kernel `V₂ = ⋃ₙ Ker π(p)ⁿ` (given by an injective `i : τ → π`
with image in `V₂` and a surjective `q : τ → π'`) is equivalent to `ω`. -/
theorem isEmpty_equiv_of_subquotient_fittingKernel (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (b : Λ →₀ ℂ)
    (hbSt : ∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ),
      η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ)
    (hb1 : finsuppCharacterSum b 1 = 1)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
    (i : τ.IntertwiningMap π) (hi : Function.Injective i)
    (hiK : ∀ x, i x ∈ fittingKernel
      (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT))
    {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
    (q : τ.IntertwiningMap π') (hq : Function.Surjective q) (hiπ' : π'.IsIrreducible)
    (hint' : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
      (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) :
    IsEmpty (π'.Equiv ω) := by
  refine ⟨fun e => ?_⟩
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  have hτa : IsAdmissible τ := isAdmissible_of_injective i hi hπa
  have hτT := hasTemperedCoefficients_of_injective hcof hτa.1 hπa.1 i hi hT
  have hπ'a : IsAdmissible π' :=
    Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective hcof q hq hτa
  have hπ'T := hasTemperedCoefficients_of_surjective q hq hτT
  set Tπ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT
  set Tτ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b τ hτa hτT
  set Tπ' :=
    orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π' hπ'a hπ'T
  have hiT : ∀ x, i (Tτ x) = Tπ (i x) := fun x => LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap
      (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
        hπa hT i)) x
  have hqT : ∀ x, q (Tτ x) = Tπ' (q x) := fun x => LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap
      (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
        hπ'a hπ'T q)) x
  -- `π'(p)` is the identity, since `π' ≃ ω = ω ⊗ (1 ∘ p)` and `b̂(1) = 1`
  have h1 : (1 : Λ →* ℂˣ).comp p = 1 := MonoidHom.one_comp p
  let e' : π'.Equiv (twist ((1 : Λ →* ℂˣ).comp p) ω) :=
    e.trans (equivOfRepresentationEq (by rw [h1, twist_one])).symm
  have hid : ∀ v, Tπ' v = v := fun v => by
    rw [orbitPolynomialOperator_eq_smul_of_equiv p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
      hcompat hc ht hw hD b (fun χ χ' _ _ h => finsuppCharacterSum_eq_of_equiv p A hω hbSt χ χ' h)
      hπ'a hiπ' hπ'T hint' 1 (fun l => by simp) e', hb1, one_smul]
  have hV'nt : Nontrivial V' := by
    have := hiπ'
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π'.asModule
  obtain ⟨v', hv'⟩ := exists_ne (0 : V')
  obtain ⟨x, rfl⟩ := hq v'
  obtain ⟨n, hn⟩ := mem_fittingKernel_iff.1 (hiK x)
  have hτn : (Tτ.toLinearMap ^ n) x = 0 := by
    apply hi
    have h := pow_apply_of_comm (q := i.toLinearMap) (A := Tτ.toLinearMap)
      (B := Tπ.toLinearMap) (fun y => hiT y) n x
    change i ((Tτ.toLinearMap ^ n) x) = (Tπ.toLinearMap ^ n) (i x) at h
    rw [map_zero, h]
    exact hn
  have hq0 : (Tπ'.toLinearMap ^ n) (q x) = 0 := by
    have h := pow_apply_of_comm (q := q.toLinearMap) (A := Tτ.toLinearMap)
      (B := Tπ'.toLinearMap) (fun y => hqT y) n x
    change q ((Tτ.toLinearMap ^ n) x) = (Tπ'.toLinearMap ^ n) (q x) at h
    rw [← h, hτn, map_zero]
  have hpow : ∀ k : ℕ, (Tπ'.toLinearMap ^ k) (q x) = q x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      change (Tπ'.toLinearMap ^ k) (Tπ' (q x)) = q x
      rw [hid, ih]
  exact hv' ((hpow n).symm.trans hq0)

include hcof hsq hiω in
/-- **Corollary III.7.2 (existence of the decomposition)**: for a finite set `F` of characters `χ`
with `ω ⊗ (χ ∘ p) ≄ ω`, an admissible tempered `π` decomposes as `V = V₁ ⊕ V₂` into
subrepresentations such that (i) every irreducible subquotient of `V₁` (satisfying the
hypotheses of Proposition III.7.1) is equivalent to some `ω ⊗ (χ ∘ p)`, `χ` unitary, and to no
`ω ⊗ (χ₀ ∘ p)` with `χ₀ ∈ F`; (ii) no irreducible subquotient of `V₂` is equivalent to `ω`. When
`F` contains a representative of every class `≠ ω` of the orbit occurring in `π`, (i) says that
every irreducible subquotient of `V₁` is equivalent to `ω`. -/
theorem exists_isCompl_orbitIsotypic (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (F : Finset (Λ →* ℂˣ)) (hF : ∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω))
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π) :
    ∃ V₁ V₂ : Subrepresentation π, IsCompl V₁.toSubmodule V₂.toSubmodule ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
        (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁) →
        ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
        (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
        ∀ {cπ' : A →* ℂˣ}, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) →
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) →
        (∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) →
        ∃ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) ∧
          Nonempty (π'.Equiv (twist (χ.comp p) ω)) ∧
          ∀ χ₀ ∈ F, IsEmpty (π'.Equiv (twist (χ₀.comp p) ω))) ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
        (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂) →
        ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
        (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
        (∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) →
        IsEmpty (π'.Equiv ω)) := by
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  obtain ⟨b, hbSt, hb1, hbF⟩ := exists_orbit_separating p A F hF
  set Tπ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT
  refine ⟨fittingRange Tπ, fittingKernel Tπ, isCompl_fittingRange_fittingKernel hπa hcof Tπ,
    ?_, ?_⟩
  · intro X _ _ τ i hi hiR V' _ _ π' q hq hiπ' cπ' hπ'c hπ'u hint'
    obtain ⟨χ, hχu, hχb, he⟩ := exists_equiv_twist_of_subquotient_fittingRange p A hA ν hcof hω
      hsq hiω hp hN hHN hm hm0 hcompat hc ht hw hD b hbSt hπa hT i hi hiR q hq hiπ' hπ'c hπ'u
      hint'
    refine ⟨χ, hχu, he, fun χ₀ hχ₀ => ⟨fun e₀ => hχb ?_⟩⟩
    obtain ⟨e⟩ := he
    rw [finsuppCharacterSum_eq_of_equiv p A hω hbSt χ χ₀ ⟨e.symm.trans e₀⟩, hbF χ₀ hχ₀]
  · intro X _ _ τ i hi hiK V' _ _ π' q hq hiπ' hint'
    exact isEmpty_equiv_of_subquotient_fittingKernel p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
      hcompat hc ht hw hD b hbSt hb1 hπa hT i hi hiK q hq hiπ' hint'

include hcof hsq hiω in
/-- **Corollary III.7.2 (uniqueness of the decomposition), comparison step**: a decomposition
`V = V₁ ⊕ V₂` into subrepresentations with (i) every irreducible subquotient of `V₁` equivalent
to `ω` and (ii) none of `V₂` equivalent to `ω` is the Fitting decomposition of `π(p)`, for a
polynomial `b` invariant under the stabilizer with `b̂(1) = 1` such that every irreducible
subquotient of `π` equivalent to `ω ⊗ (χ ∘ p)`, `χ` unitary, `b̂(χ) ≠ 0`, is equivalent to `ω`
(`hO`); every irreducible subquotient of `π` is assumed to satisfy the hypotheses of
Proposition III.7.1 (`hsub`). -/
theorem eq_fitting_of_orbitIsotypic (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (b : Λ →₀ ℂ)
    (hbSt : ∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ),
      η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ)
    (hb1 : finsuppCharacterSum b 1 = 1)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (hO : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → finsuppCharacterSum b χ ≠ 0 →
        Nonempty (π'.Equiv (twist (χ.comp p) ω)) → Nonempty (π'.Equiv ω))
    {V₁ V₂ : Subrepresentation π} (h12 : IsCompl V₁.toSubmodule V₂.toSubmodule)
    (h1 : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω))
    (h2 : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) :
    V₁ = fittingRange
        (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT) ∧
      V₂ = fittingKernel
        (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT) := by
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  set T := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT
  -- the operator `π(p)` of an admissible tempered representation embedded in `π`
  have hcomm : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (hτa : IsAdmissible τ) (hτT : HasTemperedCoefficients Ξ σ τ)
      {Y : Type w} [AddCommGroup Y] [Module ℂ Y] {τ' : Representation ℂ G Y}
      (hτ'a : IsAdmissible τ') (hτ'T : HasTemperedCoefficients Ξ σ τ')
      (f : τ.IntertwiningMap τ') (x : X),
      f (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b τ hτa hτT x) =
        orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b τ' hτ'a hτ'T
          (f x) :=
    fun hτa hτT _ _ _ _ hτ'a hτ'T f x => LinearMap.congr_fun
      (congrArg Representation.IntertwiningMap.toLinearMap
        (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
          hτ'a hτ'T f)) x
  -- `π(p)` is the identity on an irreducible subquotient equivalent to `ω`
  have hid : ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (hπ'a : IsAdmissible π') (hπ'T : HasTemperedCoefficients Ξ σ π') (hiπ' : π'.IsIrreducible)
      (hint' : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
        (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
          Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
      (e : π'.Equiv ω) (v : V'),
      orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π' hπ'a hπ'T v =
        v := by
    intro V' _ _ π' hπ'a hπ'T hiπ' hint' e v
    have h1' : (1 : Λ →* ℂˣ).comp p = 1 := MonoidHom.one_comp p
    let e' : π'.Equiv (twist ((1 : Λ →* ℂˣ).comp p) ω) :=
      e.trans (equivOfRepresentationEq (by rw [h1', twist_one])).symm
    rw [orbitPolynomialOperator_eq_smul_of_equiv p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
      hcompat hc ht hw hD b (fun χ χ' _ _ h => finsuppCharacterSum_eq_of_equiv p A hω hbSt χ χ' h)
      hπ'a hiπ' hπ'T hint' 1 (fun l => by simp) e', hb1, one_smul]
  -- step 1: `V₁ ≤ fittingRange π(p)`
  have hV₁ : V₁.toSubmodule ≤ (fittingRange T).toSubmodule := by
    let i₁ := subrepresentationInclusion V₁
    have hi₁ := subrepresentationInclusion_injective V₁
    have hτa : IsAdmissible V₁.toRepresentation := isAdmissible_of_injective i₁ hi₁ hπa
    have hτT := hasTemperedCoefficients_of_injective hcof hτa.1 hπa.1 i₁ hi₁ hT
    set T₁ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b
      V₁.toRepresentation hτa hτT
    have hinj : Function.Injective T₁ := by
      change Function.Injective T₁.toLinearMap
      rw [← LinearMap.ker_eq_bot]
      by_contra hne
      let Kr : Subrepresentation V₁.toRepresentation :=
        { toSubmodule := LinearMap.ker T₁.toLinearMap
          apply_mem_toSubmodule := fun g v hv => by
            rw [LinearMap.mem_ker] at hv ⊢
            have h := LinearMap.congr_fun (T₁.isIntertwining' g) v
            simp only [LinearMap.comp_apply] at h
            rw [h, hv, map_zero] }
      have hKr : Kr ≠ ⊥ := fun h => hne (by
        rw [eq_bot_iff]
        intro v hv
        have : v ∈ Kr := hv
        rw [h] at this
        exact this)
      obtain ⟨C, B, i', q', hi', hi'K, hq', hB⟩ := exists_irreducible_subquotient_le hτa.1 Kr hKr
      let j := i₁.comp i'
      have hj : Function.Injective j := hi₁.comp hi'
      obtain ⟨cB, hBc, hBu, hintB⟩ := hsub j hj q' hq' hB
      obtain ⟨e⟩ := h1 j hj (fun y => (i' y).property) q' hq' hB
      have hCa : IsAdmissible C.representation := isAdmissible_of_injective j hj hπa
      have hCT := hasTemperedCoefficients_of_injective hcof hCa.1 hπa.1 j hj hT
      have hBa : IsAdmissible B.representation :=
        Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective hcof q' hq' hCa
      have hBT := hasTemperedCoefficients_of_surjective q' hq' hCT
      have hB0 : ∀ y, q' y = 0 := by
        intro y
        have hTC : orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b
            C.representation hCa hCT y = 0 := by
          apply hi'
          rw [hcomm hCa hCT hτa hτT i' y, map_zero]
          exact hi'K y
        have := hcomm hCa hCT hBa hBT q' y
        rw [hTC, map_zero, hid hBa hBT hB hintB e] at this
        exact this.symm
      have hBnt : Nontrivial B := by
        have := hB
        exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) B.representation.asModule
      obtain ⟨z, hz⟩ := exists_ne (0 : B)
      obtain ⟨y, rfl⟩ := hq' z
      exact hz (hB0 y)
    have hK₁ : (fittingKernel T₁).toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨n, hn⟩ := mem_fittingKernel_iff.1 hx
      have hinjn : Function.Injective (T₁.toLinearMap ^ n) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate n
      exact hinjn (hn.trans (map_zero _).symm)
    have hR₁ : (fittingRange T₁).toSubmodule = ⊤ := by
      have := (isCompl_fittingRange_fittingKernel hτa hcof T₁).sup_eq_top
      rwa [hK₁, sup_bot_eq] at this
    intro v hv
    have hx : (⟨v, hv⟩ : V₁.toSubmodule) ∈ (fittingRange T₁).toSubmodule := by
      rw [hR₁]
      exact Submodule.mem_top
    have hx' : (⟨v, hv⟩ : V₁.toSubmodule) ∈ fittingRange T₁ := hx
    rw [mem_fittingRange_iff] at hx'
    change v ∈ fittingRange T
    rw [mem_fittingRange_iff]
    intro n
    obtain ⟨y, hy⟩ := hx' n
    refine ⟨i₁ y, ?_⟩
    have h := pow_apply_of_comm (q := i₁.toLinearMap) (A := T₁.toLinearMap) (B := T.toLinearMap)
      (fun z => hcomm hτa hτT hπa hT i₁ z) n y
    change i₁ ((T₁.toLinearMap ^ n) y) = (T.toLinearMap ^ n) (i₁ y) at h
    rw [← h, hy]
    rfl
  -- step 2: `V₂ ≤ fittingKernel π(p)`
  have hV₂ : V₂.toSubmodule ≤ (fittingKernel T).toSubmodule := by
    let i₂ := subrepresentationInclusion V₂
    have hi₂ := subrepresentationInclusion_injective V₂
    have hτa : IsAdmissible V₂.toRepresentation := isAdmissible_of_injective i₂ hi₂ hπa
    have hτT := hasTemperedCoefficients_of_injective hcof hτa.1 hπa.1 i₂ hi₂ hT
    set T₂ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b
      V₂.toRepresentation hτa hτT
    have hpow2 : ∀ (n : ℕ) (y : V₂.toSubmodule),
        i₂ ((T₂.toLinearMap ^ n) y) = (T.toLinearMap ^ n) (i₂ y) := fun n y =>
      pow_apply_of_comm (q := i₂.toLinearMap) (A := T₂.toLinearMap) (B := T.toLinearMap)
        (fun z => hcomm hτa hτT hπa hT i₂ z) n y
    have hR₂ : fittingRange T₂ = ⊥ := by
      by_contra hne
      obtain ⟨C, B, i', q', hi', hi'R, hq', hB⟩ :=
        exists_irreducible_subquotient_le hτa.1 (fittingRange T₂) hne
      let j := i₂.comp i'
      have hj : Function.Injective j := hi₂.comp hi'
      have hjV : ∀ y, j y ∈ V₂ := fun y => (i' y).property
      have hjR : ∀ y, j y ∈ fittingRange T := by
        intro y
        rw [mem_fittingRange_iff]
        intro n
        obtain ⟨z, hz⟩ := mem_fittingRange_iff.1 (hi'R y) n
        exact ⟨i₂ z, by rw [← hpow2, hz]; rfl⟩
      obtain ⟨cB, hBc, hBu, hintB⟩ := hsub j hj q' hq' hB
      obtain ⟨χ, hχu, hχb, he⟩ := exists_equiv_twist_of_subquotient_fittingRange p A hA ν hcof hω
        hsq hiω hp hN hHN hm hm0 hcompat hc ht hw hD b hbSt hπa hT j hj hjR q' hq' hB hBc hBu
        hintB
      exact (h2 j hj hjV q' hq' hB).false (hO j hj q' hq' hB χ hχu hχb he).some
    have hK₂ : (fittingKernel T₂).toSubmodule = ⊤ := by
      have := (isCompl_fittingRange_fittingKernel hτa hcof T₂).sup_eq_top
      rwa [hR₂, show (⊥ : Subrepresentation V₂.toRepresentation).toSubmodule = ⊥ from rfl,
        bot_sup_eq] at this
    intro v hv
    have hx : (⟨v, hv⟩ : V₂.toSubmodule) ∈ (fittingKernel T₂).toSubmodule := by
      rw [hK₂]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ := mem_fittingKernel_iff.1 hx
    change v ∈ fittingKernel T
    rw [mem_fittingKernel_iff]
    refine ⟨n, ?_⟩
    have h := hpow2 n ⟨v, hv⟩
    rw [hn, map_zero] at h
    exact h.symm
  -- step 3: the two decompositions coincide
  obtain ⟨e1, e2⟩ := eq_of_le_of_isCompl hV₁ hV₂ h12
    (isCompl_fittingRange_fittingKernel hπa hcof T)
  exact ⟨Subrepresentation.toSubmodule_injective e1, Subrepresentation.toSubmodule_injective e2⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [A.Normal]
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)] in
include hω hiω in
/-- The polynomial of `exists_orbit_separating` detects `ω` among the irreducible subquotients
of `π` lying in its orbit, when `F` covers the other classes occurring in `π` (`hcover`). -/
theorem exists_orbit_separating_of_covering
    (F : Finset (Λ →* ℂˣ)) (hF : ∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω))
    {π : Representation ℂ G V}
    (hcover : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → Nonempty (π'.Equiv (twist (χ.comp p) ω)) →
        Nonempty (π'.Equiv ω) ∨ ∃ χ₀ ∈ F, Nonempty (π'.Equiv (twist (χ₀.comp p) ω))) :
    ∃ b : Λ →₀ ℂ,
      (∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ), η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ) ∧
      finsuppCharacterSum b 1 = 1 ∧
      ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
        (i : τ.IntertwiningMap π), Function.Injective i →
        ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
        (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
        ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → finsuppCharacterSum b χ ≠ 0 →
          Nonempty (π'.Equiv (twist (χ.comp p) ω)) → Nonempty (π'.Equiv ω) := by
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  obtain ⟨b, hbSt, hb1, hbF⟩ := exists_orbit_separating p A F hF
  refine ⟨b, hbSt, hb1, ?_⟩
  intro X _ _ τ i hi V' _ _ π' q hq hiπ' χ hχu hχb he
  rcases hcover i hi q hq hiπ' χ hχu he with h | ⟨χ₀, hχ₀, ⟨e₀⟩⟩
  · exact h
  · obtain ⟨e⟩ := he
    exact absurd (by rw [finsuppCharacterSum_eq_of_equiv p A hω hbSt χ χ₀ ⟨e.symm.trans e₀⟩,
      hbF χ₀ hχ₀]) hχb

include hcof hsq hiω in
/-- **Corollary III.7.2 (existence)**, in the form of the source: if `F` covers the classes of
the orbit of `ω` other than `ω` that occur as irreducible subquotients of `π` (`hcover`, the
source's finiteness of `Σ`) and the irreducible subquotients of `π` satisfy the hypotheses of
Proposition III.7.1 (`hsub`), then `V = V₁ ⊕ V₂` with (i) every irreducible subquotient of `V₁`
equivalent to `ω` and (ii) no irreducible subquotient of `V₂` equivalent to `ω`. -/
theorem exists_orbitIsotypic_decomposition (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (F : Finset (Λ →* ℂˣ)) (hF : ∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω))
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hcover : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → Nonempty (π'.Equiv (twist (χ.comp p) ω)) →
        Nonempty (π'.Equiv ω) ∨ ∃ χ₀ ∈ F, Nonempty (π'.Equiv (twist (χ₀.comp p) ω)))
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) :
    ∃ V₁ V₂ : Subrepresentation π, IsCompl V₁.toSubmodule V₂.toSubmodule ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω)) ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) := by
  obtain ⟨V₁, V₂, h12, h1, h2⟩ := exists_isCompl_orbitIsotypic p A hA ν hcof hω hsq hiω hp hN hHN
    hm hm0 hcompat hc ht hw hD F hF hπa hT
  refine ⟨V₁, V₂, h12, ?_, ?_⟩
  swap
  · intro X _ _ τ i hi hiV V' _ _ π' q hq hiπ'
    exact h2 i hi hiV q hq hiπ' (hsub i hi q hq hiπ').choose_spec.2.2
  intro X _ _ τ i hi hiV V' _ _ π' q hq hiπ'
  obtain ⟨cπ', hπ'c, hπ'u, hint'⟩ := hsub i hi q hq hiπ'
  obtain ⟨χ, hχu, he, hnF⟩ := h1 i hi hiV q hq hiπ' hπ'c hπ'u hint'
  rcases hcover i hi q hq hiπ' χ hχu he with h | ⟨χ₀, hχ₀, he₀⟩
  · exact h
  · exact ((hnF χ₀ hχ₀).false he₀.some).elim

include hcof hsq hiω in
/-- **Corollary III.7.2 (uniqueness)**: under the hypotheses of
`exists_orbitIsotypic_decomposition`, two decompositions `V = V₁ ⊕ V₂ = V₁' ⊕ V₂'` with
properties (i) and (ii) coincide. -/
theorem orbitIsotypic_decomposition_unique (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (F : Finset (Λ →* ℂˣ)) (hF : ∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω))
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hcover : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → Nonempty (π'.Equiv (twist (χ.comp p) ω)) →
        Nonempty (π'.Equiv ω) ∨ ∃ χ₀ ∈ F, Nonempty (π'.Equiv (twist (χ₀.comp p) ω)))
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    {V₁ V₂ V₁' V₂' : Subrepresentation π} (h12 : IsCompl V₁.toSubmodule V₂.toSubmodule)
    (h1 : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω))
    (h2 : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω))
    (h12' : IsCompl V₁'.toSubmodule V₂'.toSubmodule)
    (h1' : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁') →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω))
    (h2' : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂') →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) :
    V₁ = V₁' ∧ V₂ = V₂' := by
  obtain ⟨b, hbSt, hb1, hO⟩ := exists_orbit_separating_of_covering p A hω hiω F hF hcover
  obtain ⟨e1, e2⟩ := eq_fitting_of_orbitIsotypic p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
    hcompat hc ht hw hD b hbSt hb1 hπa hT hsub hO h12 h1 h2
  obtain ⟨e1', e2'⟩ := eq_fitting_of_orbitIsotypic p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
    hcompat hc ht hw hD b hbSt hb1 hπa hT hsub hO h12' h1' h2'
  exact ⟨e1.trans e1'.symm, e2.trans e2'.symm⟩

include hcof hsq hiω in
/-- **Splitting an irreducible subquotient along the decomposition of the proof of Corollary
III.7.2**: if an irreducible subquotient of `π` lying in `W'` is equivalent to `ω ⊗ (χ ∘ p)`, `χ`
unitary, then it occurs in `W' ∩ V₁` when `b̂(χ) ≠ 0` and in `W' ∩ V₂` when `b̂(χ) = 0`, where
`V₁`, `V₂` are the Fitting range and kernel of `π(p)`. -/
theorem hasSubquotientIn_fitting (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (b : Λ →₀ ℂ)
    (hbSt : ∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ),
      η ∈ orbitStabilizer p A ω →
        finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) = finsuppCharacterSum b χ)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (W' : Submodule ℂ V) (χ : Λ →* ℂˣ) (hχu : ∀ l, ‖(χ l : ℂ)‖ = 1)
    (h : HasSubquotientIn π W' (twist (χ.comp p) ω)) :
    (finsuppCharacterSum b χ ≠ 0 → HasSubquotientIn π
      (W' ⊓ (fittingRange (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT)).toSubmodule) (twist (χ.comp p) ω)) ∧
    (finsuppCharacterSum b χ = 0 → HasSubquotientIn π
      (W' ⊓ (fittingKernel (orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT)).toSubmodule) (twist (χ.comp p) ω)) := by
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  obtain ⟨X, _, _, τ, i, hi, hiW, V', _, _, π', q, hq, hiπ', ⟨e⟩⟩ := h
  obtain ⟨cπ', -, -, hint'⟩ := hsub i hi q hq hiπ'
  have hτa : IsAdmissible τ := isAdmissible_of_injective i hi hπa
  have hτT := hasTemperedCoefficients_of_injective hcof hτa.1 hπa.1 i hi hT
  have hπ'a : IsAdmissible π' :=
    Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective hcof q hq hτa
  have hπ'T := hasTemperedCoefficients_of_surjective q hq hτT
  set Tπ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT
  set Tτ := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b τ hτa hτT
  set Tπ' := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π' hπ'a hπ'T
  have hiT : ∀ x, i (Tτ x) = Tπ (i x) := fun x => LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap
      (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
        hπa hT i)) x
  have hqT : ∀ x, q (Tτ x) = Tπ' (q x) := fun x => LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap
      (orbitPolynomialOperator_comp p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b hτa hτT
        hπ'a hπ'T q)) x
  have hsc : ∀ v, Tπ' v = finsuppCharacterSum b χ • v := fun v =>
    orbitPolynomialOperator_eq_smul_of_equiv p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
      hcompat hc ht hw hD b (fun χ χ' _ _ h => finsuppCharacterSum_eq_of_equiv p A hω hbSt χ χ' h)
      hπ'a hiπ' hπ'T hint' χ hχu e v
  have hpowi : ∀ (n : ℕ) (x : X), i ((Tτ.toLinearMap ^ n) x) = (Tπ.toLinearMap ^ n) (i x) :=
    fun n x => pow_apply_of_comm (q := i.toLinearMap) (A := Tτ.toLinearMap)
      (B := Tπ.toLinearMap) (fun y => hiT y) n x
  have hpowq : ∀ (n : ℕ) (x : X), q ((Tτ.toLinearMap ^ n) x) = (Tπ'.toLinearMap ^ n) (q x) :=
    fun n x => pow_apply_of_comm (q := q.toLinearMap) (A := Tτ.toLinearMap)
      (B := Tπ'.toLinearMap) (fun y => hqT y) n x
  have hpowsc : ∀ (n : ℕ) (v : V'),
      (Tπ'.toLinearMap ^ n) v = finsuppCharacterSum b χ ^ n • v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply]
      change (Tπ'.toLinearMap ^ n) (Tπ' v) = _
      rw [hsc, map_smul, ih, smul_smul, pow_succ']
  have hdec : ∀ x : X, ∃ r ∈ (fittingRange Tτ).toSubmodule,
      ∃ k ∈ (fittingKernel Tτ).toSubmodule, r + k = x := by
    intro x
    have hx : x ∈ (fittingRange Tτ).toSubmodule ⊔ (fittingKernel Tτ).toSubmodule := by
      rw [(isCompl_fittingRange_fittingKernel hτa hcof Tτ).sup_eq_top]
      exact Submodule.mem_top
    exact Submodule.mem_sup.1 hx
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · let R := fittingRange Tτ
    refine ⟨R.toSubmodule, inferInstance, inferInstance, R.toRepresentation,
      i.comp (subrepresentationInclusion R), hi.comp (subrepresentationInclusion_injective R),
      fun x => Submodule.mem_inf.2 ⟨hiW _, ?_⟩, V', inferInstance, inferInstance, π',
      q.comp (subrepresentationInclusion R), ?_, hiπ', ⟨e⟩⟩
    · change i x.val ∈ fittingRange Tπ
      rw [mem_fittingRange_iff]
      intro n
      obtain ⟨y, hy⟩ := mem_fittingRange_iff.1 x.property n
      exact ⟨i y, by rw [← hpowi, hy]⟩
    · intro v'
      obtain ⟨x, rfl⟩ := hq v'
      obtain ⟨r, hr, k, hk, rfl⟩ := hdec x
      refine ⟨⟨r, hr⟩, ?_⟩
      change q r = q (r + k)
      obtain ⟨n, hn⟩ := mem_fittingKernel_iff.1 hk
      have hk0 : finsuppCharacterSum b χ ^ n • q k = 0 := by
        rw [← hpowsc, ← hpowq, hn, map_zero]
      rw [map_add, (smul_eq_zero.1 hk0).resolve_left (pow_ne_zero n hb), add_zero]
  · let N := fittingKernel Tτ
    refine ⟨N.toSubmodule, inferInstance, inferInstance, N.toRepresentation,
      i.comp (subrepresentationInclusion N), hi.comp (subrepresentationInclusion_injective N),
      fun x => Submodule.mem_inf.2 ⟨hiW _, ?_⟩, V', inferInstance, inferInstance, π',
      q.comp (subrepresentationInclusion N), ?_, hiπ', ⟨e⟩⟩
    · change i x.val ∈ fittingKernel Tπ
      obtain ⟨n, hn⟩ := mem_fittingKernel_iff.1 x.property
      exact mem_fittingKernel_iff.2 ⟨n, by rw [← hpowi, hn, map_zero]⟩
    · intro v'
      obtain ⟨x, rfl⟩ := hq v'
      obtain ⟨r, hr, k, hk, rfl⟩ := hdec x
      refine ⟨⟨k, hk⟩, ?_⟩
      change q k = q (r + k)
      obtain ⟨y, hy⟩ := mem_fittingRange_iff.1 hr 1
      have hr0 : q r = 0 := by
        rw [← hy, hpowq, hpowsc, hb, zero_pow one_ne_zero, zero_smul]
      rw [map_add, hr0, zero_add]

include hcof hsq hiω in
/-- **The finiteness of `Σ` in the proof of Corollary III.7.2, counting form**: if the twists
`ω ⊗ (χ ∘ p)`, `χ ∈ F` unitary, are pairwise inequivalent and all occur as irreducible
subquotients of `π` lying in `W'`, and `ω` has a nonzero vector fixed by the compact open
subgroup `H`, then `|F| ≤ dim (W' ∩ V^H)`. -/
theorem card_le_finrank_of_hasSubquotientIn (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (H : CompactOpenSubgroup G) {u : W} (hu : u ∈ fixedVectors ω H.toSubgroup) (hu0 : u ≠ 0)
    (F : Finset (Λ →* ℂˣ)) (hFu : ∀ χ ∈ F, ∀ l, ‖(χ l : ℂ)‖ = 1)
    (hFi : ∀ χ ∈ F, ∀ χ' ∈ F,
      Nonempty ((twist (χ.comp p) ω).Equiv (twist (χ'.comp p) ω)) → χ = χ')
    (W' : Submodule ℂ V) (hW' : ∀ χ ∈ F, HasSubquotientIn π W' (twist (χ.comp p) ω)) :
    F.card ≤ Module.finrank ℂ (W' ⊓ fixedVectors π H.toSubgroup : Submodule ℂ V) := by
  classical
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  have hfixed : ∀ χ : Λ →* ℂˣ, u ∈ fixedVectors (twist (χ.comp p) ω) H.toSubgroup := by
    intro χ
    rw [fixedVectors_twist_eq_of_le_ker _ _ _ fun h hh => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 (hHN H hh), map_one]]
    exact hu
  induction F using Finset.induction_on generalizing W' with
  | empty => simp
  | insert χ₁ F hχ₁ ih =>
    have hF' : ∀ χ ∈ F.image (fun χ => χ * χ₁⁻¹), IsEmpty ((twist (χ.comp p) ω).Equiv ω) := by
      intro χ' hχ'
      obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hχ'
      refine ⟨fun f => hχ₁ ?_⟩
      have hchar : χ₁.comp p * (χ * χ₁⁻¹).comp p = χ.comp p := by
        ext g
        simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply]
        rw [mul_comm (χ (p g)), mul_inv_cancel_left]
      have f' : (twist (χ.comp p) ω).Equiv (twist (χ₁.comp p) ω) :=
        (equivOfRepresentationEq (by rw [twist_twist, hchar])).symm.trans
          (twistEquiv (χ₁.comp p) f)
      have hχχ₁ := hFi χ (Finset.mem_insert_of_mem hχ) χ₁ (Finset.mem_insert_self _ _) ⟨f'⟩
      exact hχχ₁ ▸ hχ
    obtain ⟨b₀, hb₀St, hb₀1, hb₀F⟩ := exists_orbit_separating p A _ hF'
    set b := finsuppTwist χ₁⁻¹ b₀ with hbdef
    have hbχ : ∀ χ, finsuppCharacterSum b χ = finsuppCharacterSum b₀ (χ * χ₁⁻¹) := fun χ =>
      finsuppCharacterSum_finsuppTwist _ _ _
    have hbSt : ∀ (χ : Λ →* ℂˣ) (η : AddChar (Additive (Λ ⧸ A.map p)) ℂ),
        η ∈ orbitStabilizer p A ω →
          finsuppCharacterSum b (χ * quotientCharacter (A.map p) η) =
            finsuppCharacterSum b χ := by
      intro χ η hη
      rw [hbχ, hbχ, ← hb₀St (χ * χ₁⁻¹) η hη]
      exact congrArg _ (mul_right_comm χ (quotientCharacter (A.map p) η) χ₁⁻¹)
    have hb1 : finsuppCharacterSum b χ₁ ≠ 0 := by
      rw [hbχ, show χ₁ * χ₁⁻¹ = 1 from mul_inv_cancel χ₁, hb₀1]
      exact one_ne_zero
    have hb0 : ∀ χ ∈ F, finsuppCharacterSum b χ = 0 := fun χ hχ => by
      rw [hbχ]
      exact hb₀F _ (Finset.mem_image_of_mem _ hχ)
    set T := orbitPolynomialOperator p A hA ν hcof hω hsq hiω hN hHN hc ht hw hD m b π hπa hT
    have hR := (hasSubquotientIn_fitting p A hA ν hcof hω hsq hiω hp hN hHN hm hm0 hcompat hc ht
      hw hD b hbSt hπa hT hsub W' χ₁ (hFu χ₁ (Finset.mem_insert_self _ _))
      (hW' χ₁ (Finset.mem_insert_self _ _))).1 hb1
    obtain ⟨x, hx, hx0⟩ := exists_ne_zero_fixed_of_hasSubquotientIn hπa.1 hR H.1 H.2
      (hfixed χ₁) hu0
    have hK : ∀ χ ∈ F, HasSubquotientIn π (W' ⊓ (fittingKernel T).toSubmodule)
        (twist (χ.comp p) ω) := fun χ hχ =>
      (hasSubquotientIn_fitting p A hA ν hcof hω hsq hiω hp hN hHN hm hm0 hcompat hc ht hw hD b
        hbSt hπa hT hsub W' χ (hFu χ (Finset.mem_insert_of_mem hχ))
        (hW' χ (Finset.mem_insert_of_mem hχ))).2 (hb0 χ hχ)
    have hIH := ih (fun χ hχ => hFu χ (Finset.mem_insert_of_mem hχ))
      (fun χ hχ χ' hχ' => hFi χ (Finset.mem_insert_of_mem hχ) χ' (Finset.mem_insert_of_mem hχ'))
      _ hK
    have : Module.Finite ℂ (fixedVectors π H.toSubgroup) := hπa.2 H.1
    have : FiniteDimensional ℂ (W' ⊓ fixedVectors π H.toSubgroup : Submodule ℂ V) :=
      Submodule.finiteDimensional_of_le inf_le_right
    have hlt : W' ⊓ (fittingKernel T).toSubmodule ⊓ fixedVectors π H.toSubgroup <
        W' ⊓ fixedVectors π H.toSubgroup := by
      refine lt_of_le_of_ne (inf_le_inf_right _ inf_le_left) fun heq => hx0 ?_
      obtain ⟨hxWR, hxH⟩ := Submodule.mem_inf.1 hx
      obtain ⟨hxW, hxR⟩ := Submodule.mem_inf.1 hxWR
      have hxmem : x ∈ W' ⊓ fixedVectors π H.toSubgroup := Submodule.mem_inf.2 ⟨hxW, hxH⟩
      rw [← heq] at hxmem
      have hxK : x ∈ (fittingKernel T).toSubmodule :=
        (Submodule.mem_inf.1 (Submodule.mem_inf.1 hxmem).1).2
      exact (Submodule.disjoint_def.1 (isCompl_fittingRange_fittingKernel hπa hcof T).disjoint)
        x hxR hxK
    have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
    rw [Finset.card_insert_of_notMem hχ₁]
    omega

include hcof hsq hiω in
/-- **The finiteness of `Σ` in the proof of Corollary III.7.2**: there is a finite set `F` of
characters `χ` with `ω ⊗ (χ ∘ p) ≄ ω` such that every irreducible subquotient of `π` equivalent
to some `ω ⊗ (χ ∘ p)`, `χ` unitary, is equivalent to `ω` or to some `ω ⊗ (χ₀ ∘ p)` with
`χ₀ ∈ F` (the hypothesis `hcover` of `exists_orbitIsotypic_decomposition`). -/
theorem exists_orbit_covering (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) :
    ∃ F : Finset (Λ →* ℂˣ), (∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω)) ∧
      ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
        (i : τ.IntertwiningMap π), Function.Injective i →
        ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
        (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
        ∀ χ : Λ →* ℂˣ, (∀ l, ‖(χ l : ℂ)‖ = 1) → Nonempty (π'.Equiv (twist (χ.comp p) ω)) →
          Nonempty (π'.Equiv ω) ∨ ∃ χ₀ ∈ F, Nonempty (π'.Equiv (twist (χ₀.comp p) ω)) := by
  classical
  have hWnt : Nontrivial W := by
    have := hiω
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ω.asModule
  obtain ⟨u, hu0⟩ := exists_ne (0 : W)
  obtain ⟨H, hu⟩ := exists_compactOpenSubgroup_fixed hsq.1.1 u
  let Good : Finset (Λ →* ℂˣ) → Prop := fun F =>
    (∀ χ ∈ F, ∀ l, ‖(χ l : ℂ)‖ = 1) ∧
    (∀ χ ∈ F, ∀ χ' ∈ F,
      Nonempty ((twist (χ.comp p) ω).Equiv (twist (χ'.comp p) ω)) → χ = χ') ∧
    (∀ χ ∈ F, IsEmpty ((twist (χ.comp p) ω).Equiv ω)) ∧
    (∀ χ ∈ F, HasSubquotientIn π ⊤ (twist (χ.comp p) ω))
  let S : Set ℕ := {n | ∃ F, Good F ∧ F.card = n}
  have hS : BddAbove S := ⟨Module.finrank ℂ (⊤ ⊓ fixedVectors π H.toSubgroup : Submodule ℂ V),
    fun n ⟨F, hF, hn⟩ => hn ▸ card_le_finrank_of_hasSubquotientIn p A hA ν hcof hω hsq hiω hp
      hN hHN hm hm0 hcompat hc ht hw hD hπa hT hsub H hu hu0 F hF.1 hF.2.1 ⊤ hF.2.2.2⟩
  have hS0 : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp, by simp, by simp⟩, rfl⟩
  obtain ⟨F, hF, hFc⟩ := Nat.sSup_mem hS0 hS
  refine ⟨F, hF.2.2.1, ?_⟩
  intro X _ _ τ i hi V' _ _ π' q hq hiπ' χ hχu ⟨e⟩
  by_cases h0 : Nonempty (π'.Equiv ω)
  · exact Or.inl h0
  by_cases h1 : ∃ χ₀ ∈ F, Nonempty (π'.Equiv (twist (χ₀.comp p) ω))
  · exact Or.inr h1
  exfalso
  have hχF : χ ∉ F := fun hχ => h1 ⟨χ, hχ, ⟨e⟩⟩
  have hgood : Good (insert χ F) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro χ' hχ'
      rcases Finset.mem_insert.1 hχ' with rfl | hχ'
      · exact hχu
      · exact hF.1 χ' hχ'
    · intro χ' hχ' χ'' hχ'' ⟨f⟩
      rcases Finset.mem_insert.1 hχ' with h1' | h1' <;>
        rcases Finset.mem_insert.1 hχ'' with h2' | h2'
      · exact h1'.trans h2'.symm
      · subst h1'
        exact (h1 ⟨χ'', h2', ⟨e.trans f⟩⟩).elim
      · subst h2'
        exact (h1 ⟨χ', h1', ⟨e.trans f.symm⟩⟩).elim
      · exact hF.2.1 χ' h1' χ'' h2' ⟨f⟩
    · intro χ' hχ'
      rcases Finset.mem_insert.1 hχ' with rfl | hχ'
      · exact ⟨fun f => h0 ⟨e.trans f⟩⟩
      · exact hF.2.2.1 χ' hχ'
    · intro χ' hχ'
      rcases Finset.mem_insert.1 hχ' with rfl | hχ'
      · exact ⟨X, inferInstance, inferInstance, τ, i, hi, fun _ => Submodule.mem_top, V',
          inferInstance, inferInstance, π', q, hq, hiπ', ⟨e⟩⟩
      · exact hF.2.2.2 χ' hχ'
  have hle := le_csSup hS ⟨_, hgood, rfl⟩
  rw [Finset.card_insert_of_notMem hχF, hFc] at hle
  omega

include hcof hsq hiω in
/-- **Corollary III.7.2**: if the irreducible subquotients of the admissible tempered `π` satisfy
the hypotheses of Proposition III.7.1 (`hsub`), there is a unique decomposition
`V = V₁ ⊕ V₂` into subrepresentations such that (i) every irreducible subquotient of `V₁` is
equivalent to `ω` and (ii) no irreducible subquotient of `V₂` is equivalent to `ω`. -/
theorem existsUnique_orbitIsotypic_decomposition (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    {m : ℝ≥0∞} (hm : m ≠ ∞) (hm0 : m ≠ 0)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    {π : Representation ℂ G V} (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π)
    (hsub : ∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      ∃ cπ' : A →* ℂˣ, (∀ (a : A) (x : V'), π' a x = (cπ' a : ℂ) • x) ∧
        (∀ a : A, ‖(cπ' a : ℂ)‖ = 1) ∧
        ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V'), twist χ' π' a x = (cω a : ℂ) • x)
          (v₁ : V') (ℓ₁ : SmoothDual (twist χ' π')) (v₂ : W) (ℓ₂ : SmoothDual ω),
            Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν) :
    ∃ V₁ V₂ : Subrepresentation π, IsCompl V₁.toSubmodule V₂.toSubmodule ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω)) ∧
      (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂) →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) ∧
      ∀ V₁' V₂' : Subrepresentation π, IsCompl V₁'.toSubmodule V₂'.toSubmodule →
        (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₁') →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      Nonempty (π'.Equiv ω)) →
        (∀ {X : Type w} [AddCommGroup X] [Module ℂ X] {τ : Representation ℂ G X}
      (i : τ.IntertwiningMap π), Function.Injective i → (∀ x, i x ∈ V₂') →
      ∀ {V' : Type w} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ G V'}
      (q : τ.IntertwiningMap π'), Function.Surjective q → π'.IsIrreducible →
      IsEmpty (π'.Equiv ω)) →
        V₁' = V₁ ∧ V₂' = V₂ := by
  obtain ⟨F, hF, hcover⟩ := exists_orbit_covering p A hA ν hcof hω hsq hiω hp hN hHN hm hm0
    hcompat hc ht hw hD hπa hT hsub
  obtain ⟨V₁, V₂, h12, h1, h2⟩ := exists_orbitIsotypic_decomposition p A hA ν hcof hω hsq hiω hp
    hN hHN hm hm0 hcompat hc ht hw hD F hF hπa hT hcover hsub
  refine ⟨V₁, V₂, h12, h1, h2, fun V₁' V₂' h12' h1' h2' => ?_⟩
  obtain ⟨e1, e2⟩ := orbitIsotypic_decomposition_unique p A hA ν hcof hω hsq hiω hp hN hHN hm
    hm0 hcompat hc ht hw hD F hF hπa hT hcover hsub h12 h1 h2 h12' h1' h2'
  exact ⟨e1.symm, e2.symm⟩

end Decomposition

end Langlands.HarishChandraSchwartz
