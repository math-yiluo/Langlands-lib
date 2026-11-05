import Langlands.Representation.Plancherel.CompactProductInducedForm
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The compact probability integral on the actual product-induced source

The product measure is explicitly the product of the already fixed compact
probabilities. No comparison with a separately chosen product Haar is used.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel.CompactInduction

open Aubert.General HarishChandraSchwartz Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)

omit [LocallyCompactSpace P] in
/-- Pair original product-induced sections by integrating their coefficient
pairing against the product of the two specified compact probabilities. -/
def productIntegralPairing (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (F J : productInducedCoefficientObject h hU A) : ℂ :=
  ∫ k : K × K,
    (coefficientTensorInvariantForm A hcof hA b).inner
      (eval _ _ F ((k.1 : G), (k.2 : G)))
      (eval _ _ J ((k.1 : G), (k.2 : G)))
    ∂(measure K hK).prod (measure K hK)

omit [LocallyCompactSpace P] in
/-- The coefficient-core pairing of two actual product-induced sections is
integrable against the product of the two fixed compact probabilities. -/
theorem integrable_productForm_pairing (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (F J : productInducedCoefficientObject h hU A) :
    Integrable (fun k : K × K =>
      (coefficientTensorInvariantForm A hcof hA b).inner
        (eval _ _ F ((k.1 : G), (k.2 : G)))
        (eval _ _ J ((k.1 : G), (k.2 : G))))
      ((measure K hK).prod (measure K hK)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup (K : Subgroup G))
  let : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : BorelSpace K := inferInstanceAs (BorelSpace (K : Subgroup G))
  have hc : Continuous (fun k : K × K =>
      (coefficientTensorInvariantForm A hcof hA b).inner
        (eval _ _ F ((k.1 : G), (k.2 : G)))
        (eval _ _ J ((k.1 : G), (k.2 : G)))) :=
    (pairing_isLocallyConstant _ _
      (coefficientTensorInvariantForm A hcof hA b).toInnerProductCore F J).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

set_option backward.isDefEq.respectTransparency false in
/-- The entire actual source form equals the compact product integral of
the actual coefficient-tensor form at the original function values. -/
theorem productForm_inner_integral (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (F J : productInducedCoefficientObject h hU A) :
    (productForm h hU hP K hK hPK hG hδ A hcof hA b).inner F J =
      productIntegralPairing h hU K hK A hcof hA b F J := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  have eval_add (F₁ F₂ : productInducedCoefficientObject h hU A) (g : G × G) :
      eval _ _ (F₁ + F₂) g = eval _ _ F₁ g + eval _ _ F₂ g := rfl
  obtain ⟨t, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective F
  obtain ⟨s, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective J
  change (productForm h hU hP K hK hPK hG hδ A hcof hA b).inner
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t)
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient s) =
    ∫ k : K × K,
      (coefficientTensorInvariantForm A hcof hA b).inner
        (eval _ _
          (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t)
          ((k.1 : G), (k.2 : G)))
        (eval _ _
          (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient s)
          ((k.1 : G), (k.2 : G)))
      ∂(measure K hK).prod (measure K hK)
  induction t using TensorProduct.inductionOn with
  | tmul f ℓ =>
    induction s using TensorProduct.inductionOn with
    | tmul j m =>
      rw [productForm_inner_tensor h hU hP K hK hPK hG hδ A hcof hA b f j ℓ m]
      refine (integral_prod_mul
        (fun k : K => b.inner (eval _ _ f k) (eval _ _ j k))
        (fun k : K => (dualInvariantForm b hcof hA).inner
          (eval _ _ ℓ k) (eval _ _ m k))).symm.trans ?_
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun k =>
        ((congrArg₂ (coefficientTensorInvariantForm A hcof hA b).inner
          (normalizedProductInductionTensorEquiv_tmul_eval
            h h hU hU A A.contragredient f ℓ ((k.1 : G), (k.2 : G)))
          (normalizedProductInductionTensorEquiv_tmul_eval
            h h hU hU A A.contragredient j m ((k.1 : G), (k.2 : G)))).trans
          (coefficientTensorInvariantForm_inner_tmul A hcof hA b _ _ _ _)).symm)
    | add s s' hs hs' =>
      simp only [map_add, eval_add,
        InvariantPositiveForm.add_right]
      rw [integral_add
        (integrable_productForm_pairing h hU K hK A hcof hA b _ _)
        (integrable_productForm_pairing h hU K hK A hcof hA b _ _)]
      exact congrArg₂ (· + ·) hs hs'
  | add t t' ht ht' =>
    simp only [map_add, eval_add,
      PreInnerProductSpace.Core.add_left]
    rw [integral_add
      (integrable_productForm_pairing h hU K hK A hcof hA b _ _)
      (integrable_productForm_pairing h hU K hK A hcof hA b _ _)]
    exact congrArg₂ (· + ·) ht ht'

/-- Fubini gives the corresponding iterated integral, keeping the same
specified probability in each factor. -/
theorem productForm_inner_integral_integral (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (F J : productInducedCoefficientObject h hU A) :
    (productForm h hU hP K hK hPK hG hδ A hcof hA b).inner F J =
      ∫ k : K, ∫ l : K,
        (coefficientTensorInvariantForm A hcof hA b).inner
          (eval _ _ F ((k : G), (l : G)))
          (eval _ _ J ((k : G), (l : G)))
        ∂measure K hK ∂measure K hK := by
  rw [productForm_inner_integral]
  exact integral_prod _ (integrable_productForm_pairing h hU K hK A hcof hA b F J)

end Langlands.Plancherel.CompactInduction
