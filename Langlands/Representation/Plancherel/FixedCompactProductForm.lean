import Langlands.Representation.Plancherel.CompactProductIntegralFormula
import Langlands.Representation.Plancherel.ProductCompactTwistForm
import Langlands.Representation.Unitary.Restriction

/-!
# The fixed compact product form and actual unitary twist isometry

The form is pulled from the untwisted actual source. Its integral formula and
the functional-preserving coefficient twist comparison prove the isometry of
the existing compact restriction map.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel.CompactInduction

open Aubert.General HarishChandraSchwartz Induction

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)

include hPK in
omit [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] in
private theorem compactFactorization (g : G) :
    ∃ p : P, ∃ k : K, g = (p : G) * (k : G) := by
  obtain ⟨p, hp, k, hk, hg⟩ := hPK g
  exact ⟨⟨p, hp⟩, ⟨k, hk⟩, hg⟩

/-- Untwisted literal restriction to the original fixed compact picture. -/
def productCompactRestriction (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation.Equiv
      ((productInducedCoefficientObject h hU A).representation.comp
        (K.prod K).toSubgroup.subtype)
      (productInducedCompactRepresentation h K A) :=
  normalizedInductionCompactEquiv (h.prod h) (K.prod K) (hU.prod hU)
    (hP.prod hP) (hK.prod hK)
    (product_compact_factorization K (compactFactorization K hPK))
    (productLeviObject A A.contragredient)

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] in
@[simp]
theorem productCompactRestriction_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (F : productInducedCoefficientObject h hU A) (k : K.prod K) :
    eval _ _ (productCompactRestriction h hU hP K hK hPK A F) k =
      eval _ _ F (k : G × G) := rfl

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] in
@[simp]
theorem productCompactRestriction_symm_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (F : ProductInducedCompactPicture h K A) (k : K.prod K) :
    eval _ _ ((productCompactRestriction h hU hP K hK hPK A).symm F)
        (k : G × G) =
      eval _ _ F k :=
  congrArg (fun J : ProductInducedCompactPicture h K A => eval _ _ J k)
    ((productCompactRestriction h hU hP K hK hPK A).apply_symm_apply F)

variable
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)

/-- The fixed positive compact form is the transport of the untwisted
source form restricted to the actual compact product subgroup. -/
def fixedProductCompactForm (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm (productInducedCompactRepresentation h K A) :=
  ((productForm h hU hP K hK hPK hG hδ A hcof hA b).comp
    (K.prod K).toSubgroup.subtype).ofEquiv
      (productCompactRestriction h hU hP K hK hPK A).symm

/-- The fixed compact form integrates the actual coefficient pairing
against the same specified compact probability in both factors. -/
theorem fixedProductCompactForm_inner_integral (hA : IsAdmissible A.representation)
    (b : InvariantPositiveForm A.representation)
    (F J : ProductInducedCompactPicture h K A) :
    (fixedProductCompactForm h hU hP K hK hPK hG hδ A hcof hA b).inner F J =
      ∫ k : K × K, (coefficientTensorInvariantForm A hcof hA b).inner
        (eval _ _ F
          (⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩ : K.prod K))
        (eval _ _ J
          (⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩ : K.prod K))
        ∂(measure K hK).prod (measure K hK) := by
  change (productForm h hU hP K hK hPK hG hδ A hcof hA b).inner
    ((productCompactRestriction h hU hP K hK hPK A).symm F)
    ((productCompactRestriction h hU hP K hK hPK A).symm J) = _
  rw [productForm_inner_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun k =>
    congrArg₂ (coefficientTensorInvariantForm A hcof hA b).inner
      (productCompactRestriction_symm_eval h hU hP K hK hPK A F
        ⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩)
      (productCompactRestriction_symm_eval h hU hP K hK hPK A J
        ⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩))

variable {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (χ : unramifiedCharacters ν) (hu : ∀ m, ‖(χ.val m : ℂ)‖ = 1)

/-- Actual compact restriction of every unitary unramified twist preserves
the entire product-induced source form. -/
theorem productInducedCompactEquiv_inner
    (hA : IsAdmissible A.representation) (b : InvariantPositiveForm A.representation)
    (F J : productInducedCoefficientObject h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    (fixedProductCompactForm h hU hP K hK hPK hG hδ A hcof hA b).inner
      (productInducedCompactEquiv ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A F)
      (productInducedCompactEquiv ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A J) =
      (productForm h hU hP K hK hPK hG hδ
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hcof
        ((isAdmissible_twist_iff χ.val.toMonoidHom A.representation
          (unramifiedCharacter_isOpen_ker ν χ)).mpr hA)
        (b.twist χ.val.toMonoidHom hu)).inner F J := by
  rw [fixedProductCompactForm_inner_integral, productForm_inner_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun k =>
    (congrArg₂ (coefficientTensorInvariantForm A hcof hA b).inner
      (productInducedCompactEquiv_eval ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A F
        ⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩)
      (productInducedCompactEquiv_eval ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A J
        ⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩)).trans
      (productCompactTwistTensorEquiv_inner ν χ hu A hcof hA b _ _))

/-- The existing compact-equivariant restriction equivalence with its
proved preservation of the entire actual unitary-twisted source form. -/
def productInducedCompactIsometry
    (hA : IsAdmissible A.representation) (b : InvariantPositiveForm A.representation) :
    {E : Representation.Equiv
      ((productInducedCoefficientObject h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation.comp
          (K.prod K).toSubgroup.subtype)
      (productInducedCompactRepresentation h K A) //
      (fixedProductCompactForm h hU hP K hK hPK hG hδ A hcof hA b).ofEquiv E =
        (productForm h hU hP K hK hPK hG hδ
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) hcof
          ((isAdmissible_twist_iff χ.val.toMonoidHom A.representation
            (unramifiedCharacter_isOpen_ker ν χ)).mpr hA)
          (b.twist χ.val.toMonoidHom hu)).comp (K.prod K).toSubgroup.subtype} :=
  ⟨productInducedCompactEquiv ν h K hP hK hν hr hU
    (compactFactorization K hPK) χ A, by
      apply InvariantPositiveForm.ext_inner
      intro F J
      exact productInducedCompactEquiv_inner h hU hP K hK hPK hG hδ A hcof
        ν hν hr χ hu hA b F J⟩

@[simp]
theorem productInducedCompactIsometry_val
    (hA : IsAdmissible A.representation) (b : InvariantPositiveForm A.representation) :
    (productInducedCompactIsometry h hU hP K hK hPK hG hδ A hcof
      ν hν hr χ hu hA b).val =
      productInducedCompactEquiv ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A := rfl

end Langlands.Plancherel.CompactInduction
