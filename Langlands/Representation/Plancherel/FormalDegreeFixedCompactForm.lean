import Langlands.Representation.Plancherel.FixedCompactProductForm

/-!
# Formal-degree normalization of the actual fixed compact picture

The central quotient and its Haar measure stay fixed. The previously proved
unitary-twist invariance of the actual Schur degree gives the isometry of the
degree-normalized original sources with one fixed positive compact form.
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
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hi : A.representation.IsIrreducible)

/-- The inverse-degree form on the fixed actual compact picture, with no
positive inducing form among its inputs. -/
def formalDegreeFixedProductCompactForm :
    InvariantPositiveForm (productInducedCompactRepresentation h K A) :=
  ((formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).comp
    (K.prod K).toSubgroup.subtype).ofEquiv
      (productCompactRestriction h hU hP K hK hPK A).symm

/-- Every positive inducing form computes the same inverse-degree fixed
compact form for the specified central quotient Haar measure. -/
theorem formalDegreeFixedProductCompactForm_eq
    (b : InvariantPositiveForm A.representation) :
    formalDegreeFixedProductCompactForm h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi =
      (fixedProductCompactForm h hU hP K hK hPK hG hδ A hcof hsq.1 b).rescale
        (representationFormalDegree C hC μ hcof hsq hi)⁻¹
        (inv_pos.mpr (representationFormalDegree_pos C hC μ hcof hsq hi)) := by
  unfold formalDegreeFixedProductCompactForm
  rw [formalDegreeProductForm_eq h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b]
  rfl

/-- The actual inverse-Schur-degree factor multiplies exactly the fixed
compact product probability integral. -/
theorem formalDegreeFixedProductCompactForm_inner_integral
    (b : InvariantPositiveForm A.representation)
    (F J : ProductInducedCompactPicture h K A) :
    (formalDegreeFixedProductCompactForm
      h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner F J =
      (representationFormalDegree C hC μ hcof hsq hi : ℂ)⁻¹ *
        ∫ k : K × K, (coefficientTensorInvariantForm A hcof hsq.1 b).inner
          (eval _ _ F
            (⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩ : K.prod K))
          (eval _ _ J
            (⟨((k.1 : G), (k.2 : G)), k.1.property, k.2.property⟩ : K.prod K))
          ∂(measure K hK).prod (measure K hK) := by
  rw [formalDegreeFixedProductCompactForm_eq
      h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b,
    InvariantPositiveForm.rescale_inner, Complex.ofReal_inv,
    fixedProductCompactForm_inner_integral]

include hPK in
omit [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] [C.Normal] [MeasurableSpace (M ⧸ C)]
  [BorelSpace (M ⧸ C)] [μ.IsHaarMeasure] [μ.IsInvInvariant] in
private theorem compactFactorization (g : G) :
    ∃ p : P, ∃ k : K, g = (p : G) * (k : G) := by
  obtain ⟨p, hp, k, hk, hg⟩ := hPK g
  exact ⟨⟨p, hp⟩, ⟨k, hk⟩, hg⟩

variable {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (χ : unramifiedCharacters ν) (hu : ∀ m, ‖(χ.val m : ℂ)‖ = 1)

/-- The degree-normalized actual twisted source restricts isometrically
to the fixed compact form, using the same quotient and the same Haar measure. -/
theorem formalDegreeProductInducedCompactEquiv_inner
    (F J : productInducedCoefficientObject h hU
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))) :
    (formalDegreeFixedProductCompactForm
      h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).inner
      (productInducedCompactEquiv ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A F)
      (productInducedCompactEquiv ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A J) =
      (formalDegreeProductForm h hU hP K hK hPK hG hδ
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
        hcof C hC μ
        (isSquareIntegrableModCentralSubgroup_unitaryTwist C hC
          χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) hu μ hsq)
        ((isIrreducible_twist_iff χ.val.toMonoidHom A.representation).mpr hi)).inner
          F J := by
  let b := Classical.choice
    (isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC μ hcof hsq)
  rw [formalDegreeFixedProductCompactForm_eq
      h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi b,
    formalDegreeProductForm_eq h hU hP K hK hPK hG hδ
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
      hcof C hC μ
      (isSquareIntegrableModCentralSubgroup_unitaryTwist C hC
        χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) hu μ hsq)
      ((isIrreducible_twist_iff χ.val.toMonoidHom A.representation).mpr hi)
      (b.twist χ.val.toMonoidHom hu),
    InvariantPositiveForm.rescale_inner, InvariantPositiveForm.rescale_inner,
    representationFormalDegree_unitaryTwist C hC μ hcof χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ) hu hsq hi,
    productInducedCompactEquiv_inner h hU hP K hK hPK hG hδ A hcof
      ν hν hr χ hu hsq.1 b]

/-- The exact existing compact-equivariant restriction equivalence, with
its proved equality of the canonical degree-normalized source forms. -/
def formalDegreeProductCompactIsometry :
    {E : Representation.Equiv
      ((productInducedCoefficientObject h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation.comp
          (K.prod K).toSubgroup.subtype)
      (productInducedCompactRepresentation h K A) //
      (formalDegreeFixedProductCompactForm
        h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi).ofEquiv E =
        (formalDegreeProductForm h hU hP K hK hPK hG hδ
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))
          hcof C hC μ
          (isSquareIntegrableModCentralSubgroup_unitaryTwist C hC
            χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) hu μ hsq)
          ((isIrreducible_twist_iff χ.val.toMonoidHom A.representation).mpr hi)).comp
            (K.prod K).toSubgroup.subtype} :=
  ⟨productInducedCompactEquiv ν h K hP hK hν hr hU
    (compactFactorization K hPK) χ A, by
      apply InvariantPositiveForm.ext_inner
      intro F J
      exact formalDegreeProductInducedCompactEquiv_inner
        h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi ν hν hr χ hu F J⟩

@[simp]
theorem formalDegreeProductCompactIsometry_val :
    (formalDegreeProductCompactIsometry
      h hU hP K hK hPK hG hδ A hcof C hC μ hsq hi ν hν hr χ hu).val =
      productInducedCompactEquiv ν h K hP hK hν hr hU
        (compactFactorization K hPK) χ A := rfl

end Langlands.Plancherel.CompactInduction
