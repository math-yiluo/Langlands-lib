import Langlands.Representation.Plancherel.CompactProductInducedForm
import Langlands.Representation.Plancherel.CoefficientTensorFormTransport
import Langlands.Representation.Plancherel.ProductInducedTransport

/-!
# Isometric representative transport on the actual product-induced source

Use the same compact Haar probability and the same central quotient measure
on both representatives. Irreducibility is used only on the inducing
representations when comparing arbitrary forms or their actual formal degrees.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel.CompactInduction

open Aubert.General HarishChandraSchwartz

universe uG uV uW

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
  {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
  (hcof : CompactOpenCofinal M)

set_option backward.isDefEq.respectTransparency false in
/-- The entire actual product-induced form commutes with representative
transport and pullback of the supplied inducing form. -/
theorem productForm_ofEquiv
    (hA : IsAdmissible A.representation) (hB : IsAdmissible B.representation)
    (b : InvariantPositiveForm B.representation)
    (e : A.representation.Equiv B.representation) :
    (productForm h hU hP K hK hPK hG hδ B hcof hB b).ofEquiv
        (productInducedCoefficientTransport h hU e) =
      productForm h hU hP K hK hPK hG hδ A hcof hA (b.ofEquiv e) := by
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK hPK
  have hv (f j : (normalizedInductionFunctor h hU).obj A) :
      (invariantPositiveForm h hU hP K hK hPK hG hδ B b).inner
          (normalizedInductionEquivOfEquiv h hU e f)
          (normalizedInductionEquivOfEquiv h hU e j) =
        (invariantPositiveForm h hU hP K hK hPK hG hδ A (b.ofEquiv e)).inner f j :=
    (congrArg (fun c => c.inner f j)
      (invariantPositiveForm_ofEquiv h hU hP K hK hPK hG hδ b e)).symm
  have hd :
      invariantPositiveForm h hU hP K hK hPK hG hδ A.contragredient
          (dualInvariantForm (b.ofEquiv e) hcof hA) =
        (invariantPositiveForm h hU hP K hK hPK hG hδ B.contragredient
          (dualInvariantForm b hcof hB)).ofEquiv
            (normalizedInductionEquivOfEquiv h hU
              (A := A.contragredient) (B := B.contragredient)
              (smoothContragredientEquiv e.symm)) := by
    rw [dualInvariantForm_ofEquiv hcof hA hB b e]
    exact invariantPositiveForm_ofEquiv h hU hP K hK hPK hG hδ
      (A := A.contragredient) (B := B.contragredient)
      (dualInvariantForm b hcof hB) (smoothContragredientEquiv e.symm)
  apply InvariantPositiveForm.ext_inner
  intro F J
  obtain ⟨t, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective F
  obtain ⟨s, rfl⟩ :=
    (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).surjective J
  change (productForm h hU hP K hK hPK hG hδ B hcof hB b).inner
      (productInducedCoefficientTransport h hU e
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t))
      (productInducedCoefficientTransport h hU e
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient s)) =
    (productForm h hU hP K hK hPK hG hδ A hcof hA (b.ofEquiv e)).inner
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient t)
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient s)
  induction t using TensorProduct.inductionOn with
  | tmul f ℓ =>
    induction s using TensorProduct.inductionOn with
    | tmul j m =>
      rw [productInducedCoefficientTransport_tensor,
        productInducedCoefficientTransport_tensor,
        productForm_inner_tensor, productForm_inner_tensor, hv]
      exact congrArg (fun z : ℂ =>
        (invariantPositiveForm h hU hP K hK hPK hG hδ A (b.ofEquiv e)).inner f j * z)
          (congrArg (fun c => c.inner ℓ m) hd).symm
    | add s s' hs hs' =>
      simp only [map_add, InvariantPositiveForm.add_right, hs, hs']
  | add t t' ht ht' =>
    simp only [map_add, PreInnerProductSpace.Core.add_left, ht, ht']

/-- For an irreducible admissible inducing source, arbitrary supplied
positive forms on the two representatives give the same transported form. -/
theorem productForm_equiv
    (hA : IsAdmissible A.representation) (hB : IsAdmissible B.representation)
    (hi : A.representation.IsIrreducible)
    (a : InvariantPositiveForm A.representation)
    (b : InvariantPositiveForm B.representation)
    (e : A.representation.Equiv B.representation) :
    (productForm h hU hP K hK hPK hG hδ B hcof hB b).ofEquiv
        (productInducedCoefficientTransport h hU e) =
      productForm h hU hP K hK hPK hG hδ A hcof hA a :=
  (productForm_ofEquiv h hU hP K hK hPK hG hδ hcof hA hB b e).trans
    (productForm_independent h hU hP K hK hPK hG hδ A hcof hA hi (b.ofEquiv e) a)

section FormalDegree

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsqA : IsSquareIntegrableModCentralSubgroup C hC A.representation μ)
  (hiA : A.representation.IsIrreducible)
  (hsqB : IsSquareIntegrableModCentralSubgroup C hC B.representation μ)
  (hiB : B.representation.IsIrreducible)

/-- The actual inverse-Schur-degree source forms are preserved under the
existing pointwise representative transport, with the measures fixed. -/
theorem formalDegreeProductForm_ofEquiv
    (e : A.representation.Equiv B.representation) :
    (formalDegreeProductForm h hU hP K hK hPK hG hδ B hcof C hC μ hsqB hiB).ofEquiv
        (productInducedCoefficientTransport h hU e) =
      formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsqA hiA := by
  let b := Classical.choice
    (isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC μ hcof hsqB)
  rw [formalDegreeProductForm_eq h hU hP K hK hPK hG hδ B hcof C hC μ hsqB hiB b,
    formalDegreeProductForm_eq h hU hP K hK hPK hG hδ A hcof C hC μ hsqA hiA
      (b.ofEquiv e)]
  have hp := productForm_ofEquiv h hU hP K hK hPK hG hδ hcof hsqA.1 hsqB.1 b e
  have hd := representationFormalDegree_equiv C hC μ hcof e hsqA hiA hsqB hiB
  apply InvariantPositiveForm.ext_inner
  intro F J
  change ((representationFormalDegree C hC μ hcof hsqB hiB)⁻¹ : ℝ) *
      (productForm h hU hP K hK hPK hG hδ B hcof hsqB.1 b).inner
        (productInducedCoefficientTransport h hU e F)
        (productInducedCoefficientTransport h hU e J) =
    ((representationFormalDegree C hC μ hcof hsqA hiA)⁻¹ : ℝ) *
      (productForm h hU hP K hK hPK hG hδ A hcof hsqA.1 (b.ofEquiv e)).inner F J
  rw [hd]
  exact congrArg (fun z : ℂ =>
    (((representationFormalDegree C hC μ hcof hsqA hiA)⁻¹ : ℝ) : ℂ) * z)
      (congrArg (fun c => c.inner F J) hp)

/-- The canonical pointwise product-induced representative equivalence,
together with its full inverse-degree Hermitian isometry property. -/
def formalDegreeProductTransport
    (e : A.representation.Equiv B.representation) :
    {E : (productInducedCoefficientObject h hU A).representation.Equiv
        (productInducedCoefficientObject h hU B).representation //
      (formalDegreeProductForm h hU hP K hK hPK hG hδ B hcof C hC μ hsqB hiB).ofEquiv E =
        formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μ hsqA hiA} :=
  ⟨productInducedCoefficientTransport h hU e,
    formalDegreeProductForm_ofEquiv h hU hP K hK hPK hG hδ hcof
      C hC μ hsqA hiA hsqB hiB e⟩

@[simp]
theorem formalDegreeProductTransport_val
    (e : A.representation.Equiv B.representation) :
    (formalDegreeProductTransport h hU hP K hK hPK hG hδ hcof
      C hC μ hsqA hiA hsqB hiB e).val =
        productInducedCoefficientTransport h hU e := rfl

/-- Schur's lemma on the inducing source removes the choice of equivalence
from the constructed isometric transport. -/
theorem formalDegreeProductTransport_independent
    (e f : A.representation.Equiv B.representation) :
    formalDegreeProductTransport h hU hP K hK hPK hG hδ hcof
        C hC μ hsqA hiA hsqB hiB e =
      formalDegreeProductTransport h hU hP K hK hPK hG hδ hcof
        C hC μ hsqA hiA hsqB hiB f :=
  Subtype.ext (productInducedCoefficientTransport_independent h hU hsqA.1 hiA e f)

end FormalDegree

section Coefficients

variable [T2Space G] (hm : Continuous h.projection)

/-- The same compact probability coefficient map is preserved by pointwise
representative transport on the actual source functions. -/
theorem coefficientMap_transport
    (hA : A.IsAdmissible) (hB : B.IsAdmissible)
    (e : A.representation.Equiv B.representation)
    (F : productInducedCoefficientObject h hU A) :
    coefficientMap h hU B K hK hP hm hPK hG hδ hB
        (productInducedCoefficientTransport h hU e F) =
      coefficientMap h hU A K hK hP hm hPK hG hδ hA F := by
  ext g
  rw [coefficientMap_integral, coefficientMap_integral]
  have he : integrand h hU B K g (productInducedCoefficientTransport h hU e F) =
      integrand h hU A K g F := by
    funext k
    exact congrFun (productInducedCoefficientIntegrand_transport h hU e F g)
      ⟨k, Subgroup.mem_top _⟩
  rw [he]

end Coefficients

end Langlands.Plancherel.CompactInduction
