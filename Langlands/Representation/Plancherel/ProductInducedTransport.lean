import Langlands.Representation.Plancherel.ProductInducedCoefficients
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-!
# Representative transport on actual product induction

Lift vector equivalence and inverse smooth-dual pullback pointwise through the
actual normalized product induction. The diagonal contraction is preserved,
and Schur's lemma on the inducing representation removes the choice.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {P M U : Subgroup G}
  {A : SmoothRep.{0, uG, uV} ℂ M}
  {B : SmoothRep.{0, uG, uW} ℂ M}
  {C : SmoothRep.{0, uG, uX} ℂ M}

section Levi

variable [IsTopologicalGroup G]

/-- The actual product-Levi equivalence is vector transport tensored with
inverse pullback on smooth functionals. -/
def productCoefficientLeviEquiv
    (e : A.representation.Equiv B.representation) :
    Representation.Equiv
      (productLeviObject A A.contragredient).representation
      (productLeviObject B B.contragredient).representation :=
  Representation.Equiv.mk (coefficientTensorCongr e) (by
    intro m
    apply LinearMap.ext
    intro t
    exact coefficientTensorCongr_action e (HaarModulus.subgroupProdEquiv M M m) t)

@[simp]
theorem productCoefficientLeviEquiv_tmul
    (e : A.representation.Equiv B.representation) (v : A)
    (ℓ : SmoothDual A.representation) :
    productCoefficientLeviEquiv e (v ⊗ₜ[ℂ] ℓ) =
      e v ⊗ₜ[ℂ] contragredientMap e.symm.toIntertwiningMap ℓ := rfl

/-- Vector equivalence and inverse dual pullback preserve the bilinear
contraction on every tensor. -/
theorem productCoefficientLeviEquiv_pairing
    (e : A.representation.Equiv B.representation) (t : CoefficientTensor A) :
    TensorProduct.lift (smoothDualPairing B.representation).flip
        (productCoefficientLeviEquiv e t) =
      TensorProduct.lift (smoothDualPairing A.representation).flip t := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    change ℓ.val (e.symm (e v)) = ℓ.val v
    rw [e.symm_apply_apply]
  | add t s ht hs =>
    calc
      _ = TensorProduct.lift (smoothDualPairing B.representation).flip
          (productCoefficientLeviEquiv e t + productCoefficientLeviEquiv e s) :=
        congrArg (TensorProduct.lift (smoothDualPairing B.representation).flip)
          (map_add (coefficientTensorCongr e) t s)
      _ = _ :=
        (map_add (TensorProduct.lift (smoothDualPairing B.representation).flip) _ _).trans
          (congrArg₂ (· + ·) ht hs)
      _ = _ := (map_add (TensorProduct.lift (smoothDualPairing A.representation).flip)
        t s).symm

end Levi

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- Transport equivalent inducing representatives on the actual normalized
induction from the literal product parabolic. -/
def productInducedCoefficientTransport
    (e : A.representation.Equiv B.representation) :
    Representation.Equiv
      (productInducedCoefficientObject h hU A).representation
      (productInducedCoefficientObject h hU B).representation :=
  normalizedInductionEquivOfEquiv (h.prod h) (hU.prod hU)
    (productCoefficientLeviEquiv e)

/-- The transport is the pointwise product-Levi map on actual induced
functions, including independent source and target carrier universes. -/
@[simp]
theorem productInducedCoefficientTransport_eval
    (e : A.representation.Equiv B.representation)
    (F : productInducedCoefficientObject h hU A) (x : G × G) :
    Induction.eval (P.prod P)
        (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject B B.contragredient))
        (productInducedCoefficientTransport h hU e F) x =
      productCoefficientLeviEquiv e
        (Induction.eval (P.prod P)
          (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) F x) := rfl

/-- The full diagonal integrand is unchanged pointwise. No integration,
admissibility, compact quotient or second countability is needed. -/
theorem productInducedCoefficientIntegrand_transport
    (e : A.representation.Equiv B.representation)
    (F : productInducedCoefficientObject h hU A) (g : G) :
    productInducedCoefficientIntegrand h hU B g
        (productInducedCoefficientTransport h hU e F) =
      productInducedCoefficientIntegrand h hU A g F := by
  funext k
  exact (congrArg (TensorProduct.lift (smoothDualPairing B.representation).flip)
    (productInducedCoefficientTransport_eval h hU e F ((k : G) * g, k))).trans
      (productCoefficientLeviEquiv_pairing e _)

/-- The pointwise transport intertwines the full actual product-group action. -/
theorem productInducedCoefficientTransport_action
    (e : A.representation.Equiv B.representation)
    (x : G × G) (F : productInducedCoefficientObject h hU A) :
    productInducedCoefficientTransport h hU e
        ((productInducedCoefficientObject h hU A).representation x F) =
      (productInducedCoefficientObject h hU B).representation x
        (productInducedCoefficientTransport h hU e F) :=
  congrArg (fun T : productInducedCoefficientObject h hU A →ₗ[ℂ]
    productInducedCoefficientObject h hU B => T F)
      ((productInducedCoefficientTransport h hU e).isIntertwining' x)

@[simp]
theorem productInducedCoefficientTransport_refl
    (F : productInducedCoefficientObject h hU A) :
    productInducedCoefficientTransport h hU
      (Representation.Equiv.refl A.representation) F = F := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact coefficientTensorCongr_refl _

/-- Composite inducing equivalences give composite pointwise transports. -/
theorem productInducedCoefficientTransport_trans
    (e : A.representation.Equiv B.representation)
    (f : B.representation.Equiv C.representation)
    (F : productInducedCoefficientObject h hU A) :
    productInducedCoefficientTransport h hU (e.trans f) F =
      productInducedCoefficientTransport h hU f
        (productInducedCoefficientTransport h hU e F) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact coefficientTensorCongr_trans e f _

/-- Schur's lemma is applied only to the irreducible admissible inducing
representation. The induced representation need not be irreducible. -/
theorem productInducedCoefficientTransport_independent
    (hA : A.IsAdmissible) (hi : A.representation.IsIrreducible)
    (e f : A.representation.Equiv B.representation) :
    productInducedCoefficientTransport h hU e =
      productInducedCoefficientTransport h hU f := by
  have he : productCoefficientLeviEquiv e = productCoefficientLeviEquiv f := by
    apply Representation.Equiv.ext
    funext t
    exact congrArg (fun E : CoefficientTensor A ≃ₗ[ℂ] CoefficientTensor B => E t)
      (coefficientTensorCongr_eq_of_admissible hA hi e f)
  exact congrArg (normalizedInductionEquivOfEquiv (h.prod h) (hU.prod hU)) he

section ProductComparison

variable [SecondCountableTopology G] [CompactSpace (Induction.LeftQuotient P)]

/-- The actual product transport agrees on pure tensors with the pointwise
transports of both normalized inductions. -/
theorem productInducedCoefficientTransport_tensor
    (e : A.representation.Equiv B.representation)
    (f : (normalizedInductionFunctor h hU).obj A)
    (fdual : (normalizedInductionFunctor h hU).obj A.contragredient) :
    productInducedCoefficientTransport h hU e
        (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
          (f ⊗ₜ[ℂ] fdual)) =
      normalizedProductInductionTensorEquiv h h hU hU B B.contragredient
        (normalizedInductionEquivOfEquiv h hU e f ⊗ₜ[ℂ]
          normalizedInductionEquivOfEquiv h hU
            (A := A.contragredient) (B := B.contragredient)
            (smoothContragredientEquiv e.symm) fdual) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact (productInducedCoefficientTransport_eval h hU e _ x).trans
    ((congrArg (productCoefficientLeviEquiv e)
      (normalizedProductInductionTensorEquiv_tmul_eval h h hU hU A A.contragredient
        f fdual x)).trans
      (normalizedProductInductionTensorEquiv_tmul_eval h h hU hU B B.contragredient
        (normalizedInductionEquivOfEquiv h hU e f)
        (normalizedInductionEquivOfEquiv h hU
          (A := A.contragredient) (B := B.contragredient)
          (smoothContragredientEquiv e.symm) fdual) x).symm)

end ProductComparison

section IntegralCoefficients

variable [SecondCountableTopology G] [CompactSpace (Induction.LeftQuotient P)]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace P]
  (hP : IsClosed (P : Set G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hm : Continuous h.projection)

/-- Equivalent inducing representatives have the same actual coefficient
function. The proof compares their diagonal integrals against the same measure. -/
theorem productInducedCoefficientMap_transport
    (hA : A.IsAdmissible) (hB : B.IsAdmissible)
    (e : A.representation.Equiv B.representation)
    (F : productInducedCoefficientObject h hU A) :
    productInducedCoefficientMap h hU B hP hG hδ hm hB
        (productInducedCoefficientTransport h hU e F) =
      productInducedCoefficientMap h hU A hP hG hδ hm hA F := by
  ext g
  rw [productInducedCoefficientMap_integral, productInducedCoefficientMap_integral,
    productInducedCoefficientIntegrand_transport]

/-- Coefficient preservation identifies the actual coefficient images of
equivalent inducing representatives. -/
theorem range_productInducedCoefficientMap_of_equiv
    (hA : A.IsAdmissible) (hB : B.IsAdmissible)
    (e : A.representation.Equiv B.representation) :
    LinearMap.range (productInducedCoefficientMap h hU A hP hG hδ hm hA) =
      LinearMap.range (productInducedCoefficientMap h hU B hP hG hδ hm hB) := by
  apply le_antisymm
  · rintro _ ⟨F, rfl⟩
    exact ⟨productInducedCoefficientTransport h hU e F,
      productInducedCoefficientMap_transport h hU hP hG hδ hm hA hB e F⟩
  · rintro _ ⟨F, rfl⟩
    exact ⟨productInducedCoefficientTransport h hU e.symm F,
      productInducedCoefficientMap_transport h hU hP hG hδ hm hB hA e.symm F⟩

end IntegralCoefficients

end Langlands.Plancherel
