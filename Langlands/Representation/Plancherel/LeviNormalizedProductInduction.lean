import Langlands.Representation.Plancherel.NormalizedProductInduction
import Langlands.Representation.Plancherel.LeviInflatedNormalization
import Langlands.Representation.Tensor.ProductFiltration

/-! # Product induction with the positive Levi normalization -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Aubert.General

universe uG uH

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  [SecondCountableTopology G] [SecondCountableTopology H]

/-- Inner Haar moduli on a product of closed unimodular subgroups are trivial. -/
theorem isUnimodularModulus_prod {U : Subgroup G} {V : Subgroup H}
    (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set H))
    (hδU : IsUnimodularModulus U hU) (hδV : IsUnimodularModulus V hV) :
    IsUnimodularModulus (U.prod V) (hU.prod hV) := by
  intro u
  have hp := HaarModulus.closedRestrictCharacter_prod U U V V hU hV
    Subgroup.le_normalizer Subgroup.le_normalizer u
  change HaarModulus.closedRestrictCharacter (U.prod V) (hU.prod hV)
    (U.prod V) (HaarModulus.prod_normalizes
      Subgroup.le_normalizer Subgroup.le_normalizer) u = 1
  rw [hp]
  exact (congrArg₂ (· * ·) (hδU ⟨u.1.1, u.2.1⟩)
    (hδV ⟨u.1.2, u.2.2⟩)).trans (mul_one 1)

end Langlands.Aubert.General

namespace Langlands.Plancherel

open Aubert.General

universe uG uH uV uW

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {P M U : Subgroup G} {Q N V : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N V)
  (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set H))
  (hδU : IsUnimodularModulus U hU) (hδV : IsUnimodularModulus V hV)
  (A : SmoothRep.{0, uG, uV} ℂ M) (B : SmoothRep.{0, uH, uW} ℂ N)

/-- Apply the existing normalization comparison to each induced tensor factor. -/
def externalInductionLeviEquiv :
    Representation.Equiv
      (Induction.BinaryTensor.external
        ((normalizedInductionFunctor h hU).obj A).representation
        ((normalizedInductionFunctor k hV).obj B).representation)
      (Induction.BinaryTensor.external
        ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
        ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B).representation) :=
  FiniteTensorFiltration.tprodCongr
    (Induction.BinaryTensor.pullEquiv (normalizedInductionLeviEquiv h hU hδU A)
      (MonoidHom.fst G H))
    (Induction.BinaryTensor.pullEquiv (normalizedInductionLeviEquiv k hV hδV B)
      (MonoidHom.snd G H))

@[simp]
theorem externalInductionLeviEquiv_tmul
    (f : (normalizedInductionFunctor h hU).obj A)
    (j : (normalizedInductionFunctor k hV).obj B) :
    externalInductionLeviEquiv h k hU hV hδU hδV A B (f ⊗ₜ[ℂ] j) =
      normalizedInductionLeviEquiv h hU hδU A f ⊗ₜ[ℂ]
        normalizedInductionLeviEquiv k hV hδV B j :=
  TensorProduct.congr_tmul _ _ _ _

@[simp]
theorem externalInductionLeviEquiv_symm_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (j : (DynamicNormalization.leviTwistedInductionFunctor k hV).obj B) :
    (externalInductionLeviEquiv h k hU hV hδU hδV A B).symm (f ⊗ₜ[ℂ] j) =
      (normalizedInductionLeviEquiv h hU hδU A).symm f ⊗ₜ[ℂ]
        (normalizedInductionLeviEquiv k hV hδV B).symm j :=
  TensorProduct.congr_symm_tmul _ _ _ _

variable [SecondCountableTopology G] [SecondCountableTopology H]
  [CompactSpace (Induction.LeftQuotient P)] [CompactSpace (Induction.LeftQuotient Q)]

/-- Tensor comparison for actual source-normalized induction from the product
parabolic, transported through the existing full-parabolic comparisons. -/
def leviNormalizedProductInductionTensorEquiv :
    Representation.Equiv
      (Induction.BinaryTensor.external
        ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
        ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B).representation)
      ((DynamicNormalization.leviTwistedInductionFunctor (h.prod k) (hU.prod hV)).obj
        (productLeviObject A B)).representation :=
  ((externalInductionLeviEquiv h k hU hV hδU hδV A B).symm.trans
    (normalizedProductInductionTensorEquiv h k hU hV A B)).trans
      (normalizedInductionLeviEquiv (h.prod k) (hU.prod hV)
        (isUnimodularModulus_prod hU hV hδU hδV) (productLeviObject A B))

/-- Normalization comparisons commute with the actual product-induction map
on every tensor, including sums of pure tensors. -/
theorem leviNormalizedProductInductionTensorEquiv_commutes
    (t : (normalizedInductionFunctor h hU).obj A ⊗[ℂ]
      (normalizedInductionFunctor k hV).obj B) :
    normalizedInductionLeviEquiv (h.prod k) (hU.prod hV)
        (isUnimodularModulus_prod hU hV hδU hδV) (productLeviObject A B)
        (normalizedProductInductionTensorEquiv h k hU hV A B t) =
      leviNormalizedProductInductionTensorEquiv h k hU hV hδU hδV A B
        (externalInductionLeviEquiv h k hU hV hδU hδV A B t) := by
  simp only [leviNormalizedProductInductionTensorEquiv, Representation.Equiv.trans_apply,
    Representation.Equiv.symm_apply_apply]

/-- The source-normalized comparison sends pure tensors to their pointwise
tensor, with the original order of the two coordinates. -/
@[simp]
theorem leviNormalizedProductInductionTensorEquiv_tmul_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (j : (DynamicNormalization.leviTwistedInductionFunctor k hV).obj B) (x : G × H) :
    Induction.eval (P.prod Q)
        (leviInflatedInducingRepresentation (h.prod k) (hU.prod hV)
          (productLeviObject A B))
        (leviNormalizedProductInductionTensorEquiv h k hU hV hδU hδV A B
          (f ⊗ₜ[ℂ] j)) x =
      Induction.eval P (leviInflatedInducingRepresentation h hU A) f x.1 ⊗ₜ[ℂ]
        Induction.eval Q (leviInflatedInducingRepresentation k hV B) j x.2 := by
  simp only [leviNormalizedProductInductionTensorEquiv, Representation.Equiv.trans_apply,
    externalInductionLeviEquiv_symm_tmul]
  rw [normalizedInductionLeviEquiv_eval (h.prod k) (hU.prod hV)
      (isUnimodularModulus_prod hU hV hδU hδV) (productLeviObject A B),
    normalizedProductInductionTensorEquiv_tmul_eval,
    normalizedInductionLeviEquiv_symm_eval h hU hδU A,
    normalizedInductionLeviEquiv_symm_eval k hV hδV B]

end Langlands.Plancherel
