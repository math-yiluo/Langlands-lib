import Langlands.Representation.Plancherel.ActualCommonLeviTensor
import Langlands.Representation.Plancherel.ActualConjugateLeviTwist
import Langlands.Representation.Plancherel.DynamicLeviCoefficientConjugation
import Langlands.Representation.Plancherel.ProductInducedTransport

/-! # Actual translated common-Levi coefficient tensors -/

noncomputable section

set_option maxRecDepth 4096

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualConjugateLeviTwist

section InducingTransport

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
  (hδ : IsUnimodularModulus U hU)
  {A : SmoothRep.{0, u, uV} ℂ M} {B : SmoothRep.{0, u, uW} ℂ M}
  (e : A.representation.Equiv B.representation)
  [SecondCountableTopology H]

/-- Actual pointwise product-induction transport, in the positive Levi
normalization, for an equivalence of inducing representatives. -/
def coefficientCongr :
    (leviProductInducedCoefficientObject h hU A).representation.Equiv
      (leviProductInducedCoefficientObject h hU B).representation :=
  CoefficientConjugation.leviInductionCongr (h.prod h) (hU.prod hU)
    (isUnimodularModulus_prod hU hU hδ hδ) (productCoefficientLeviEquiv e)

@[simp]
theorem coefficientCongr_eval (v : leviProductInducedCoefficientObject h hU A)
    (x : H × H) :
    Induction.eval (P.prod P)
      (leviInflatedInducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject B B.contragredient))
      (coefficientCongr h hU hδ e v) x =
      productCoefficientLeviEquiv e
        (Induction.eval (P.prod P)
          (leviInflatedInducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) v x) :=
  CoefficientConjugation.leviInductionCongr_eval (h.prod h) (hU.prod hU)
    (isUnimodularModulus_prod hU hU hδ hδ) (productCoefficientLeviEquiv e) v x

variable [CompactSpace (Induction.LeftQuotient P)]

/-- The transport carries each vector factor by e and each actual smooth-dual
factor by the inverse pullback. -/
theorem coefficientCongr_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    coefficientCongr h hU hδ e
      (leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)) =
      leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ B B.contragredient
        (CoefficientConjugation.leviInductionCongr h hU hδ e f ⊗ₜ[ℂ]
          CoefficientConjugation.leviInductionCongr h hU hδ
            (A := A.contragredient) (B := B.contragredient)
            (smoothContragredientEquiv e.symm) ℓ) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact (coefficientCongr_eval h hU hδ e _ x).trans
    ((congrArg (productCoefficientLeviEquiv e)
      (leviNormalizedProductInductionTensorEquiv_tmul_eval h h hU hU hδ hδ
        A A.contragredient f ℓ x)).trans
      (leviNormalizedProductInductionTensorEquiv_tmul_eval h h hU hU hδ hδ
        B B.contragredient
        (CoefficientConjugation.leviInductionCongr h hU hδ e f)
        (CoefficientConjugation.leviInductionCongr h hU hδ
          (A := A.contragredient) (B := B.contragredient)
          (smoothContragredientEquiv e.symm) ℓ) x).symm)

end InducingTransport

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "gA" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "hg" => commonDecomposition χg χg rfl
set_option hygiene false in
local notation "hUg" => radical_isClosed χg
set_option hygiene false in
local notation "hδg" => DynamicOppositeCanonicalScalar.radical_unimodular χg hG

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

/-- Actual coefficient translation followed by the canonical identification
of the conjugate twist. Both factors retain the source-normalized model. -/
def translatedCoefficient (z : unramifiedCharacters (normCharacters χ)) :
    (coefficientFiber χ χ rfl A z).representation.Equiv
      (coefficientFiber χg χg rfl gA (conjugateParameter χ g z)).representation :=
  (DynamicCoefficientConjugation.coefficientLeftTranslation χ g hG
    (twistObject χ z A) K hK hPK).trans
      (coefficientCongr hg hUg hδg (conjugateTwistEquiv χ g z A))

/-- The actual translated vector factor, including the same-carrier
conjugate-twist identification. -/
def translatedVector (z : unramifiedCharacters (normCharacters χ)) :
    ((DynamicNormalization.leviTwistedInductionFunctor
      (decomposition χ) (radical_isClosed χ)).obj (twistObject χ z A)).representation.Equiv
    ((DynamicNormalization.leviTwistedInductionFunctor hg hUg).obj
      (twistObject χg (conjugateParameter χ g z) gA)).representation :=
  (DynamicCoefficientConjugation.leftTranslation χ g hG (twistObject χ z A)).trans
    (CoefficientConjugation.leviInductionCongr hg hUg hδg (conjugateTwistEquiv χ g z A))

/-- The actual translated dual factor, including inverse pullback on the
smooth dual of the inducing equivalence. -/
def translatedDual (z : unramifiedCharacters (normCharacters χ)) :
    ((DynamicNormalization.leviTwistedInductionFunctor
      (decomposition χ) (radical_isClosed χ)).obj
        (twistObject χ z A).contragredient).representation.Equiv
    ((DynamicNormalization.leviTwistedInductionFunctor hg hUg).obj
      (twistObject χg (conjugateParameter χ g z) gA).contragredient).representation :=
  (DynamicCoefficientConjugation.dualLeftTranslation χ g hG (twistObject χ z A)).trans
    (CoefficientConjugation.leviInductionCongr hg hUg hδg
      (smoothContragredientEquiv (conjugateTwistEquiv χ g z A).symm))

variable (K' : OpenSubgroup (RationalPoint F G.X))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (hχgK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic χg, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χg)
  (hψ'K' : ∀ x : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K' gA)
  (q : ContinuedPair χg hG K' hK' ψ' hψ' hψ'K' χg rfl hχgK' (gA).contragredient)

/-- The simultaneous regular and bijective locus of the two particular
actual target operators, pulled back through full parameter conjugation. -/
def genericLocus : Set (unramifiedCharacters (normCharacters χ)) :=
  conjugateParameter χ g ⁻¹'
    ActualCommonLeviTensor.genericLocus χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K' gA p q

/-- Parameter conjugation restricted to the genuine simultaneous generic locus. -/
def genericParameter :
    genericLocus χ g hG A K' hK' hχgK' ψ' hψ' hψ'K' p q →
      ActualCommonLeviTensor.genericLocus χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K' gA p q :=
  Set.restrictPreimage
    (ActualCommonLeviTensor.genericLocus χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K' gA p q)
    (conjugateParameter χ g)

/-- Waldspurger's actual translated tensor on its genuine generic locus:
translate both factors, identify the conjugate twist, then apply the actual
forward standard continuation and inverse reverse-dual continuation. -/
def genericComparison
    (z : genericLocus χ g hG A K' hK' hχgK' ψ' hψ' hψ'K' p q) :
    (coefficientFiber χ χ rfl A z.val).representation.IntertwiningMap
      (coefficientFiber χg ψ' hψ' gA (conjugateParameter χ g z.val)).representation :=
  (ActualCommonLeviTensor.genericComparison χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K' gA p q
    (genericParameter χ g hG A K' hK' hχgK' ψ' hψ' hψ'K' p q z)).comp
      (translatedCoefficient χ g hG A K hK hPK z.val).toIntertwiningMap

variable (z : genericLocus χ g hG A K' hK' hχgK' ψ' hψ' hψ'K' p q)

set_option hygiene false in
local notation "Tz" => genericComparison χ g hG A K hK hPK K' hK' hχgK' ψ' hψ' hψ'K' p q z

/-- Every coefficient vector retains the actual external rational-point action. -/
theorem genericComparison_action (x : RationalPoint F G.X × RationalPoint F G.X)
    (v : coefficientFiber χ χ rfl A z.val) :
    Tz ((coefficientFiber χ χ rfl A z.val).representation x v) =
      (coefficientFiber χg ψ' hψ' gA (conjugateParameter χ g z.val)).representation x (Tz v) :=
  congrArg (fun T => T v) ((Tz).isIntertwining' x)

end Langlands.Plancherel.ActualConjugateLeviTensor
