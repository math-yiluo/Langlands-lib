import Langlands.Representation.Plancherel.DynamicCommonLeviContinuation
import Langlands.Representation.Plancherel.ReverseDualTensorComparison
import Langlands.Representation.Plancherel.LeviCoefficientConjugation
import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Group.LeftQuotientInversion

/-! # The actual common-Levi forward/inverse-reverse-dual tensor -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]


attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The actual unramified twist on the literal common Levi. -/
abbrev twistObject (z : unramifiedCharacters (normCharacters χ))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :=
  A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))

/-- Smooth duality uses the inverse of the same actual character. -/
def dualTwistEquiv (z : unramifiedCharacters (normCharacters χ))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    (twistObject χ z A).contragredient.representation.Equiv
      (twistObject χ z⁻¹ A.contragredient).representation where
  toLinearEquiv :=
    (smoothContragredientTwistEquiv (parameterTransport χ z).val.toMonoidHom
      A.representation
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))).toLinearEquiv
  isIntertwining' m := by
    have hchar : (parameterTransport χ z⁻¹).val.toMonoidHom =
        (parameterTransport χ z).val.toMonoidHom⁻¹ := by
      rw [map_inv]
      rfl
    change _ = (twist (parameterTransport χ z⁻¹).val.toMonoidHom
      (smoothContragredient A.representation) m) ∘ₗ _
    rw [hchar]
    exact (smoothContragredientTwistEquiv (parameterTransport χ z).val.toMonoidHom
      A.representation
      (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))).isIntertwining' m

@[simp]
theorem dualTwistEquiv_apply (z : unramifiedCharacters (normCharacters χ))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (ℓ : (twistObject χ z A).contragredient)
    (v : A) : (dualTwistEquiv χ z A ℓ).val v = ℓ.val v := rfl

variable (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG

/-- A package of the published restricted actual continuation data. No existence
claim is made by this structure; its analytic fields remain explicit. -/
structure ContinuedPair where
  modulus : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁
  region : Set (unramifiedCharacters (normCharacters χ))
  isOpen_region : IsOpen region
  nonempty_region : region.Nonempty
  converges : region ⊆ pairFullDomainRegion χ K hK ψ hψ ψ' A
  presentation : PairContinuation χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
    modulus A region converges

namespace ContinuedPair

variable (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)

/-- The displayed denominator locus of this actual continuation. -/
abbrev regularRegion := p.presentation.regularRegion

/-- Use the published actual ambient standard continuation. -/
def operator (z : p.regularRegion) :
    (UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
      (parameterTransport χ z.val) A).representation.IntertwiningMap
    (UnramifiedLeviInduction h₁ hU₁ (leviNormCharacters χ)
      (parameterTransport χ z.val) A).representation :=
  continuedFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K p.modulus A
    p.region p.converges p.presentation p.isOpen_region p.nonempty_region (fun _ h => h) z

/-- The displayed operator is conjugate to its own whole-operator compact
continuation by the actual restriction and extension maps. -/
theorem operator_compact (z : p.regularRegion) :
    (compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A).toLinearMap.comp
      ((operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z).toLinearMap.comp
        (compactEquiv χ hG K hK ψ hψ hψK z.val A).symm.toLinearMap) =
      p.presentation.continuedOperator z :=
  continuedFamily_compact χ hG K hK ψ hψ hψK ψ' hψ' hψ'K p.modulus A
    p.region p.converges p.presentation p.isOpen_region p.nonempty_region (fun _ h => h) z

/-- On the displayed starting region this is the actual standard integral
with its published source quotient measure. -/
theorem operator_agrees (z : p.region) :
    operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p
      ⟨z.val, p.presentation.subset_regularRegion z.property⟩ =
      pairFamily χ K hK ψ hψ ψ' hψ' p.modulus A
        ⟨z.val, p.converges z.property⟩ :=
  continuedFamily_agrees χ hG K hK ψ hψ hψK ψ' hψ' hψ'K p.modulus A
    p.region p.converges p.presentation p.isOpen_region p.nonempty_region (fun _ h => h) z

end ContinuedPair

/-- The actual positive-Levi coefficient fiber of the twist. -/
abbrev coefficientFiber (z : unramifiedCharacters (normCharacters χ)) :=
  leviProductInducedCoefficientObject h₀ hU₀ (twistObject χ z A)

/-- The functional-preserving inducing equivalence lifted through actual
positive-Levi induction. -/
def dualInductionEquiv (z : unramifiedCharacters (normCharacters χ)) :
    ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (twistObject χ z A).contragredient).representation.Equiv
    (UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
      (parameterTransport χ z⁻¹) A.contragredient).representation :=
  CoefficientConjugation.leviInductionCongr h₀ hU₀ hδ₀ (dualTwistEquiv χ z A)

variable
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

/-- Both actual operator denominators must be nonzero, with inversion on the
contragredient parameter. No claim of nonemptiness is built into this set. -/
def regularLocus : Set (unramifiedCharacters (normCharacters χ)) :=
  p.regularRegion ∩ (fun z => z⁻¹) ⁻¹' q.regularRegion

/-- The particular reverse actual dual operator, transported through the
canonical smooth-dual twist equivalences. -/
def reverseDual (z : regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q) :
    ((DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj
      (twistObject χ z.val A).contragredient).representation.IntertwiningMap
    ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (twistObject χ z.val A).contragredient).representation :=
  ((dualInductionEquiv χ hG ψ hψ A z.val).symm.toIntertwiningMap.comp
    (ContinuedPair.operator χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient
      q ⟨z.val⁻¹, z.property.2⟩)).comp
      (dualInductionEquiv χ hG ψ' hψ' A z.val).toIntertwiningMap

/-- Simultaneous regularity and invertibility of precisely the actual forward
and reverse dual operators. Analytic nonempty/density is a separate target. -/
def genericLocus : Set (unramifiedCharacters (normCharacters χ)) :=
  {z | ∃ hz : z ∈ regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q,
    Function.Bijective (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
      A p ⟨z, hz.1⟩) ∧
    Function.Bijective (reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ⟨z, hz⟩)}

include hK hψK in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Compactness follows from the actual displayed compact representatives. -/
theorem quotientCompact : CompactSpace (LeftQuotient (parabolic ψ)) :=
  Induction.compactSpace_leftQuotient_of_compact_representatives (parabolic ψ) hK (fun g => by
    obtain ⟨p, k, h⟩ := hψK g
    exact ⟨p, p.property, k, k.property, h⟩)

/-- The existing product induction equivalence with compactness discharged
by the actual Iwasawa factorization. -/
def tensorEquiv (z : unramifiedCharacters (normCharacters χ)) :
    (Induction.BinaryTensor.external
      ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
        (twistObject χ z A)).representation
      ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
        (twistObject χ z A).contragredient).representation).Equiv
      (coefficientFiber χ ψ hψ A z).representation := by
  letI := quotientCompact K hK ψ hψK
  exact leviNormalizedProductInductionTensorEquiv h₀ h₀ hU₀ hU₀ hδ₀ hδ₀
    (twistObject χ z A) (twistObject χ z A).contragredient

/-- The actual `s = 1` normalized comparison on the genuine generic locus. -/
def genericComparison (z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q) :
    (coefficientFiber χ ψ hψ A z.val).representation.IntertwiningMap
    (coefficientFiber χ ψ' hψ' A z.val).representation := by
  letI := quotientCompact K hK ψ hψK
  letI := quotientCompact K hK ψ' hψ'K
  exact reverseDualTensorComparison h₀ h₁ hU₀ hU₁ (twistObject χ z.val A)
    (twistObject χ z.val A)
    (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
      A p ⟨z.val, z.property.choose.1⟩)
    (reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ⟨z.val, z.property.choose⟩)
    z.property.choose_spec.2 hδ₀ hδ₁

section Laws

variable (z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)

local notation "Az" => twistObject χ z.val A
set_option quotPrecheck false in
local notation "Jz" => ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
  A p ⟨z.val, z.property.choose.1⟩
set_option quotPrecheck false in
local notation "Rz" => reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
  A p q ⟨z.val, z.property.choose⟩
set_option quotPrecheck false in
local notation "hz" => z.property.choose_spec.2
local notation "Tz" => genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z

/-- Formula (1) for this particular actual continued family at `s = 1`. -/
theorem genericComparison_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj Az)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (Az).contragredient) :
    Tz (tensorEquiv χ hG K hK ψ hψ hψK A z.val (f ⊗ₜ[ℂ] ℓ)) =
      tensorEquiv χ hG K hK ψ' hψ' hψ'K A z.val
        (Jz f ⊗ₜ[ℂ] reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz ℓ) := by
  have : CompactSpace (LeftQuotient (parabolic ψ)) := quotientCompact K hK ψ hψK
  have : CompactSpace (LeftQuotient (parabolic ψ')) := quotientCompact K hK ψ' hψ'K
  exact reverseDualTensorComparison_tmul h₀ h₁ hU₀ hU₁ Az Az Jz Rz hz hδ₀ hδ₁ f ℓ

/-- Evaluation retains the actual positive-Levi functions and the specified
inverse of the reverse dual, on every pair of rational points. -/
theorem genericComparison_tmul_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj Az)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (Az).contragredient)
    (x : RationalPoint F G.X × RationalPoint F G.X) :
    Induction.eval ((parabolic ψ').prod (parabolic ψ'))
        (leviInflatedInducingRepresentation ((h₁).prod h₁) ((hU₁).prod hU₁)
          (productLeviObject Az (Az).contragredient))
        (Tz (tensorEquiv χ hG K hK ψ hψ hψK A z.val (f ⊗ₜ[ℂ] ℓ))) x =
      Induction.eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ Az)
        (Jz f) x.1 ⊗ₜ[ℂ]
      Induction.eval (parabolic ψ') (leviInflatedInducingRepresentation h₁ hU₁ (Az).contragredient)
        (reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz ℓ) x.2 := by
  have : CompactSpace (LeftQuotient (parabolic ψ)) := quotientCompact K hK ψ hψK
  have : CompactSpace (LeftQuotient (parabolic ψ')) := quotientCompact K hK ψ' hψ'K
  exact reverseDualTensorComparison_tmul_eval h₀ h₁ hU₀ hU₁ Az Az Jz Rz hz hδ₀ hδ₁ f ℓ x

/-- The actual product rational-point action commutes with the comparison
on every coefficient vector. -/
theorem genericComparison_action (x : RationalPoint F G.X × RationalPoint F G.X)
    (v : coefficientFiber χ ψ hψ A z.val) :
    Tz ((coefficientFiber χ ψ hψ A z.val).representation x v) =
      (coefficientFiber χ ψ' hψ' A z.val).representation x (Tz v) :=
  congrArg (fun T => T v) ((Tz).isIntertwining' x)

/-- Both particular operators are invertible on the displayed generic
locus, so their actual tensor comparison is bijective. -/
theorem genericComparison_bijective : Function.Bijective Tz := by
  have : CompactSpace (LeftQuotient (parabolic ψ)) := quotientCompact K hK ψ hψK
  have : CompactSpace (LeftQuotient (parabolic ψ')) := quotientCompact K hK ψ' hψ'K
  exact reverseDualTensorComparison_bijective h₀ h₁ hU₀ hU₁ Az Az Jz Rz hz hδ₀ hδ₁
    z.property.choose_spec.1

end Laws

end Langlands.Plancherel.ActualCommonLeviTensor
