import Langlands.Representation.Plancherel.ActualCommonLeviRationalTensor

/-! # Polynomial product action on the actual common-Levi compact tensor -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviCompactTensor

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact ActualCommonLeviTensor
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
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
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
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

local notation "h" => commonDecomposition χ ψ hψ
local notation "hU" => radical_isClosed ψ
local notation "hδ" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hP" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hr" => commonProjection_continuous χ ψ hψ
local notation "hν" => DynamicOppositeCanonicalScalar.normCharacters_continuous χ
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "G₀" => RationalPoint F G.X
set_option quotPrecheck false in
local notation "hνM" => (fun a => (hν a).comp (parameterHomeomorph χ).symm.continuous)

private abbrev compactInductionAction (B : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : X) :=
  unramifiedCompactRepresentation h hU hδ K hP hK hψK
    (leviNormCharacters χ) hνM hr B (parameterTransport χ z)

local notation "σ" => compactInductionAction χ hG K hK ψ hψ hψK

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- The full rational-point product action on the fixed compact tensor uses
inverse parameter on the inducing smooth dual. -/
def compactTensorRepresentation (z : X) :
    Representation ℂ (G₀ × G₀) (compactFiber χ K ψ hψ A) :=
  BinaryTensor.external (σ A z) (σ A.contragredient z⁻¹)

local notation "ρ" => compactTensorRepresentation χ hG K hK ψ hψ hψK A

/-- The actual restriction and dual identification intertwine the full
product action with the compact tensor action. -/
def compactTensorRepresentationEquiv (z : X) :
    (coefficientFiber χ ψ hψ A z).representation.Equiv (ρ z) := by
  let restriction (B : SmoothRep.{0, u, uV} ℂ (levi χ)) (w : X) :=
    unramifiedCompactRepresentationEquiv h hU hδ K hP hK hψK
      (leviNormCharacters χ) hνM hr B (parameterTransport χ w)
  let e := BinaryTensor.pullEquiv (restriction A z) (MonoidHom.fst G₀ G₀)
  let f := BinaryTensor.pullEquiv
    ((dualInductionEquiv χ hG ψ hψ A z).trans (restriction A.contragredient z⁻¹))
    (MonoidHom.snd G₀ G₀)
  exact (tensorEquiv χ hG K hK ψ hψ hψK A z).symm.trans
    (Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
      (fun x => (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining' x))

@[simp]
theorem compactTensorRepresentationEquiv_toLinearEquiv (z : X) :
    (compactTensorRepresentationEquiv χ hG K hK ψ hψ hψK A z).toLinearEquiv =
      compactTensorEquiv χ hG K hK ψ hψ hψK A z := rfl

/-- Each product-group action operator has a finite regular expansion on every
fixed vector of the compact tensor. -/
theorem compactTensorRepresentation_polynomial (x : G₀ × G₀) :
    IsPolynomialOperatorOn Set.univ (fun z => ρ z.val x) := by
  have hA : IsPolynomialOperatorOn (Set.univ : Set X) (fun z => σ A z.val x.1) :=
    unramifiedCompactRepresentation_transport_polynomial h hU hδ K hP hK hψK
      (parameterHomeomorph χ) (normCharacters χ) hν hr A x.1
  have hdual : IsPolynomialOperatorOn (Set.univ : Set X)
      (fun z => σ A.contragredient z.val x.2) :=
    unramifiedCompactRepresentation_transport_polynomial h hU hδ K hP hK hψK
      (parameterHomeomorph χ) (normCharacters χ) hν hr A.contragredient x.2
  have hinv : IsPolynomialOperatorOn (Set.univ : Set X)
      (fun z => σ A.contragredient z.val⁻¹ x.2) := by
    intro v
    exact (hdual v).inversion
  change IsPolynomialOperatorOn (Set.univ : Set X)
    (fun z => TensorProduct.map (σ A z.val x.1) (σ A.contragredient z.val⁻¹ x.2))
  exact hA.tensor hinv

/-- The action on the compact product consists of the same two compact-picture
right translations at every parameter. -/
theorem compactTensorRepresentation_comp (z : X) :
    (ρ z).comp (MonoidHom.prodMap K.toSubgroup.subtype K.toSubgroup.subtype) =
      BinaryTensor.external (compactPictureAction h K A)
        (compactPictureAction h K A.contragredient) := by
  have hrestrict (B : SmoothRep.{0, u, uV} ℂ (levi χ)) (w : X) (k : K) :
      σ B w (k : G₀) = compactPictureAction h K B k :=
    DFunLike.congr_fun (unramifiedCompactRepresentation_comp h hU hδ K hP hK hψK
      (leviNormCharacters χ) hνM hr B (parameterTransport χ w)) k
  apply MonoidHom.ext
  intro k
  apply TensorProduct.ext'
  intro v w
  change BinaryTensor.external (σ A z) (σ A.contragredient z⁻¹)
      ((k.1 : G₀), (k.2 : G₀)) (v ⊗ₜ[ℂ] w) = _
  simp only [BinaryTensor.external_tmul, hrestrict A z k.1, hrestrict A.contragredient z⁻¹ k.2]

end Langlands.Plancherel.ActualCommonLeviCompactTensor
