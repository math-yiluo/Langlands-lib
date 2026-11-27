import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCNaturality

/-! # Covariance of the c-family under unramified self-twists -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily DynamicCommonLeviComposition

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine
  cFamilyLeviFiniteType

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n

section CompactFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K' : OpenSubgroup (rationalPoints (lowerAmbient i ν (rootSet i ν I')))}
  (hK' : IsCompact (K' : Set (rationalPoints (lowerAmbient i ν (rootSet i ν I')))))
  (hPK' : ∀ g : rationalPoints (lowerAmbient i ν (rootSet i ν I')),
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs, ∃ k : K',
      g = (p : rationalPoints (lowerAmbient i ν (rootSet i ν I'))) * (k : _))

set_option hygiene false in
local notation "Rup" => productInducedCompactEquiv (leviRationalNormCharacters i ν I)
  (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
  (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
  (continuous_leviRationalNormCharacters i ν I)
  (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _)
  (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
  (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
set_option hygiene false in
local notation "Rlow" => productInducedCompactEquiv (leviNormCharacters χs) (decomposition χs) K'
  (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
  (DynamicInducedOrbit.leviNormCharacters_continuous χs)
  (DynamicOppositeCanonicalScalar.projection_continuous χs) (radical_isClosed χs) hPK'

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- `cCompactFamily` unfolded: restriction, twist transport, c-map and inverse restriction. -/
theorem cCompactFamily_apply [LocallyCompactSpace (standardParabolicPoints i ν (rootSet i ν I))]
    (A : SmoothRep.{0, u, uV} ℂ 𝐌) (z : unramifiedCharacters νM)
    (hz : z ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A)
    (Fc : ProductInducedCompactPicture
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K A) :
    cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z, hz⟩ Fc =
      (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)
          (SmoothRep.pullback (eₛ).symm A))
        (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
          (twistPullbackEquiv hG hi hν I I' hζ n hn A z)
          (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hz
            ((Rup z A).symm Fc))) :=
  rfl


/-- The self-twist `sA ≃ sA ⊗ sτ` of the lower inducing representation induced by a self-twist
`a : A ≃ A ⊗ τ`; its linear map is that of `a`. -/
abbrev lowerSelfTwist (A : SmoothRep.{0, u, uV} ℂ 𝐌) (τ : unramifiedCharacters νM)
    (a : A.representation.Equiv
      (A.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation) :
    (SmoothRep.pullback (eₛ).symm A).representation.Equiv
      ((SmoothRep.pullback (eₛ).symm A).twist
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χs)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ))).representation :=
  (SmoothRep.pullbackEquiv (eₛ).symm a).trans (twistPullbackEquiv hG hi hν I I' hζ n hn A τ)

/-- The joint convergence domain is stable under translation by a self-twist. -/
theorem mul_mem_cDomain_of_selfTwist (A : SmoothRep.{0, u, uV} ℂ 𝐌)
    {z τ : unramifiedCharacters νM}
    (a : A.representation.Equiv
      (A.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : z ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A) :
    z * τ ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A :=
  cConverges_of_equiv hG hi hν I I' hζ hζ' n hn K hK (parameterSelfTwistEquiv νM A z τ a) hz

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- **Covariance of the c-family under self-twists** on the fixed compact pictures: for a
self-twist `a : A ≃ A ⊗ τ` and `z`, `zτ` in the joint convergence domain,
`c(s, A ⊗ zτ) ∘ a = (sa) ∘ c(s, A ⊗ z)`, where `a` and `sa` act by the self-twist operators of
the two compact pictures. -/
theorem cCompactFamily_selfTwist_aux [LocallyCompactSpace (standardParabolicPoints i ν (rootSet i ν I))]
    (A : SmoothRep.{0, u, uV} ℂ 𝐌) (z τ : unramifiedCharacters νM)
    (a : A.representation.Equiv
      (A.twist τ.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM τ)).representation)
    (hz : z ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A)
    (hzτ : z * τ ∈ cDomain hG hi hν I I' hζ hζ' n hn K hK A)
    (X : productInducedCoefficientObject
      (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
      (A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z))) :
    cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z * τ, hzτ⟩
        (productCompactSelfTwistEquiv νM A
          (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
          (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
          (continuous_leviRationalNormCharacters i ν I)
          (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) τ a ((Rup z A) X)) =
      productCompactSelfTwistEquiv (leviNormCharacters χs) (SmoothRep.pullback (eₛ).symm A)
        (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
        (DynamicInducedOrbit.leviNormCharacters_continuous χs)
        (DynamicOppositeCanonicalScalar.projection_continuous χs)
        (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
        (lowerSelfTwist hG hi hν I I' hζ n hn A τ a)
        (cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z, hz⟩
          ((Rup z A) X)) := by
  have h1 := productInducedParameterSelfTwist_restriction νM
    (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
    (continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _)
    (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) A z τ a X
  calc cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z * τ, hzτ⟩
        (productCompactSelfTwistEquiv νM A
          (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)) K
          (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK
          (continuous_leviRationalNormCharacters i ν I)
          (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) τ a ((Rup z A) X))
      = cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z * τ, hzτ⟩
          ((Rup (z * τ) A) (productInducedCoefficientTransport
            (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
            (parameterSelfTwistEquiv νM A z τ a) X)) :=
        congrArg (cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z * τ, hzτ⟩)
          h1.symm
    _ = (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (z * τ))
          (SmoothRep.pullback (eₛ).symm A))
        (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
          (twistPullbackEquiv hG hi hν I I' hζ n hn A (z * τ))
          (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hzτ
            ((Rup (z * τ) A).symm ((Rup (z * τ) A) (productInducedCoefficientTransport
              (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
              (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
              (parameterSelfTwistEquiv νM A z τ a) X))))) :=
        cCompactFamily_apply hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A (z * τ) hzτ _
    _ = (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (z * τ))
          (SmoothRep.pullback (eₛ).symm A))
        (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
          (twistPullbackEquiv hG hi hν I I' hζ n hn A (z * τ))
          (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hzτ
            (productInducedCoefficientTransport
              (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
              (isClosed_standardUnipotentPoints i ν (rootSet i ν I))
              (parameterSelfTwistEquiv νM A z τ a) X))) :=
        congrArg (fun W => (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (z * τ))
          (SmoothRep.pullback (eₛ).symm A))
          (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
            (twistPullbackEquiv hG hi hν I I' hζ n hn A (z * τ))
            (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hzτ W)))
          (Representation.Equiv.symm_apply_apply (Rup (z * τ) A) _)
    _ = (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (z * τ))
          (SmoothRep.pullback (eₛ).symm A))
        (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
          (twistPullbackEquiv hG hi hν I I' hζ n hn A (z * τ))
          (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
            (lowerPullbackEquiv hG hi hν I I' hζ n hn (parameterSelfTwistEquiv νM A z τ a))
            (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hz X))) :=
        congrArg (fun W => (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (z * τ))
          (SmoothRep.pullback (eₛ).symm A))
          (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
            (twistPullbackEquiv hG hi hν I I' hζ n hn A (z * τ)) W))
          (cMap_natural hG hi hν I I' hζ hζ' n hn K hK hCST (parameterSelfTwistEquiv νM A z τ a)
            hPK hK' hPK' hz hzτ X)
    _ = productCompactSelfTwistEquiv (leviNormCharacters χs) (SmoothRep.pullback (eₛ).symm A)
          (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
          (DynamicInducedOrbit.leviNormCharacters_continuous χs)
          (DynamicOppositeCanonicalScalar.projection_continuous χs)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
          (lowerSelfTwist hG hi hν I I' hζ n hn A τ a)
          ((Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)
            (SmoothRep.pullback (eₛ).symm A))
            (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
              (twistPullbackEquiv hG hi hν I I' hζ n hn A z)
              (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hz X))) :=
        productInducedCompactEquiv_transport_selfTwist (leviNormCharacters χs) (decomposition χs) K'
          (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
          (DynamicInducedOrbit.leviNormCharacters_continuous χs)
          (DynamicOppositeCanonicalScalar.projection_continuous χs) (radical_isClosed χs) hPK'
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (z * τ))
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
          (twistPullbackEquiv hG hi hν I I' hζ n hn A z)
          (twistPullbackEquiv hG hi hν I I' hζ n hn A (z * τ))
          (lowerPullbackEquiv hG hi hν I I' hζ n hn (parameterSelfTwistEquiv νM A z τ a))
          (lowerSelfTwist hG hi hν I I' hζ n hn A τ a) (fun _ => rfl) _
    _ = productCompactSelfTwistEquiv (leviNormCharacters χs) (SmoothRep.pullback (eₛ).symm A)
          (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
          (DynamicInducedOrbit.leviNormCharacters_continuous χs)
          (DynamicOppositeCanonicalScalar.projection_continuous χs)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
          (lowerSelfTwist hG hi hν I I' hζ n hn A τ a)
          (cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A ⟨z, hz⟩
            ((Rup z A) X)) :=
        (congrArg (productCompactSelfTwistEquiv (leviNormCharacters χs)
          (SmoothRep.pullback (eₛ).symm A)
          (decomposition χs) K' (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
          (DynamicInducedOrbit.leviNormCharacters_continuous χs)
          (DynamicOppositeCanonicalScalar.projection_continuous χs)
          (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn τ)
          (lowerSelfTwist hG hi hν I I' hζ n hn A τ a))
          ((cCompactFamily_apply hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' A z hz
            ((Rup z A) X)).trans
            (congrArg (fun W => (Rlow (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z)
              (SmoothRep.pullback (eₛ).symm A))
              (productInducedCoefficientTransport (decomposition χs) (radical_isClosed χs)
                (twistPullbackEquiv hG hi hν I I' hζ n hn A z)
                (cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' _ hz W)))
              (Representation.Equiv.symm_apply_apply (Rup z A) X)))).symm

end CompactFamily

end WeakExpansion

end Langlands.HarishChandraSchwartz
