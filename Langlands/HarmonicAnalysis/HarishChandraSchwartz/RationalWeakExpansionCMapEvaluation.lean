import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily

/-! # Tensor evaluation of the actual c-map -/

noncomputable section

set_option maxHeartbeats 480000
set_option maxRecDepth 8192
set_option quotPrecheck false

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

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine cFamilyLeviFiniteType

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

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
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "hα₊" => outerCentralizer_pos hG hi hν I' hζ'
set_option hygiene false in
local notation "hα₋" => outerCentralizer_neg hG hi hν I' hζ'

variable (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {K' : OpenSubgroup (rationalPoints (lowerAmbient i ν (rootSet i ν I')))}
  (hK' : IsCompact (K' : Set (rationalPoints (lowerAmbient i ν (rootSet i ν I')))))
  (hPK' : ∀ g : rationalPoints (lowerAmbient i ν (rootSet i ν I')),
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χs, ∃ k : K',
      g = (p : rationalPoints (lowerAmbient i ν (rootSet i ν I'))) * (k : _))

set_option hygiene false in
local notation "dM" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "uM" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "dL" => decomposition χs
set_option hygiene false in
local notation "uL" => radical_isClosed χs
set_option hygiene false in
local notation "λγ" => ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK : ℂ)⁻¹)

variable (B : SmoothRep.{0, u, uV} ℂ 𝐌)

/-- The standard normalized product tensor chart for the inducing representation. -/
def cMapSourceTensor :=
  haveI : CompactSpace (Induction.LeftQuotient (standardParabolicPoints i ν (rootSet i ν I))) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives _ hK
      (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
  normalizedProductInductionTensorEquiv dM dM uM uM B B.contragredient

/-- The corresponding normalized product tensor chart for the pulled-back representation. -/
def cMapTargetTensor :=
  haveI : CompactSpace (Induction.LeftQuotient (DynamicOppositeStandardIntertwining.parabolic χs)) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives _ hK' (fun g => by
      obtain ⟨p, k, h⟩ := hPK' g
      exact ⟨p, p.property, k, k.property, h⟩)
  normalizedProductInductionTensorEquiv (decomposition χs) (decomposition χs)
        (radical_isClosed χs) (radical_isClosed χs)
        (SmoothRep.pullback (eₛ).symm B)
        (SmoothRep.pullback (eₛ).symm B).contragredient

set_option hygiene false in
local notation "JS" => cMapSourceTensor hG hi hν I K hK hPK B
set_option hygiene false in
local notation "JT" => cMapTargetTensor hG hi hν I I' hζ n hn hK' hPK' B

/-- The actual c-map is the scalar times the tensor of its two convergent factors between
normalized product charts. -/
theorem cMap_eq_tensor (hB : CConverges hG hi hν I I' hζ hζ' n hn K hK B) :
    cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B hB =
      λγ • ((JT).toLinearEquiv.toLinearMap ∘ₗ
        TensorProduct.map (cFactor hG hi hν I I' hζ n hn ζ' hα₊ K hK hCST B hB.1)
          (cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST B hB.2) ∘ₗ
        (JS).symm.toLinearEquiv.toLinearMap) := by
  simp only [cMap, cMapSourceTensor, cMapTargetTensor]
  congr 1

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "νL" => leviNormCharacters χs
set_option hygiene false in
local notation "D" => cDomain hG hi hν I I' hζ hζ' n hn K hK B
set_option hygiene false in
local notation "sz(" z ")" => lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn z
set_option hygiene false in
local notation "V(" z ")" => B.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z)
set_option hygiene false in
local notation "ρS(" z ")" => productInducedCompactEquiv νM dM K
  (isClosed_standardParabolicPoints_rootSet hG hi hν I) hK (continuous_leviRationalNormCharacters i ν I)
  (continuous_projection_standard hG hi hν (rootSet_subset i ν I) _) uM
  (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) z B
set_option hygiene false in
local notation "ρT(" z ")" => productInducedCompactEquiv νL dL K'
  (DynamicOppositeCanonicalScalar.parabolic_isClosed χs) hK'
  (DynamicInducedOrbit.leviNormCharacters_continuous χs)
  (DynamicOppositeCanonicalScalar.projection_continuous χs) uL hPK' (sz(z)) (SmoothRep.pullback (eₛ).symm B)

/-- The target representative change in the c-family is the normalized product
coefficient transport along `twistPullbackEquiv`. -/
theorem cFamily_eq_transport (z : D) :
    cFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B z =
      (productInducedCoefficientTransport dL uL (twistPullbackEquiv hG hi hν I I' hζ n hn B z.val)).toLinearEquiv.toLinearMap
        ∘ₗ cMap hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' (V(z.val)) z.property := by
  simp only [cFamily]

/-- On the fixed compact spaces the actual family uses normalized restriction on the
lower group and extension on the ambient group. -/
theorem cCompactFamily_eq_composite (z : D) :
    cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B z =
      (ρT(z.val)).toLinearEquiv.toLinearMap ∘ₗ
        cFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' B z ∘ₗ
        (ρS(z.val)).symm.toLinearEquiv.toLinearMap := by
  simp only [cCompactFamily]

end WeakExpansion
end Langlands.HarishChandraSchwartz
