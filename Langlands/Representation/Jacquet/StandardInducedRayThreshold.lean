import Langlands.Representation.Jacquet.StandardTensorRayAsymptotics
import Langlands.Representation.Jacquet.StandardUnitaryJacquetFixedLevel

/-! # A common actual ray threshold throughout the original unramified induced family -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

/-- The fixed vectors of the original unramified standard induced action
are linearly equivalent to the untwisted fixed vectors, at any compact-open
ambient level. -/
def standardUnramifiedInducedFixedEquiv
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
    (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    fixedVectors (standardUnramifiedInducedObject hG hi hν I τ ψ).representation L.toSubgroup ≃ₗ[ℂ]
      fixedVectors
        (((normalizedInductionFunctor
          (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))).obj τ).representation)
        L.toSubgroup := by
  have := compactSpace_leftQuotient_standardParabolicPoints_rootSet hG hi hν I hKc hPK
  exact normalizedInductionCompactTrivialTwistFixedVectorsEquiv
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) τ L hL
    ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)
    (Induction.compactSubgroup_le_unramifiedPullback_ker
      (RationalPointFamily.leviRationalNormCharacters i ν I)
      (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)).projection
      (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _) ψ)

include hKc hPK in
/-- The original untwisted fixed dimension bounds every unramified fiber,
and every such fiber is admissible. -/
theorem standardUnramifiedInduced_admissible_finrank
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτ : τ.IsAdmissible)
    (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
    (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)) :
    (standardUnramifiedInducedObject hG hi hν I τ ψ).IsAdmissible ∧
      Module.finrank ℂ
        (fixedVectors (standardUnramifiedInducedObject hG hi hν I τ ψ).representation L.toSubgroup) =
          standardInducedFixedOrder hG hi hν I τ L := by
  refine ⟨?_, (standardUnramifiedInducedFixedEquiv hG hi hν I hKc hPK τ L hL ψ).finrank_eq⟩
  exact CompactInduction.induced_isAdmissible
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K hKc
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (τ.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ))
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    ((SmoothRep.isAdmissible_twist_iff _ _ τ).mpr hτ)

variable {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν J q L)

include hKc hPK hmem in
/-- One explicit integer is a common actual constant-term threshold along
the fixed strict component ray for every unramified source twist and every
coefficient tensor whose original function is bi-invariant at the chosen
standard level. -/
theorem standardUnramifiedConstantTerm_ray_threshold
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτ : τ.IsAdmissible) {L : Subgroup (rationalPoints G)} (hLB : L ∈ B)
    (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I))
    (t : CoefficientTensor (standardUnramifiedInducedObject hG hi hν I τ ψ))
    (hinv : ∀ (k l : basisOpenSubgroup hB hLB) (g : rationalPoints G),
      coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ ψ) t
        ((k : rationalPoints G) * g * (l : rationalPoints G)) =
          coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ ψ) t g)
    {r : ℕ} (hr : standardInducedFixedOrder hG hi hν I τ (basisOpenSubgroup hB hLB) ≤ r) :
    let Vψ := standardUnramifiedInducedObject hG hi hν I τ ψ
    let m := (hA.centralStrictElement i ν hi hζ : standardLeviPoints i ν J)
    coefficientTensorMap Vψ t ((m ^ r : standardLeviPoints i ν J) : rationalPoints G) =
      standardHalfModulus i ν J (m ^ r) *
        standardConstantTerm hA (fun g => coefficientTensorMap Vψ t g) (m ^ r) := by
  obtain ⟨hadm, hdim⟩ := standardUnramifiedInduced_admissible_finrank
    hG hi hν I hKc hPK τ hτ (basisOpenSubgroup hB hLB) (hB.1 L hLB).2.2.2 ψ
  exact standardConstantTerm_ray_of_finrank_le hG hi hν hζ hB hA hmem _ hadm hLB
    hdim.le t hinv hr

end Langlands.HarishChandraSchwartz
