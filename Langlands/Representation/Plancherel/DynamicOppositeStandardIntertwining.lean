import Langlands.Representation.Plancherel.StandardInductionSelfComparison
import Langlands.Representation.Plancherel.StandardIntertwiningDynamicSource
import Langlands.Representation.Plancherel.StandardIntertwiningModulus
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Aubert.General.DynamicLeviTopology
import Langlands.Representation.Aubert.General.DynamicOppositeHaarReciprocity
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Actual opposite standard integrals at the common source Haar scale -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicOppositeStandardIntertwining

open Aubert.General StandardIntertwining
open BruhatTits.DynamicUnipotentContainment
open OrderedSubgroupFactorization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance dynamicOppositeStandardIntertwiningIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance dynamicOppositeStandardIntertwiningTopologicalSpace : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance dynamicOppositeStandardIntertwiningT2Space : T2Space F := BruhatTits.localField_t2Space F
local instance dynamicOppositeStandardIntertwiningIsTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance dynamicOppositeStandardIntertwiningT2Space2 : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance dynamicOppositeStandardIntertwiningLocallyCompactSpace : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance dynamicOppositeStandardIntertwiningNonarchimedeanGroup : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

/-- The literal identity-test parabolic of the cocharacter. -/
abbrev parabolic : Subgroup (RationalPoint F G.X) :=
  (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _))

/-- The literal common dynamic Levi. -/
abbrev levi : Subgroup (RationalPoint F G.X) :=
  (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))

/-- The literal contracted radical. -/
abbrev radical : Subgroup (RationalPoint F G.X) := unipotentPoints χ

/-- The literal parabolic of the inverse cocharacter. -/
abbrev oppositeParabolic : Subgroup (RationalPoint F G.X) :=
  parabolic (Dynamic.inverseCocharacter χ)

/-- The literal radical of the inverse cocharacter. -/
abbrev oppositeRadical : Subgroup (RationalPoint F G.X) :=
  radical (Dynamic.inverseCocharacter χ)

/-- The actual affine group scheme representing the common Levi. -/
abbrev parameterScheme : GroupScheme (Spec (CommRingCat.of F)) :=
  Dynamic.Affine.centralizerScheme χ

local instance centralizerClosedImmersion :
    IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom χ
local instance centralizerAffine : IsAffine (parameterScheme χ).X.left :=
  isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom χ).hom.hom.left
local instance dynamicOppositeStandardIntertwiningTopologicalSpace2 : TopologicalSpace (RationalPoint F (parameterScheme χ).X) :=
  rationalPointTopology F (parameterScheme χ).X

/-- The parameter group is identified with the literal Levi by its actual
closed representative, with its canonical point topology. -/
def parameterHomeomorph :
    RationalPoint F (parameterScheme χ).X ≃ₜ* levi χ :=
  dynamicCentralizerPointHomeomorph F G χ

/-- The genuine rational-character norms on the actual centralizer scheme. -/
abbrev normCharacters :
    rationalCharacters (parameterScheme χ) →
      (rationalPoints (parameterScheme χ) →* ℝ≥0ˣ) :=
  fun ψ => (rationalNormCharacters (parameterScheme χ) ψ).toMul

/-- The same norms on the literal common Levi, transported through its actual
closed representative. -/
abbrev leviNormCharacters :
    rationalCharacters (parameterScheme χ) → (levi χ →* ℝ≥0ˣ) :=
  fun ψ => (normCharacters χ ψ).comp (parameterHomeomorph χ).symm.toMulEquiv.toMonoidHom

/-- Actual unramified parameters reach both inductions through one homeomorphism. -/
def parameterTransport :
    unramifiedCharacters (normCharacters χ) ≃ₜ*
      unramifiedCharacters (leviNormCharacters χ) :=
  unramifiedCharactersHomeomorph (parameterHomeomorph χ) (normCharacters χ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Connected reductivity of this parameter scheme is proved from that of G. -/
theorem parameterScheme_isConnectedReductive (hG : IsConnectedReductive G) :
    IsConnectedReductive (parameterScheme χ) :=
  dynamicCentralizerReductive F G hG χ (parameterScheme χ)
    (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The original actual semidirect decomposition. -/
theorem decomposition : IsSemidirectDecomposition (parabolic χ) (levi χ) (radical χ) :=
  dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 _))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The opposite decomposition has exactly the same Levi, not an isomorphic copy. -/
theorem oppositeDecomposition :
    IsSemidirectDecomposition (oppositeParabolic χ) (levi χ) (oppositeRadical χ) := by
  simpa only [Dynamic.centralizer_inverseCocharacter] using
    (dynamic_isSemidirectDecomposition (Dynamic.inverseCocharacter χ) (Over.mk (𝟙 _)))

omit [LocallyOfFiniteType G.X.hom] in
theorem radical_isClosed : IsClosed (radical χ : Set (RationalPoint F G.X)) :=
  isClosed_unipotentPoints χ

omit [LocallyOfFiniteType G.X.hom] in
theorem oppositeRadical_isClosed :
    IsClosed (oppositeRadical χ : Set (RationalPoint F G.X)) :=
  isClosed_unipotentPoints (Dynamic.inverseCocharacter χ)

omit [LocallyOfFiniteType G.X.hom] in
theorem levi_isClosed : IsClosed (levi χ : Set (RationalPoint F G.X)) :=
  isClosed_rationalPoint_subgroup F (Dynamic.centralizer χ)
    (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Opposite actual radicals intersect trivially, without a root-system premise. -/
theorem radical_inf_oppositeRadical : radical χ ⊓ oppositeRadical χ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hx.2
    (Dynamic.unipotent_le_parabolic χ _ hx.1)

private theorem closedRestrictCharacter_eq_one_of_eq_bot
    (U : Subgroup (RationalPoint F G.X))
    (hU : IsClosed (U : Set (RationalPoint F G.X))) (hbot : U = ⊥)
    (M : Subgroup (RationalPoint F G.X))
    (hMU : M ≤ Subgroup.normalizer (U : Set (RationalPoint F G.X))) (m : M) :
    HaarModulus.closedRestrictCharacter U hU M hMU m = 1 := by
  let := hU.locallyCompactSpace
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have : Subsingleton U := by rw [hbot]; infer_instance
  have he : HaarModulus.normalizerConj U ⟨m, hMU m.property⟩ =
      ContinuousMulEquiv.refl U :=
    DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
  apply Units.ext
  change mulEquivHaarChar (HaarModulus.normalizerConj U ⟨m, hMU m.property⟩) = 1
  rw [he]
  simp

section Modulus

variable
  [MeasurableSpace ((radical χ).subgroupOf (oppositeRadical χ))]
  [BorelSpace ((radical χ).subgroupOf (oppositeRadical χ))]
  [MeasurableSpace ((oppositeRadical χ).subgroupOf (radical χ))]
  [BorelSpace ((oppositeRadical χ).subgroupOf (radical χ))]

omit [MeasurableSpace ((oppositeRadical χ).subgroupOf (radical χ))]
  [BorelSpace ((oppositeRadical χ).subgroupOf (radical χ))] in
/-- Opposite standard integrals have the required squared-modulus identity,
conditional only on the two displayed structural character premises. -/
theorem conditionalSquaredModulus
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G) :
    SquaredModulusCompatibility (decomposition χ) (radical_isClosed χ)
      (oppositeDecomposition χ) (oppositeRadical_isClosed χ) := by
  apply (squaredModulusCompatibility_iff _ _ _ _).mpr
  intro m
  have h := RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
    hRefl hCST hG χ (oppositeRadical χ) (levi χ) (radical χ) rfl rfl rfl
    (oppositeRadical_isClosed χ) (radical_isClosed χ)
    (oppositeDecomposition χ).levi_le_normalizer (decomposition χ).levi_le_normalizer m
  have hi := closedRestrictCharacter_eq_one_of_eq_bot
    (radical χ ⊓ oppositeRadical χ)
    ((radical_isClosed χ).inter (oppositeRadical_isClosed χ))
    (radical_inf_oppositeRadical χ) (levi χ)
    (levi_le_normalizer_intersection (decomposition χ) (oppositeDecomposition χ)) m
  rw [hi, Units.val_one, one_pow]
  have hv := congrArg (fun z : ℝ≥0ˣ => (z : ℝ≥0)) ((mul_comm _ _).trans h)
  simpa only [Units.val_mul, Units.val_one] using hv

omit [MeasurableSpace ((radical χ).subgroupOf (oppositeRadical χ))]
  [BorelSpace ((radical χ).subgroupOf (oppositeRadical χ))] in
/-- The reverse integral satisfies the same identity at the same common Levi. -/
theorem conditionalReverseSquaredModulus
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G) :
    SquaredModulusCompatibility (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (decomposition χ) (radical_isClosed χ) := by
  apply (squaredModulusCompatibility_iff _ _ _ _).mpr
  intro m
  have h := RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus
    hRefl hCST hG χ (oppositeRadical χ) (levi χ) (radical χ) rfl rfl rfl
    (oppositeRadical_isClosed χ) (radical_isClosed χ)
    (oppositeDecomposition χ).levi_le_normalizer (decomposition χ).levi_le_normalizer m
  have hi := closedRestrictCharacter_eq_one_of_eq_bot
    (oppositeRadical χ ⊓ radical χ)
    ((oppositeRadical_isClosed χ).inter (radical_isClosed χ))
    ((inf_comm _ _).trans (radical_inf_oppositeRadical χ)) (levi χ)
    (levi_le_normalizer_intersection (oppositeDecomposition χ) (decomposition χ)) m
  rw [hi, Units.val_one, one_pow]
  have hv := congrArg (fun z : ℝ≥0ˣ => (z : ℝ≥0)) h
  simpa only [Units.val_mul, Units.val_one] using hv

end Modulus

section SourceMeasures

open Haar

local instance dynamicOppositeStandardIntertwiningMeasurableSpace : MeasurableSpace (radical χ) := borel _
local instance dynamicOppositeStandardIntertwiningBorelSpace : BorelSpace (radical χ) := ⟨rfl⟩
local instance dynamicOppositeStandardIntertwiningMeasurableSpace2 : MeasurableSpace (oppositeRadical χ) := borel _
local instance dynamicOppositeStandardIntertwiningBorelSpace2 : BorelSpace (oppositeRadical χ) := ⟨rfl⟩
local instance dynamicOppositeStandardIntertwiningMeasurableSpace3 : MeasurableSpace ((radical χ).subgroupOf (oppositeRadical χ)) := borel _
local instance dynamicOppositeStandardIntertwiningBorelSpace3 : BorelSpace ((radical χ).subgroupOf (oppositeRadical χ)) := ⟨rfl⟩
local instance dynamicOppositeStandardIntertwiningMeasurableSpace4 : MeasurableSpace ((oppositeRadical χ).subgroupOf (radical χ)) := borel _
local instance dynamicOppositeStandardIntertwiningBorelSpace4 : BorelSpace ((oppositeRadical χ).subgroupOf (radical χ)) := ⟨rfl⟩
local instance dynamicOppositeStandardIntertwiningMeasurableSpace5 : MeasurableSpace (QuotientSpace (U := radical χ) (oppositeRadical χ)) :=
  borel _
local instance dynamicOppositeStandardIntertwiningBorelSpace5 : BorelSpace (QuotientSpace (U := radical χ) (oppositeRadical χ)) := ⟨rfl⟩
local instance dynamicOppositeStandardIntertwiningMeasurableSpace6 : MeasurableSpace (QuotientSpace (U := oppositeRadical χ) (radical χ)) :=
  borel _
local instance dynamicOppositeStandardIntertwiningBorelSpace6 : BorelSpace (QuotientSpace (U := oppositeRadical χ) (radical χ)) := ⟨rfl⟩

private theorem radicalCover (x : radical χ) :
    ∃ C : OpenSubgroup (radical χ), IsCompact (C : Set (radical χ)) ∧ x ∈ C := by
  obtain ⟨C, hC, hx⟩ := exists_compactOpenSubgroup χ {x} isCompact_singleton
  exact ⟨C, hC, hx (Set.mem_singleton x)⟩

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Intrinsic Haar on the original radical, with the inverse image of K of mass one. -/
abbrev radicalHaar : Measure (radical χ) :=
  subgroupCompactOpenHaar K hK (radical χ) (radical_isClosed χ)

/-- Intrinsic Haar on the opposite radical, at the same ambient source scale. -/
abbrev oppositeRadicalHaar : Measure (oppositeRadical χ) :=
  subgroupCompactOpenHaar K hK (oppositeRadical χ) (oppositeRadical_isClosed χ)

/-- Intrinsic Haar on the forward integral's actual intersection. -/
abbrev forwardIntersectionHaar : Measure ((radical χ).subgroupOf (oppositeRadical χ)) :=
  sourceIntersectionHaar K hK (radical χ) (oppositeRadical χ)
    (radical_isClosed χ) (oppositeRadical_isClosed χ)

/-- Intrinsic Haar on the reverse integral's actual intersection. -/
abbrev reverseIntersectionHaar : Measure ((oppositeRadical χ).subgroupOf (radical χ)) :=
  sourceIntersectionHaar K hK (oppositeRadical χ) (radical χ)
    (oppositeRadical_isClosed χ) (radical_isClosed χ)

instance radicalHaar_rightInvariant : IsMulRightInvariant (radicalHaar χ K hK) :=
  sourceSubgroupHaar_rightInvariant_of_cover K hK (radical χ)
    (radical_isClosed χ) (radicalCover χ)

instance oppositeRadicalHaar_rightInvariant :
    IsMulRightInvariant (oppositeRadicalHaar χ K hK) :=
  sourceSubgroupHaar_rightInvariant_of_cover K hK (oppositeRadical χ)
    (oppositeRadical_isClosed χ) (radicalCover (Dynamic.inverseCocharacter χ))

instance forwardIntersectionHaar_rightInvariant :
    IsMulRightInvariant (forwardIntersectionHaar χ K hK) :=
  sourceIntersectionHaar_rightInvariant_of_cover K hK (radical χ) (oppositeRadical χ)
    (radical_isClosed χ) (oppositeRadical_isClosed χ) (radicalCover χ)

instance reverseIntersectionHaar_rightInvariant :
    IsMulRightInvariant (reverseIntersectionHaar χ K hK) :=
  sourceIntersectionHaar_rightInvariant_of_cover K hK (oppositeRadical χ) (radical χ)
    (oppositeRadical_isClosed χ) (radical_isClosed χ)
    (radicalCover (Dynamic.inverseCocharacter χ))

/-- The actual forward quotient, selected by proved Weil compatibility at K. -/
abbrev forwardQuotientMeasure :
    Measure (QuotientSpace (U := radical χ) (oppositeRadical χ)) :=
  DynamicSource.quotientMeasure K hK χ (Dynamic.inverseCocharacter χ)

/-- The actual reverse quotient uses the identical source normalization K. -/
abbrev reverseQuotientMeasure :
    Measure (QuotientSpace (U := oppositeRadical χ) (radical χ)) :=
  DynamicSource.quotientMeasure K hK (Dynamic.inverseCocharacter χ) χ

/-- Full complex Weil compatibility for the actual forward quotient. -/
theorem forwardQuotientMeasure_isCompatible :
    QuotientIntegration.IsCompatible ((radical χ).subgroupOf (oppositeRadical χ))
      (oppositeRadicalHaar χ K hK) (forwardIntersectionHaar χ K hK)
      (forwardQuotientMeasure χ K hK) :=
  DynamicSource.quotientMeasure_isCompatible K hK χ (Dynamic.inverseCocharacter χ)

/-- Full complex Weil compatibility for the actual reverse quotient. -/
theorem reverseQuotientMeasure_isCompatible :
    QuotientIntegration.IsCompatible ((oppositeRadical χ).subgroupOf (radical χ))
      (radicalHaar χ K hK) (reverseIntersectionHaar χ K hK)
      (reverseQuotientMeasure χ K hK) :=
  DynamicSource.quotientMeasure_isCompatible K hK (Dynamic.inverseCocharacter χ) χ

theorem forwardQuotientMeasure_ne_zero : forwardQuotientMeasure χ K hK ≠ 0 :=
  DynamicSource.quotientMeasure_ne_zero K hK χ (Dynamic.inverseCocharacter χ)

theorem reverseQuotientMeasure_ne_zero : reverseQuotientMeasure χ K hK ≠ 0 :=
  DynamicSource.quotientMeasure_ne_zero K hK (Dynamic.inverseCocharacter χ) χ

section Families

open Induction

/-- The actual forward full domain. No openness or nonemptiness is asserted. -/
def forwardFullDomainRegion (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    Set (unramifiedCharacters (normCharacters χ)) :=
  standardIntertwiningFullDomainRegion (decomposition χ) (radical_isClosed χ)
    (oppositeRadical χ) (parameterHomeomorph χ) (normCharacters χ)
    (forwardQuotientMeasure χ K hK) A

/-- The actual reverse full domain uses the same centralizer parameters and K. -/
def reverseFullDomainRegion (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    Set (unramifiedCharacters (normCharacters χ)) :=
  standardIntertwiningFullDomainRegion (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (radical χ) (parameterHomeomorph χ) (normCharacters χ)
    (reverseQuotientMeasure χ K hK) A

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)

/-- The actual forward opposite standard integral on its entire full domain,
at the intrinsic common source Haar scale. All measure and modulus inputs
are supplied by the proved constructions above. -/
def conditionalForwardFamily (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : forwardFullDomainRegion χ K hK A) :
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation.IntertwiningMap
    (UnramifiedLeviInduction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  standardInductionIntertwinerFamily (decomposition χ) (radical_isClosed χ)
    (oppositeRadical χ) (parameterHomeomorph χ) (normCharacters χ)
    (forwardQuotientMeasure χ K hK) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadicalHaar χ K hK) (forwardIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG) A z

/-- The reverse actual integral uses the same literal Levi, norms, and source K. -/
def conditionalReverseFamily (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : reverseFullDomainRegion χ K hK A) :
    (UnramifiedLeviInduction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation.IntertwiningMap
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  standardInductionIntertwinerFamily (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (radical χ) (parameterHomeomorph χ) (normCharacters χ)
    (reverseQuotientMeasure χ K hK) (decomposition χ) (radical_isClosed χ)
    (radicalHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalReverseSquaredModulus χ hRefl hCST hG) A z

/-- Every forward value represents the original smooth-dual scalar integral
at every source input and ambient group element. -/
theorem conditionalForwardFamily_spec (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : forwardFullDomainRegion χ K hK A)
    (f : UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    HasIntegral (decomposition χ) (radical_isClosed χ) (oppositeRadical χ)
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
      (forwardQuotientMeasure χ K hK) f
      (eval (oppositeParabolic χ) (leviInflatedInducingRepresentation
        (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
        (A.twist (parameterTransport χ z.val).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val))))
        (conditionalForwardFamily χ K hK hRefl hCST hG A z f)) :=
  standardInductionIntertwinerFamily_spec (decomposition χ) (radical_isClosed χ)
    (oppositeRadical χ) (parameterHomeomorph χ) (normCharacters χ)
    (forwardQuotientMeasure χ K hK) (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (oppositeRadicalHaar χ K hK) (forwardIntersectionHaar χ K hK)
    (forwardQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalSquaredModulus χ hRefl hCST hG) A z f

/-- Every reverse value satisfies the analogous original integral relation. -/
theorem conditionalReverseFamily_spec (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : reverseFullDomainRegion χ K hK A)
    (f : UnramifiedLeviInduction (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    HasIntegral (oppositeDecomposition χ) (oppositeRadical_isClosed χ) (radical χ)
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
      (reverseQuotientMeasure χ K hK) f
      (eval (parabolic χ) (leviInflatedInducingRepresentation
        (decomposition χ) (radical_isClosed χ)
        (A.twist (parameterTransport χ z.val).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val))))
        (conditionalReverseFamily χ K hK hRefl hCST hG A z f)) :=
  standardInductionIntertwinerFamily_spec (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
    (radical χ) (parameterHomeomorph χ) (normCharacters χ)
    (reverseQuotientMeasure χ K hK) (decomposition χ) (radical_isClosed χ)
    (radicalHaar χ K hK) (reverseIntersectionHaar χ K hK)
    (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
    (conditionalReverseSquaredModulus χ hRefl hCST hG) A z f

end Families

end SourceMeasures

end Langlands.Plancherel.DynamicOppositeStandardIntertwining
