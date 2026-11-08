import Langlands.Representation.Plancherel.StandardIntertwiningNonvanishing
import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.CommonLeviCompactSplitting

/-! # Nonvanishing of the actual dynamic opposite standard integrals -/

noncomputable section

universe u uG uV

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- If an open subgroup of the Levi fixes `v`, then every open subgroup `Q` of
`G` inside one identity neighborhood has `P ∩ Q` fixing `v` for the inflated
action. -/
theorem exists_nhds_fixedVectors_comp_projection (hr : Continuous h.projection)
    (τ : Representation ℂ M V) (S : OpenSubgroup M) (v : V)
    (hv : v ∈ fixedVectors τ S.toSubgroup) :
    ∃ W ∈ 𝓝 (1 : G), ∀ Q : OpenSubgroup G, (Q : Set G) ⊆ W →
      v ∈ fixedVectors (τ.comp h.projection) (conjOpenSubgroup P Q 1).toSubgroup := by
  obtain ⟨O, hO, he⟩ := IsInducing.subtypeVal.isOpen_iff.mp
    (S.isOpen.preimage hr)
  have h1 : (1 : G) ∈ O := by
    have h1S : (1 : P) ∈ h.projection ⁻¹' (S : Set M) := by
      change h.projection 1 ∈ S
      rw [map_one]
      exact S.one_mem
    exact (Set.ext_iff.mp he 1).mpr h1S
  refine ⟨O, hO.mem_nhds h1, fun Q hQ => ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro p
  have hpQ : ((p : P) : G) ∈ Q := by
    simpa only [inv_one, one_mul, mul_one] using mem_conjOpenSubgroup.mp p.property
  have hpO : (p : P) ∈ h.projection ⁻¹' (S : Set M) :=
    (Set.ext_iff.mp he (p : P)).mp (hQ hpQ)
  have hfix := (Representation.mem_invariants _ _).mp hv ⟨h.projection p, hpO⟩
  exact hfix

end Generic

namespace DynamicOppositeNonvanishing

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance dynamicOppositeNonvanishingIsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance dynamicOppositeNonvanishingTopologicalSpace :
    TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance dynamicOppositeNonvanishingT2SpaceF : T2Space F :=
  BruhatTits.localField_t2Space F
local instance dynamicOppositeNonvanishingIsTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
local instance dynamicOppositeNonvanishingT2Space : T2Space (RationalPoint F G.X) :=
  rationalPoint_t2Space F G
local instance dynamicOppositeNonvanishingLocallyCompactSpace :
    LocallyCompactSpace (RationalPoint F G.X) := rationalPoint_locallyCompactSpace F G
local instance dynamicOppositeNonvanishingNonarchimedeanGroup :
    NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local instance dynamicOppositeNonvanishingCentralizerClosedImmersion :
    IsClosedImmersion (Dynamic.Affine.centralizerHom χ).hom.hom.left :=
  Dynamic.Affine.isClosedSubgroup_centralizerHom χ
local instance dynamicOppositeNonvanishingCentralizerAffine :
    IsAffine (parameterScheme χ).X.left :=
  isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom χ).hom.hom.left
local instance dynamicOppositeNonvanishingParameterTopology :
    TopologicalSpace (RationalPoint F (parameterScheme χ).X) :=
  rationalPointTopology F (parameterScheme χ).X

local instance dynamicOppositeNonvanishingMeasurableSpace1 :
    MeasurableSpace (radical χ) := borel _
local instance dynamicOppositeNonvanishingBorelSpace1 : BorelSpace (radical χ) := ⟨rfl⟩
local instance dynamicOppositeNonvanishingMeasurableSpace2 :
    MeasurableSpace (oppositeRadical χ) := borel _
local instance dynamicOppositeNonvanishingBorelSpace2 :
    BorelSpace (oppositeRadical χ) := ⟨rfl⟩
local instance dynamicOppositeNonvanishingMeasurableSpace3 :
    MeasurableSpace ((radical χ).subgroupOf (oppositeRadical χ)) := borel _
local instance dynamicOppositeNonvanishingBorelSpace3 :
    BorelSpace ((radical χ).subgroupOf (oppositeRadical χ)) := ⟨rfl⟩
local instance dynamicOppositeNonvanishingMeasurableSpace4 :
    MeasurableSpace ((oppositeRadical χ).subgroupOf (radical χ)) := borel _
local instance dynamicOppositeNonvanishingBorelSpace4 :
    BorelSpace ((oppositeRadical χ).subgroupOf (radical χ)) := ⟨rfl⟩
local instance dynamicOppositeNonvanishingMeasurableSpace5 :
    MeasurableSpace (QuotientSpace (U := radical χ) (oppositeRadical χ)) := borel _
local instance dynamicOppositeNonvanishingBorelSpace5 :
    BorelSpace (QuotientSpace (U := radical χ) (oppositeRadical χ)) := ⟨rfl⟩
local instance dynamicOppositeNonvanishingMeasurableSpace6 :
    MeasurableSpace (QuotientSpace (U := oppositeRadical χ) (radical χ)) := borel _
local instance dynamicOppositeNonvanishingBorelSpace6 :
    BorelSpace (QuotientSpace (U := oppositeRadical χ) (radical χ)) := ⟨rfl⟩

/-- Every point of `Q` is a product `o z w` with `o ∈ Q ∩ U(χ⁻¹)`, `z` in the
dynamic Levi `Z(χ)(F)` and `w ∈ Q ∩ U(χ)`: an Iwahori factorization of `Q`
along `χ`. -/
def HasOppositeIwahoriFactorization (Q : OpenSubgroup (RationalPoint F G.X)) : Prop :=
  ∀ k ∈ Q, ∃ o ∈ unipotentPoints (Dynamic.inverseCocharacter χ),
      ∃ z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)), ∃ w ∈ unipotentPoints χ,
        o ∈ Q ∧ w ∈ Q ∧ k = o * z * w

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- A compact open subgroup with a factorization `o z w` has the local product
property for the forward integral from `P(χ)` to `P(χ⁻¹)`: the trivial
intersection `P(χ) ∩ U(χ⁻¹) = 1` forces every point of `U(χ⁻¹) ∩ P(χ) Q` into
`Q`. -/
theorem forward_hasSourceLocalProduct (Q : OpenSubgroup (RationalPoint F G.X))
    (hfac : HasOppositeIwahoriFactorization χ Q) :
    HasSourceLocalProduct (parabolic χ) (radical χ) (oppositeRadical χ) Q := by
  intro x hx hPQ
  obtain ⟨p, hp, k, hk, hxk⟩ := hPQ
  obtain ⟨o, ho, z, hz, w, hw, hoQ, -, hk'⟩ := hfac k⁻¹ (Q.inv_mem hk)
  have hko : k * o = w⁻¹ * z⁻¹ := by
    have hk2 : k = (o * z * w)⁻¹ := by rw [← hk', inv_inv]
    rw [hk2]
    group
  have hxoP : x * o ∈ parabolic χ := by
    rw [hxk, mul_assoc, hko]
    exact mul_mem hp (mul_mem (inv_mem ((decomposition χ).unipotent_le hw))
      (inv_mem ((decomposition χ).levi_le hz)))
  have hxoU : x * o ∈ unipotentPoints (Dynamic.inverseCocharacter χ) := mul_mem hx ho
  have h1 : x * o = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hxoU hxoP
  refine ⟨1, one_mem _, o⁻¹, Q.inv_mem hoQ, inv_mem ho, ?_⟩
  rw [one_mul]
  exact eq_inv_of_mul_eq_one_left h1

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The same factorization gives the local product property for the reverse
integral from `P(χ⁻¹)` to `P(χ)`. -/
theorem reverse_hasSourceLocalProduct (Q : OpenSubgroup (RationalPoint F G.X))
    (hfac : HasOppositeIwahoriFactorization χ Q) :
    HasSourceLocalProduct (oppositeParabolic χ) (oppositeRadical χ) (radical χ) Q := by
  intro x hx hPQ
  obtain ⟨p, hp, k, hk, hxk⟩ := hPQ
  obtain ⟨o, ho, z, hz, w, hw, -, hwQ, hk'⟩ := hfac k hk
  have hxwP : x * w⁻¹ ∈ oppositeParabolic χ := by
    rw [hxk, hk', mul_assoc, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_mem hp (mul_mem ((oppositeDecomposition χ).unipotent_le ho)
      ((oppositeDecomposition χ).levi_le hz))
  have hxwU : x * w⁻¹ ∈ unipotentPoints
      (Dynamic.inverseCocharacter (Dynamic.inverseCocharacter χ)) := by
    rw [Dynamic.inverseCocharacter_inverseCocharacter]
    exact mul_mem hx (inv_mem hw)
  have h1 : x * w⁻¹ = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (Dynamic.inverseCocharacter χ) hxwU hxwP
  refine ⟨1, one_mem _, w, hwQ, hw, ?_⟩
  rw [one_mul]
  exact mul_inv_eq_one.mp h1

omit [LocallyOfFiniteType G.X.hom] in
/-- Every identity neighborhood contains a compact open subgroup with a
factorization `o z w` along `χ`. -/
theorem exists_factored_compactOpen_subset (hG : IsConnectedReductive G)
    {W : Set (RationalPoint F G.X)} (hW : W ∈ 𝓝 (1 : RationalPoint F G.X)) :
    ∃ Q : OpenSubgroup (RationalPoint F G.X), IsCompact (Q : Set (RationalPoint F G.X)) ∧
      (Q : Set (RationalPoint F G.X)) ⊆ W ∧ HasOppositeIwahoriFactorization χ Q := by
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨V, hVc, hVW⟩ := Jacquet.exists_isCompact_openSubgroup_subset hW
  obtain ⟨g, -, Q, hQc, hQV, hfac, -⟩ := CommonLeviSplitting.exists_iwahoriCut χ V hVc
  exact ⟨Q, hQc, hQV.trans hVW, hfac⟩

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- At every parameter of its full domain, the actual forward opposite
standard integral is nonzero, as soon as the inducing representation has a
nonzero vector. -/
theorem conditionalForwardFamily_ne_zero (z : forwardFullDomainRegion χ K hK A)
    (v : A) (hv0 : v ≠ 0) :
    conditionalForwardFamily χ K hK hRefl hCST hG A z ≠ 0 := by
  have hτ : IsSmooth (Langlands.twist (HaarModulus.closedHalfCharacter (radical χ)
      (radical_isClosed χ) (levi χ) (decomposition χ).levi_le_normalizer)
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
          (parameterTransport χ z.val))).representation) :=
    (isSmooth_twist_iff _ _ (HaarModulus.isOpen_ker_closedHalfCharacter _ _ _ _)).mpr
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
          (parameterTransport χ z.val))).isSmooth
  obtain ⟨S, hS⟩ := hτ v
  obtain ⟨W, hW, hWQ⟩ := exists_nhds_fixedVectors_comp_projection (decomposition χ)
    (projection_continuous χ) _ S v hS
  exact (exists_factored_compactOpen_subset χ hG hW).elim fun Q hQ =>
    standardInductionIntertwinerFamily_ne_zero (decomposition χ) (radical_isClosed χ)
      (parameterHomeomorph χ) (normCharacters χ) (forwardQuotientMeasure χ K hK)
      (oppositeDecomposition χ) (oppositeRadical_isClosed χ)
      (oppositeRadicalHaar χ K hK) (forwardIntersectionHaar χ K hK)
      (forwardQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
      (conditionalSquaredModulus χ hRefl hCST hG) A z Q hQ.1 v
      (hWQ Q hQ.2.1) (forward_hasSourceLocalProduct χ Q hQ.2.2) hv0

/-- The reverse actual opposite standard integral is nonzero at every
parameter of its full domain, under the same condition. -/
theorem conditionalReverseFamily_ne_zero (z : reverseFullDomainRegion χ K hK A)
    (v : A) (hv0 : v ≠ 0) :
    conditionalReverseFamily χ K hK hRefl hCST hG A z ≠ 0 := by
  have hτ : IsSmooth (Langlands.twist (HaarModulus.closedHalfCharacter (oppositeRadical χ)
      (oppositeRadical_isClosed χ) (levi χ) (oppositeDecomposition χ).levi_le_normalizer)
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
          (parameterTransport χ z.val))).representation) :=
    (isSmooth_twist_iff _ _ (HaarModulus.isOpen_ker_closedHalfCharacter _ _ _ _)).mpr
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ)
          (parameterTransport χ z.val))).isSmooth
  obtain ⟨S, hS⟩ := hτ v
  obtain ⟨W, hW, hWQ⟩ := exists_nhds_fixedVectors_comp_projection (oppositeDecomposition χ)
    (oppositeProjection_continuous χ) _ S v hS
  exact (exists_factored_compactOpen_subset χ hG hW).elim fun Q hQ =>
    standardInductionIntertwinerFamily_ne_zero (oppositeDecomposition χ)
      (oppositeRadical_isClosed χ)
      (parameterHomeomorph χ) (normCharacters χ) (reverseQuotientMeasure χ K hK)
      (decomposition χ) (radical_isClosed χ)
      (radicalHaar χ K hK) (reverseIntersectionHaar χ K hK)
      (reverseQuotientMeasure_isCompatible χ K hK) (levi_isClosed χ)
      (conditionalReverseSquaredModulus χ hRefl hCST hG) A z Q hQ.1 v
      (hWQ Q hQ.2.1) (reverse_hasSourceLocalProduct χ Q hQ.2.2) hv0

end DynamicOppositeNonvanishing

end Langlands.Plancherel
