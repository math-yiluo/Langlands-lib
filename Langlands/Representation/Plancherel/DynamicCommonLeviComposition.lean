import Langlands.Representation.Plancherel.DynamicOppositeStandardIntertwining
import Langlands.Representation.Plancherel.CommonLeviCompactSplitting

/-! # Composition of actual standard intertwining integrals for a common Levi (target)

Waldspurger 2003, IV.1 (12) (printed p.283): if `P, P', P'' ∈ P(M)` satisfy
`d(P', P) = d(P', P'') + d(P'', P)`, where `d(P₁, P₂) = ♯(Σ^red(P₁) ∩ Σ^red(P̄₂))`
(IV.1, printed p.279), then `J_{P'|P}(π) = J_{P'|P''}(π) J_{P''|P}(π)`.

This module states that identity for actual dynamic data, on the common domain where the three
standard integrals converge absolutely. Fix a base cocharacter `χ` of `G`, with literal Levi
`M = Z_G(χ)(F)`, and let `ψ₀, ψ₁, ψ₂` be cocharacters with the same centralizer subgroup
functor. Their dynamic parabolics `P_G(ψᵢ)` then have the literal Levi `M`
(`commonDecomposition`). For two such cocharacters `ψ, ψ'`, `pairFamily` is the actual standard
integral from the `P_G(ψ)`-normalized induction to the `P_G(ψ')`-normalized induction of an
unramified twist of a smooth representation of `M`, over `(U_G(ψ) ∩ U_G(ψ')) \ U_G(ψ')` with
the source quotient measure at one compact open subgroup `K`. It is defined on the full domain
region and is conditional on the squared-modulus identity of the two radicals, supplied as a
proof. For `ψ = χ`, `ψ' = χ⁻¹` it is the published opposite family
(`pairFamily_inverse_eq_conditionalForwardFamily`).

`IsDistanceAdditive` is the group-theoretic form of the distance condition:
`U₀ ∩ U₂ ≤ U₁` and `Ū₀ ∩ Ū₂ ≤ Ū₁` for the radicals `Uᵢ = U_G(ψᵢ)` and `Ūᵢ = U_G(ψᵢ⁻¹)`.
The compact open subgroup `K` is required to split along the two consecutive pairs, in the
sense of the published `CommonLeviSplitting.SplitsAlong`.

The structural target `DistanceAdditiveRadicalFactorizationStatement` asserts the ordered
product decomposition of the three radicals, with complements `U₁ ∩ Ū₀` and `U₂ ∩ Ū₁`. The
main target `ConditionalDynamicCommonLeviCompositionStatement` asserts IV.1 (12) for the actual
families, conditional on that structural target. No target is proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General StandardIntertwining DynamicOppositeStandardIntertwining
open BruhatTits.DynamicUnipotentContainment
open OrderedSubgroupFactorization

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

/-! ### The common Levi -/

section Decomposition

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- **The literal common Levi.** A cocharacter `ψ` with the same centralizer subgroup functor as
`χ` has the actual semidirect decomposition `P_G(ψ)(F) = M ⋉ U_G(ψ)(F)` with the literal Levi
`M = Z_G(χ)(F)`, not an isomorphic copy. -/
theorem commonDecomposition (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ) :
    IsSemidirectDecomposition (parabolic ψ) (levi χ) (radical ψ) := by
  have h := decomposition ψ
  simp only [levi, hψ] at h
  exact h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- The inverse of a cocharacter with the centralizer of `χ` has the same centralizer. -/
theorem centralizer_inverseCocharacter_eq (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ) :
    Dynamic.centralizer (Dynamic.inverseCocharacter ψ) = Dynamic.centralizer χ :=
  (Dynamic.centralizer_inverseCocharacter ψ).trans hψ

end Decomposition

/-! ### Borel structures on the actual radicals, intersections and quotients -/

local instance commonLeviRadicalMeasurableSpace
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : MeasurableSpace (radical ψ) := borel _
local instance commonLeviRadicalBorelSpace
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : BorelSpace (radical ψ) := ⟨rfl⟩
local instance commonLeviIntersectionMeasurableSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace ((radical ψ).subgroupOf (radical ψ')) := borel _
local instance commonLeviIntersectionBorelSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace ((radical ψ).subgroupOf (radical ψ')) := ⟨rfl⟩
local instance commonLeviQuotientMeasurableSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    MeasurableSpace (QuotientSpace (U := radical ψ) (radical ψ')) := borel _
local instance commonLeviQuotientBorelSpace
    (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    BorelSpace (QuotientSpace (U := radical ψ) (radical ψ')) := ⟨rfl⟩

/-! ### Actual standard integrals between two parabolics with Levi `M` -/

section Families

open Haar Induction

private theorem commonLeviRadicalCover (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (x : radical ψ) :
    ∃ C : OpenSubgroup (radical ψ), IsCompact (C : Set (radical ψ)) ∧ x ∈ C := by
  obtain ⟨C, hC, hx⟩ := exists_compactOpenSubgroup ψ {x} isCompact_singleton
  exact ⟨C, hC, hx (Set.mem_singleton x)⟩

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Intrinsic Haar measure on the actual intersection `U_G(ψ) ∩ U_G(ψ')`, as a subgroup of
`U_G(ψ')`, with the inverse image of `K` of mass one. -/
abbrev pairIntersectionHaar (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    Measure ((radical ψ).subgroupOf (radical ψ')) :=
  sourceIntersectionHaar K hK (radical ψ) (radical ψ') (radical_isClosed ψ) (radical_isClosed ψ')

instance pairIntersectionHaar_rightInvariant (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    IsMulRightInvariant (pairIntersectionHaar K hK ψ ψ') :=
  sourceIntersectionHaar_rightInvariant_of_cover K hK (radical ψ) (radical ψ')
    (radical_isClosed ψ) (radical_isClosed ψ') (commonLeviRadicalCover ψ)

/-- The actual quotient measure on `(U_G(ψ) ∩ U_G(ψ')) \ U_G(ψ')`, selected by proved Weil
compatibility at the source scale `K`. -/
abbrev pairQuotientMeasure (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    Measure (QuotientSpace (U := radical ψ) (radical ψ')) :=
  DynamicSource.quotientMeasure K hK ψ ψ'

/-- Full complex Weil compatibility for the actual pair quotient. -/
theorem pairQuotientMeasure_isCompatible (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    QuotientIntegration.IsCompatible ((radical ψ).subgroupOf (radical ψ'))
      (radicalHaar ψ' K hK) (pairIntersectionHaar K hK ψ ψ')
      (pairQuotientMeasure K hK ψ ψ') :=
  DynamicSource.quotientMeasure_isCompatible K hK ψ ψ'

variable (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)

/-- The actual full domain of the standard integral from `P_G(ψ)` to `P_G(ψ')`, in the
unramified parameters of the common Levi `M = Z_G(χ)(F)`. No openness or nonemptiness is
asserted. -/
def pairFullDomainRegion (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    Set (unramifiedCharacters (normCharacters χ)) :=
  standardIntertwiningFullDomainRegion (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (radical ψ') (parameterHomeomorph χ) (normCharacters χ)
    (pairQuotientMeasure K hK ψ ψ') A

/-- **The actual standard integral `J_{P_G(ψ')|P_G(ψ)}`** on its full domain, between the
normalized inductions of the same unramified twist of `A`, at the intrinsic source Haar scale
`K`. It is conditional on the squared-modulus identity `hδ` of the two radicals over `M`. -/
def pairFamily
    (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : pairFullDomainRegion χ K hK ψ hψ ψ' A) :
    (UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation.IntertwiningMap
    (UnramifiedLeviInduction (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
      (leviNormCharacters χ) (parameterTransport χ z.val) A).representation :=
  standardInductionIntertwinerFamily (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (radical ψ') (parameterHomeomorph χ) (normCharacters χ)
    (pairQuotientMeasure K hK ψ ψ') (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
    (radicalHaar ψ' K hK) (pairIntersectionHaar K hK ψ ψ')
    (pairQuotientMeasure_isCompatible K hK ψ ψ') (levi_isClosed χ) hδ A z

/-- Every value of the pair family represents the original smooth-dual scalar integrals over
`(U_G(ψ) ∩ U_G(ψ')) \ U_G(ψ')` at every source vector and ambient group element. -/
theorem pairFamily_spec
    (hδ : SquaredModulusCompatibility (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (commonDecomposition χ ψ' hψ') (radical_isClosed ψ'))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : pairFullDomainRegion χ K hK ψ hψ ψ' A)
    (f : UnramifiedLeviInduction (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
      (leviNormCharacters χ) (parameterTransport χ z.val) A) :
    HasIntegral (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (radical ψ')
      (A.twist (parameterTransport χ z.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val)))
      (pairQuotientMeasure K hK ψ ψ') f
      (eval (parabolic ψ') (leviInflatedInducingRepresentation
        (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
        (A.twist (parameterTransport χ z.val).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z.val))))
        (pairFamily χ K hK ψ hψ ψ' hψ' hδ A z f)) :=
  standardInductionIntertwinerFamily_spec (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (radical ψ') (parameterHomeomorph χ) (normCharacters χ)
    (pairQuotientMeasure K hK ψ ψ') (commonDecomposition χ ψ' hψ') (radical_isClosed ψ')
    (radicalHaar ψ' K hK) (pairIntersectionHaar K hK ψ ψ')
    (pairQuotientMeasure_isCompatible K hK ψ ψ') (levi_isClosed χ) hδ A z f

/-- The opposite full domain is the pair full domain for `ψ = χ`, `ψ' = χ⁻¹`. -/
theorem forwardFullDomainRegion_eq_pair (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    forwardFullDomainRegion χ K hK A =
      pairFullDomainRegion χ K hK χ rfl (Dynamic.inverseCocharacter χ) A :=
  rfl

/-- **Compatibility with the opposite family.** For `ψ = χ` and `ψ' = χ⁻¹`, the pair family
with the published conditional squared-modulus proof is the published forward opposite family
`J_{P̄|P}`. -/
theorem pairFamily_inverse_eq_conditionalForwardFamily
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : forwardFullDomainRegion χ K hK A) :
    pairFamily χ K hK χ rfl (Dynamic.inverseCocharacter χ)
        (Dynamic.centralizer_inverseCocharacter χ)
        (conditionalSquaredModulus χ hRefl hCST hG) A z =
      conditionalForwardFamily χ K hK hRefl hCST hG A z :=
  rfl

end Families

/-! ### The distance condition -/

section Conditions

/-- **The distance condition `d(P₂, P₀) = d(P₂, P₁) + d(P₁, P₀)`, group-theoretic form.** For
the radicals `Uᵢ = U_G(ψᵢ)(F)` and `Ūᵢ = U_G(ψᵢ⁻¹)(F)`: `U₀ ∩ U₂ ≤ U₁` and `Ū₀ ∩ Ū₂ ≤ Ū₁`. With
`Σᵢ` the reduced roots of `P_G(ψᵢ)`, Waldspurger's distance `d(P₂, P₀) = ♯(Σ₂ ∩ -Σ₀)` satisfies
`Σ₂ ∩ -Σ₀ ⊆ (Σ₂ ∩ -Σ₁) ⊔ (Σ₁ ∩ -Σ₀)`, a disjoint union, and the distance condition holds exactly
when this inclusion is an equality. That happens exactly when no root lies in `Σ₀ ∩ Σ₂` but not
in `Σ₁`, and also exactly when no root lies in `-Σ₀ ∩ -Σ₂` but not in `-Σ₁`. Each conjunct is
the group form of one of these two root conditions. -/
def IsDistanceAdditive (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : Prop :=
  radical ψ₀ ⊓ radical ψ₂ ≤ radical ψ₁ ∧
    oppositeRadical ψ₀ ⊓ oppositeRadical ψ₂ ≤ oppositeRadical ψ₁

end Conditions

/-! ### Targets -/

/-- **Structural target: ordered factorization of the radicals.** Let `G` be connected reductive
and let `ψ₀, ψ₁, ψ₂` be cocharacters with the same centralizer subgroup functor satisfying the
distance condition. Then the radicals `Uᵢ = U_G(ψᵢ)(F)` have the literal ordered product
coordinates of `OrderedSubgroupFactorization`, with complements `V = U₁ ∩ Ū₀` and `W = U₂ ∩ Ū₁`:
`U₁ = (U₀ ∩ U₁) V`, `U₂ = (U₁ ∩ U₂) W` and `U₂ = (U₀ ∩ U₂) V W`, each multiplication map being a
homeomorphism. -/
def DistanceAdditiveRadicalFactorizationStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G,
      Dynamic.centralizer ψ₁ = Dynamic.centralizer ψ₀ →
      Dynamic.centralizer ψ₂ = Dynamic.centralizer ψ₀ →
      IsDistanceAdditive ψ₀ ψ₁ ψ₂ →
      Nonempty (OrderedSubgroupFactorization (radical ψ₀) (radical ψ₁) (radical ψ₂)
        (radical ψ₁ ⊓ oppositeRadical ψ₀) (radical ψ₂ ⊓ oppositeRadical ψ₁))

/-- **Target (Waldspurger IV.1 (12) for actual dynamic parabolics).** Let `G` be connected
reductive, `χ` a cocharacter with literal Levi `M = Z_G(χ)(F)`, and `ψ₀, ψ₁, ψ₂` cocharacters with
the centralizer of `χ` satisfying the distance condition. Let `K` be a compact open subgroup such
that `K ∩ U₁` splits along `ψ₀` and `K ∩ U₂` splits along `ψ₁`, in the sense of the published
`CommonLeviSplitting.SplitsAlong`. The instance `[Smooth G.X.hom]`, which `SplitsAlong` requires,
is the field `smooth` of `IsConnectedReductive G`. Assume the structural target
`DistanceAdditiveRadicalFactorizationStatement`. Then for every smooth representation `A` of `M`,
every unramified parameter `z` in the full domains of the three standard integrals, and every
squared-modulus proof defining them, `J_{P₂|P₀}(z) = J_{P₂|P₁}(z) J_{P₁|P₀}(z)` on the
`P₀`-normalized induction, where `Pᵢ = P_G(ψᵢ)`. -/
def ConditionalDynamicCommonLeviCompositionStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth G.X.hom]
    (_hfac : DistanceAdditiveRadicalFactorizationStatement.{u})
    (_hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (h₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ)
    (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer χ)
    (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer χ)
    (_hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂)
    (_hK₁₀ : CommonLeviSplitting.SplitsAlong K ψ₀ ψ₁)
    (_hK₂₁ : CommonLeviSplitting.SplitsAlong K ψ₁ ψ₂)
    (hδ₁₀ : SquaredModulusCompatibility (commonDecomposition χ ψ₀ h₀) (radical_isClosed ψ₀)
      (commonDecomposition χ ψ₁ h₁) (radical_isClosed ψ₁))
    (hδ₂₁ : SquaredModulusCompatibility (commonDecomposition χ ψ₁ h₁) (radical_isClosed ψ₁)
      (commonDecomposition χ ψ₂ h₂) (radical_isClosed ψ₂))
    (hδ₂₀ : SquaredModulusCompatibility (commonDecomposition χ ψ₀ h₀) (radical_isClosed ψ₀)
      (commonDecomposition χ ψ₂ h₂) (radical_isClosed ψ₂))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (z : unramifiedCharacters (normCharacters χ))
    (hz₁₀ : z ∈ pairFullDomainRegion χ K hK ψ₀ h₀ ψ₁ A)
    (hz₂₁ : z ∈ pairFullDomainRegion χ K hK ψ₁ h₁ ψ₂ A)
    (hz₂₀ : z ∈ pairFullDomainRegion χ K hK ψ₀ h₀ ψ₂ A)
    (f : UnramifiedLeviInduction (commonDecomposition χ ψ₀ h₀) (radical_isClosed ψ₀)
      (leviNormCharacters χ) (parameterTransport χ z) A),
    pairFamily χ K hK ψ₀ h₀ ψ₂ h₂ hδ₂₀ A ⟨z, hz₂₀⟩ f =
      pairFamily χ K hK ψ₁ h₁ ψ₂ h₂ hδ₂₁ A ⟨z, hz₂₁⟩
        (pairFamily χ K hK ψ₀ h₀ ψ₁ h₁ hδ₁₀ A ⟨z, hz₁₀⟩ f)

end Langlands.Plancherel.DynamicCommonLeviComposition
