import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.Representation.Aubert.General.RationalOppositeParabolic

/-! # The scalar `j` depends only on the opposite pair `{P, P̄}` (target)

Waldspurger 2003, IV.3 (1) (printed pp.285–286): `j_P(π)` does not depend on `P ∈ P(M)`.
For the opposite parabolic `P' = P̄` no composition formula IV.1 (12) is needed:
`j_{P̄}(π) J_{P̄|P}(π) = J_{P̄|P}(π) J_{P|P̄}(π) J_{P̄|P}(π) = J_{P̄|P}(π) j_P(π)`.

The dynamic scalar `conditionalCanonicalRationalScalar` is attached to a cocharacter `χ`,
through `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)`, the radicals `U_G(χ)`, `U_G(χ⁻¹)` and the actual
centralizer scheme `Z_G(χ)`. This module compares it for two cocharacters `χ, ψ` with the same
centralizer subgroup functor, `Z_G(ψ) = Z_G(χ)`: it identifies their Levis (`leviChange`,
`changeRepresentation`) and their centralizer schemes (`parameterChangeIso`) compatibly. It
states (`ConditionalDynamicOppositePairScalarStatement`) that `j_ψ = j_χ` after this
identification whenever the parabolics and radicals of `ψ` are those of `χ`, in the same or in
the exchanged order. The exchanged order is IV.3 (1) for `P' = P̄`; the same order is the
independence of the cocharacter describing `(P, P̄)`. The corollary
`conditionalDynamicOppositeInverseScalar_of_pair` proves the case `ψ = χ⁻¹` from the target.
The target is not proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

/-! ### Two cocharacters with the same centralizer -/

section Change

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hM : Dynamic.centralizer ψ = Dynamic.centralizer χ)

include hM

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- Equal centralizer subgroup functors have the same literal Levi `M(F)`. -/
theorem changeLevi_mem_iff (x : RationalPoint F G.X) : x ∈ levi ψ ↔ x ∈ levi χ := by
  change x ∈ (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) ↔
    x ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))
  rw [hM]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
private theorem changeLevi_refl_mem_iff (x : RationalPoint F G.X) :
    ContinuousMulEquiv.refl (RationalPoint F G.X) x ∈ levi ψ ↔ x ∈ levi χ :=
  changeLevi_mem_iff χ ψ hM x

/-- **The common Levi.** The identity of `G(F)` as a topological group isomorphism from the
Levi `Z_G(χ)(F)` onto the equal Levi `Z_G(ψ)(F)`. -/
def leviChange : levi χ ≃ₜ* levi ψ :=
  QuotientIntegration.subgroupContinuousMulEquiv (ContinuousMulEquiv.refl (RationalPoint F G.X))
    (levi χ) (levi ψ) (changeLevi_refl_mem_iff χ ψ hM)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem leviChange_apply_coe (m : levi χ) :
    (leviChange χ ψ hM m : RationalPoint F G.X) = m :=
  ContinuousMulEquiv.refl_apply (RationalPoint F G.X) (m : RationalPoint F G.X)

/-- **The same representation on the equal Levi**: `A` viewed as a representation of
`Z_G(ψ)(F) = Z_G(χ)(F)`, on the same space. -/
abbrev changeRepresentation (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    SmoothRep.{0, u, uV} ℂ (levi ψ) :=
  SmoothRep.pullback (leviChange χ ψ hM).symm A

/-- **The common parameter group.** The actual centralizer schemes of `χ` and `ψ` represent the
same subgroup functor, so they are identified compatibly with their inclusions in `G`. -/
def parameterChangeIso : parameterScheme χ ≅ parameterScheme ψ :=
  GroupScheme.SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (hM ▸ Dynamic.Affine.isRepresentedBy_centralizerHom ψ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The parameter isomorphism commutes with the inclusions of the two centralizer schemes. -/
theorem parameterChangeIso_hom_comp :
    (parameterChangeIso χ ψ hM).hom ≫ Dynamic.Affine.centralizerHom ψ =
      Dynamic.Affine.centralizerHom χ :=
  GroupScheme.SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- On rational points, the parameter isomorphism followed by the inclusion of `Z_G(ψ)` is the
inclusion of `Z_G(χ)`. -/
theorem parameterChangeIso_hom_points (y : RationalPoint F (parameterScheme χ).X) :
    (y ≫ (parameterChangeIso χ ψ hM).hom.hom.hom) ≫
        (Dynamic.Affine.centralizerHom ψ).hom.hom =
      y ≫ (Dynamic.Affine.centralizerHom χ).hom.hom := by
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun k => y ≫ k.hom.hom) (parameterChangeIso_hom_comp χ ψ hM)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The parameter isomorphism and the Levi identification agree under the identifications
`parameterHomeomorph` of the parameter points with the literal Levis. -/
theorem parameterHomeomorph_parameterChangeIso (y : RationalPoint F (parameterScheme χ).X) :
    parameterHomeomorph ψ
        (GroupScheme.rationalPoints.map (parameterChangeIso χ ψ hM).hom y) =
      leviChange χ ψ hM (parameterHomeomorph χ y) := by
  apply Subtype.ext
  rw [leviChange_apply_coe, parameterHomeomorph_apply_coe,
    parameterHomeomorph_apply_coe, GroupScheme.rationalPoints.map_apply]
  exact parameterChangeIso_hom_points χ ψ hM y

end Change

/-! ### The inverse cocharacter -/

section Inverse

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- The opposite parabolic of `χ⁻¹` is `P_G(χ)`. -/
theorem inverse_oppositeParabolic :
    oppositeParabolic (Dynamic.inverseCocharacter χ) = parabolic χ := by
  rw [oppositeParabolic, Dynamic.inverseCocharacter_inverseCocharacter]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- The opposite radical of `χ⁻¹` is `U_G(χ)`. -/
theorem inverse_oppositeRadical :
    oppositeRadical (Dynamic.inverseCocharacter χ) = radical χ := by
  rw [oppositeRadical, Dynamic.inverseCocharacter_inverseCocharacter]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- `G = P K` gives the Iwasawa decomposition for the opposite parabolic of `χ⁻¹`. -/
theorem inverse_oppositeParabolic_mul_compact (K : OpenSubgroup (RationalPoint F G.X))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (x : RationalPoint F G.X) :
    ∃ p : oppositeParabolic (Dynamic.inverseCocharacter χ), ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X) := by
  obtain ⟨p, k, h⟩ := hPK x
  have hp : (p : RationalPoint F G.X) ∈ oppositeParabolic (Dynamic.inverseCocharacter χ) := by
    rw [inverse_oppositeParabolic]
    exact p.2
  exact ⟨⟨p, hp⟩, k, h⟩

end Inverse

/-! ### The target -/

set_option hygiene false in
local notation "Aψ" => (changeRepresentation χ ψ hM A)

/-- **Target (Waldspurger IV.3 (1) for the pair `{P, P̄}`, transport form).** Let `χ, ψ` be
cocharacters of a connected reductive `G` with the same centralizer `M = Z_G(χ) = Z_G(ψ)`, as
subgroup functors. Suppose that the parabolics and radicals of `ψ` are those of `χ`, either in
the same order (`P_G(ψ) = P`, `U_G(ψ) = U`, `P_G(ψ⁻¹) = P̄`, `U_G(ψ⁻¹) = Ū`) or in the exchanged
order (`P_G(ψ) = P̄`, `U_G(ψ) = Ū`, `P_G(ψ⁻¹) = P`, `U_G(ψ⁻¹) = U`), as subgroups of `G(F)`. Let
`K` be a compact open subgroup with `G = P K = P̄ K`; the two decompositions for `ψ` are taken as
given proofs. Let `A` be a smooth representation of `M(F)` and `Aψ` the same representation of
`Z_G(ψ)(F) = M(F)`. Take conditional data of the canonical scalar `j_P` of `J_{P|P̄} J_{P̄|P}` for
`A` and, independently, conditional data of `j_{P_G(ψ)}` for `Aψ`. Then the scalar for `ψ` is the
scalar for `χ` transported along the identification `Z_G(χ) ≅ Z_G(ψ)` of the actual centralizer
schemes over `G`. In the exchanged order this is `j_{P̄}(π) = j_P(π)`. -/
def ConditionalDynamicOppositePairScalarStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hM : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (_hpair : (parabolic ψ = parabolic χ ∧ radical ψ = radical χ ∧
        oppositeParabolic ψ = oppositeParabolic χ ∧ oppositeRadical ψ = oppositeRadical χ) ∨
      (parabolic ψ = oppositeParabolic χ ∧ radical ψ = oppositeRadical χ ∧
        oppositeParabolic ψ = parabolic χ ∧ oppositeRadical ψ = radical χ))
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hPK' : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic ψ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK' : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic ψ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (_hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (p' : ForwardContinuation ψ hRefl hCST hG K hK hPK' hOppK' Aψ)
    (q' : ReverseContinuation ψ hRefl hCST hG K hK hPK' hOppK' Aψ)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters ψ))}
    (_hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion ψ K hK Aψ)
    (_hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion ψ K hK Aψ)
    {D' : Set (unramifiedCharacters (normCharacters ψ))}
    (_hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition ψ) (radical_isClosed ψ)
        (leviNormCharacters ψ) (parameterTransport ψ z) Aψ).IsIrreducible),
    conditionalCanonicalRationalScalar ψ hRefl hCST hG K hK hPK' hOppK' Aψ
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous ψ) (parameterScheme_isConnectedReductive ψ hG)
        (parameterChangeIso χ ψ hM)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)

set_option hygiene false in
local notation "χi" => (Dynamic.inverseCocharacter χ)
set_option hygiene false in
local notation "hMi" => (Dynamic.centralizer_inverseCocharacter χ)
set_option hygiene false in
local notation "hOppKi" => (inverse_oppositeParabolic_mul_compact χ K hPK)
set_option hygiene false in
local notation "Ai" => (changeRepresentation χ χi hMi A)

/-- **`j_{P̄} = j_P` for the inverse cocharacter.** For `ψ = χ⁻¹`, with `P_G(χ⁻¹) = P̄`,
`P_G((χ⁻¹)⁻¹) = P` and the decompositions `G = P̄ K`, `G = P K` of `χ`, the target gives that
the canonical scalar of `χ⁻¹` for `A` (on the equal Levi `Z_G(χ⁻¹)(F) = M(F)`) is the canonical
scalar of `χ` transported along `Z_G(χ) ≅ Z_G(χ⁻¹)`. -/
theorem conditionalDynamicOppositeInverseScalar_of_pair
    (hpair : ConditionalDynamicOppositePairScalarStatement.{u, uV})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (p' : ForwardContinuation χi hRefl hCST hG K hK hOppK hOppKi Ai)
    (q' : ReverseContinuation χi hRefl hCST hG K hK hOppK hOppKi Ai)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χi))}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χi K hK Ai)
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χi K hK Ai)
    {D' : Set (unramifiedCharacters (normCharacters χi))}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χi) (radical_isClosed χi)
        (leviNormCharacters χi) (parameterTransport χi z) Ai).IsIrreducible) :
    conditionalCanonicalRationalScalar χi hRefl hCST hG K hK hOppK hOppKi Ai
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χi) (parameterScheme_isConnectedReductive χi hG)
        (parameterChangeIso χ χi hMi)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) :=
  hpair χ χi hRefl hCST hG hMi
    (Or.inr ⟨rfl, rfl, inverse_oppositeParabolic χ, inverse_oppositeRadical χ⟩)
    K hK hPK hOppK hOppK hOppKi A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi p' q' hDForward' hneForward' hDForwardΩ'
    hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'

end Langlands.Plancherel
