import Langlands.Representation.Plancherel.DynamicOppositePairScalar
import Langlands.Representation.Plancherel.CommonLeviCompactSplitting

/-! # The scalar `j` does not depend on `P ∈ P(M)` (target)

Waldspurger 2003, IV.3 (1) (printed pp.285–286): `j_P(π)` does not depend on `P ∈ P(M)`. The
proof starts from `j_{P'}(π) J_{P'|P}(π) = J_{P'|P̄'}(π) J_{P̄'|P'}(π) J_{P'|P}(π)` and uses the
composition formula IV.1 (12) four times.

The dynamic scalar `conditionalCanonicalRationalScalar` is attached to a cocharacter `χ`, through
`P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and the actual centralizer scheme `Z_G(χ)`, with radical measures
normalized by one compact open subgroup `K`. An element `P'` of `P(M)` is `P_G(ψ)` for a
cocharacter `ψ` with the same centralizer subgroup functor, `Z_G(ψ) = Z_G(χ)`. The target
`ConditionalDynamicCommonLeviScalarStatement` states that `j_ψ = j_χ` after the identification of
Levis and centralizer schemes of `DynamicOppositePairScalar`, for one `K` that has the four
compact-parabolic factorizations `G = Q K`, `Q ∈ {P, P̄, P', P̄'}`, and the four splittings of
Worker 200's `CommonLeviSplitting.IsCommonLeviSplitting K χ ψ`.

The splittings are those of the consecutive pairs in the four instances of IV.1 (12) of the
proof. `isCommonLeviSplitting_of_pair` proves them for every `K` when the radicals of `ψ` are
those of `χ` in the same or in the exchanged order; `conditionalDynamicOppositePairScalar_of_commonLevi`
derives the published opposite-pair target `ConditionalDynamicOppositePairScalarStatement` from
the target of this module. The target is not proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open StandardIntertwining

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

/-! ### Splittings for the parabolics of one opposite pair -/

section Splitting

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- If `U(m) = U(t)`, every compact open subgroup splits `U(m)` along `t`, with trivial first
factor. -/
theorem splitsAlong_of_radical_eq {t m : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (Q : OpenSubgroup (RationalPoint F G.X)) (h : radical m = radical t) :
    CommonLeviSplitting.SplitsAlong Q t m := by
  unfold CommonLeviSplitting.SplitsAlong HasCompactOpenProduct
  intro g hg hgQ
  have hgt : g ∈ radical t := h ▸ hg
  exact ⟨1, Subgroup.mem_inf.mpr ⟨one_mem _, one_mem _⟩, one_mem Q, g,
    Subgroup.mem_inf.mpr ⟨hg, hgt⟩, hgQ, (one_mul g).symm⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- If `U(m) = U(t⁻¹)`, every compact open subgroup splits `U(m)` along `t`, with trivial second
factor. -/
theorem splitsAlong_of_radical_eq_opposite {t m : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (Q : OpenSubgroup (RationalPoint F G.X)) (h : radical m = oppositeRadical t) :
    CommonLeviSplitting.SplitsAlong Q t m := by
  unfold CommonLeviSplitting.SplitsAlong HasCompactOpenProduct
  intro g hg hgQ
  have hgt : g ∈ oppositeRadical t := h ▸ hg
  exact ⟨g, Subgroup.mem_inf.mpr ⟨hgt, hg⟩, hgQ, 1,
    Subgroup.mem_inf.mpr ⟨one_mem _, one_mem _⟩, one_mem Q, (mul_one g).symm⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] in
/-- **Common-Levi splitting for one opposite pair.** If the radicals of `ψ` are those of `χ`, in
the same order (`U_G(ψ) = U`, `U_G(ψ⁻¹) = Ū`) or in the exchanged order (`U_G(ψ) = Ū`,
`U_G(ψ⁻¹) = U`), then every compact open subgroup has the common-Levi splitting for `χ` and `ψ`:
each of the four products has one trivial factor. -/
theorem isCommonLeviSplitting_of_pair (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (Q : OpenSubgroup (RationalPoint F G.X))
    (hpair : (radical ψ = radical χ ∧ oppositeRadical ψ = oppositeRadical χ) ∨
      (radical ψ = oppositeRadical χ ∧ oppositeRadical ψ = radical χ)) :
    CommonLeviSplitting.IsCommonLeviSplitting Q χ ψ := by
  rcases hpair with ⟨hU, hŪ⟩ | ⟨hU, hŪ⟩
  · exact ⟨splitsAlong_of_radical_eq Q hU, splitsAlong_of_radical_eq_opposite Q hŪ,
      splitsAlong_of_radical_eq Q hU.symm, splitsAlong_of_radical_eq_opposite Q hŪ.symm⟩
  · exact ⟨splitsAlong_of_radical_eq_opposite Q hU, splitsAlong_of_radical_eq Q hŪ,
      splitsAlong_of_radical_eq_opposite Q hŪ.symm, splitsAlong_of_radical_eq Q hU.symm⟩

end Splitting

/-! ### The target -/

set_option hygiene false in
local notation "Aψ" => (changeRepresentation χ ψ hM A)

/-- **Target (Waldspurger IV.3 (1), transport form).** Let `χ, ψ` be cocharacters of a connected
reductive `G` with the same centralizer `M = Z_G(χ) = Z_G(ψ)`, as subgroup functors, so that
`P = P_G(χ)` and `P' = P_G(ψ)` both lie in `P(M)`. Let `K` be a compact open subgroup with the
four compact-parabolic factorizations `G = P K = P̄ K = P' K = P̄' K` (the two for `ψ` are the
given proofs `hPK'`, `hOppK'`) and with the common-Levi splitting
`CommonLeviSplitting.IsCommonLeviSplitting K χ ψ`: `K ∩ U_G(ψ^±)` splits along `χ` and
`K ∩ U_G(χ^±)` splits along `ψ`. The instance `[Smooth G.X.hom]`, which this splitting requires, is
the field `smooth` of `IsConnectedReductive G`. Let `A` be a smooth representation of `M(F)` and
`Aψ` the same representation of `Z_G(ψ)(F) = M(F)`. Take conditional data of the canonical scalar
`j_P` of `J_{P|P̄} J_{P̄|P}` for `A` and, independently, conditional data of `j_{P'}` of
`J_{P'|P̄'} J_{P̄'|P'}` for `Aψ`. Then the scalar for `ψ` is the scalar for `χ` transported along
the identification `Z_G(χ) ≅ Z_G(ψ)` of the actual centralizer schemes over `G`. -/
def ConditionalDynamicCommonLeviScalarStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth G.X.hom]
    (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (hM : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (_hs : CommonLeviSplitting.IsCommonLeviSplitting K χ ψ)
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

/-- **The opposite-pair target is a special case.** The target of this module implies the
published `ConditionalDynamicOppositePairScalarStatement`: when the radicals of `ψ` are those of
`χ` in the same or the exchanged order, `isCommonLeviSplitting_of_pair` supplies the splitting
premise for the given `K`, with the instance `[Smooth G.X.hom]` taken from `hG`. -/
theorem conditionalDynamicOppositePairScalar_of_commonLevi
    (h : ConditionalDynamicCommonLeviScalarStatement.{u, uV}) :
    ConditionalDynamicOppositePairScalarStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ ψ hRefl hCST hG hM hpair K hK hPK hOppK hPK' hOppK' A p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ D hD hne hi
    p' q' DForward' DReverse' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse'
    hDReverseΩ' D' hD' hne' hi'
  have : Smooth G.X.hom := hG.smooth
  have hs : CommonLeviSplitting.IsCommonLeviSplitting K χ ψ :=
    isCommonLeviSplitting_of_pair χ ψ K
      (hpair.imp (fun hp => ⟨hp.2.1, hp.2.2.2⟩) (fun hp => ⟨hp.2.1, hp.2.2.2⟩))
  exact h χ ψ hRefl hCST hG hM K hK hs hPK hOppK hPK' hOppK' A p q hDForward hneForward
    hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi p' q' hDForward' hneForward' hDForwardΩ'
    hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'

end Langlands.Plancherel
