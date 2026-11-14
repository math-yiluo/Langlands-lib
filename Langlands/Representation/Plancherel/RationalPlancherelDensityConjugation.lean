import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.Representation.Plancherel.RationalPlancherelConstantConjugation

/-! # Conjugation invariance of the Plancherel density

Waldspurger 2003, Lemma V.2.1 (printed p.292), third item: `μ(sω) = μ(ω)` for `s ∈ W^G`, where
`μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²` (V.2). This module derives the transport form of this identity
for the Library's density `plancherelDensity` from two inputs:

- the conjugation target `ConditionalDynamicOppositeConjugationScalarStatement` for the
  canonical scalar `j_P` (IV.3 (3) in transport form, module
  `DynamicOppositeConjugationScalar`), which is assumed;
- the conjugation invariance of the density constant `∏_α γ(M_α|M)²`
  (`plancherelDensityConstant_eq_of_conjugation`, module
  `RationalPlancherelConstantConjugation`), which is proved.

For a torus `i : T → G`, a cocharacter `ζ` of `T` and `g ∈ G(F)`, the conjugate torus is
`innerConjugate i g = i ≫ Int(g)`, whose cocharacter `ζ ≫ (i ≫ Int(g))` equals
`(ζ ≫ i) ≫ Int(g)` only up to associativity of composition.
`conditionalDynamicOppositeConjugationScalar_of_heq` restates the conjugation target for
conjugate data given up to equality, so that it applies to the cocharacter
`ζ ≫ (i ≫ Int(g))`. The module states the target `PlancherelDensityConjugationStatement`: the
density for `(innerConjugate i g, K₁, gA)`, with `K₁ = gKg⁻¹` (in particular `K₁ = K` when
`g ∈ K`), is the density for `(i, K, A)` transported along `Int(g)`. It proves that the
conjugation target for `j_P` implies it (`plancherelDensity_conjugation_of_conjugationScalar`
and `plancherelDensityConjugation_of_conjugationScalar`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal
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

/-- **The conjugation target with the conjugate data given up to equality.** Assume
`ConditionalDynamicOppositeConjugationScalarStatement`. Its conclusion holds for conjugate data
formed with any cocharacter `χ'` equal to `gχg⁻¹ = χ ≫ Int(g)`, any representation `A'`
(heterogeneously) equal to `gA`, any isomorphism `e` (heterogeneously) equal to
`parameterConjugationIso χ g`, and any compact open `K₁` equal to `gKg⁻¹`. This form lets
the target be applied when `gχg⁻¹` is written differently, for instance `ζ ≫ (i ≫ Int(g))`
for a cocharacter `ζ` of a torus `i`. -/
theorem conditionalDynamicOppositeConjugationScalar_of_heq
    (hconj : ConditionalDynamicOppositeConjugationScalarStatement.{u, uV})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (g : RationalPoint F G.X)
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
    (χ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hχ : χ ≫ (G.innerIso g).hom = χ')
    (A' : SmoothRep.{0, u, uV} ℂ (levi χ')) (hA : HEq (conjugateRepresentation χ g A) A')
    (e : parameterScheme χ ≅ parameterScheme χ') (he : HEq (parameterConjugationIso χ g) e)
    (K₁ : OpenSubgroup (RationalPoint F G.X))
    (hK₁ : RationalDynamicSource.conjugateCompact g K = K₁)
    (hK₁c : IsCompact (K₁ : Set (RationalPoint F G.X)))
    (hPK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χ', ∃ k : K₁, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ', ∃ k : K₁,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (p' : ForwardContinuation χ' hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ A')
    (q' : ReverseContinuation χ' hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ A')
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χ'))}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χ' K₁ hK₁c A')
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χ' K₁ hK₁c A')
    {D' : Set (unramifiedCharacters (normCharacters χ'))}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χ') (radical_isClosed χ')
        (leviNormCharacters χ') (parameterTransport χ' z) A').IsIrreducible) :
    conditionalCanonicalRationalScalar χ' hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ A'
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χ') (parameterScheme_isConnectedReductive χ' hG) e
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  subst hχ
  obtain rfl := eq_of_heq hA
  obtain rfl := eq_of_heq he
  exact conditionalDynamicOppositeConjugationScalar_of_eq hconj χ hRefl hCST hG g K hK hPK hOppK
    A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    K₁ hK₁ hK₁c hPK₁ hOppK₁ p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse'
    hDReverseΩ' hD' hne' hi'

end Langlands.Plancherel

namespace Langlands.Plancherel.RationalPlancherelDensity

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

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

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T) (hG : IsConnectedReductive G) (g : RationalPoint F G.X)

set_option hygiene false in
local notation "χ" => (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "ig" => (innerConjugate i g)
set_option hygiene false in
local notation "χg" => (CommGroupScheme.groupHom ζ ≫ innerConjugate i g)
set_option hygiene false in
local notation "Ag" => (conjugateRepresentation (CommGroupScheme.groupHom ζ ≫ i) g A)

/-- The transport of rational functions along the conjugation `Int(g)` fixes the complex
constants of `RationalPlancherelDensity`. -/
theorem fieldConstant_conjugation (c : ℂ) :
    rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χg) (parameterScheme_isConnectedReductive χg hG)
        (parameterConjugationIso χ g) (fieldConstant i ζ hG c) =
      fieldConstant ig ζ hG c :=
  rationalUnramifiedFunctionFieldEquiv_constant _ _ _ _ _ c

/-- **Conjugation invariance of the density (transport form of Lemma V.2.1, third item).**
Assume the conjugation target `ConditionalDynamicOppositeConjugationScalarStatement`. Let
`χ = ζ ≫ i`, `g ∈ G(F)`, and let `K₁` be a compact open subgroup equal to `gKg⁻¹`, for example
`gKg⁻¹` itself (`hK₁ = rfl`) or `K` when `g ∈ K`
(`RationalDynamicSource.conjugateCompact_eq_self`). Then the density for the conjugate torus
`i ≫ Int(g)`, the compact `K₁` and the conjugate representation `gA` is the density for `i`,
`K` and `A` transported along `Int(g)`: `μ(gA ⊗ (z ∘ Int(g)⁻¹)) = μ(A ⊗ z)`. -/
theorem plancherelDensity_conjugation_of_conjugationScalar
    (hconj : ConditionalDynamicOppositeConjugationScalarStatement.{u, uV})
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
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
    (K₁ : OpenSubgroup (RationalPoint F G.X)) (hK₁ : conjugateCompact g K = K₁)
    (hK₁c : IsCompact (K₁ : Set (RationalPoint F G.X)))
    (hPK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χg, ∃ k : K₁, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χg, ∃ k : K₁,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (p' : ForwardContinuation χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag)
    (q' : ReverseContinuation χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χg))}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χg K₁ hK₁c Ag)
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χg K₁ hK₁c Ag)
    {D' : Set (unramifiedCharacters (normCharacters χg))}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
        (leviNormCharacters χg) (parameterTransport χg z) Ag).IsIrreducible) :
    plancherelDensity ig ζ hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag p' q' hneForward' hDForwardΩ'
        hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χg) (parameterScheme_isConnectedReductive χg hG)
        (parameterConjugationIso χ g)
        (plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
          hneReverse hDReverseΩ hne hi) := by
  have hscalar := conditionalDynamicOppositeConjugationScalar_of_heq hconj χ hRefl hCST hG g K hK
    hPK hOppK A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    χg (Category.assoc _ _ _) Ag HEq.rfl (parameterConjugationIso χ g) HEq.rfl
    K₁ hK₁ hK₁c hPK₁ hOppK₁ p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse'
    hDReverseΩ' hD' hne' hi'
  have hconst : plancherelDensityConstant ig ζ K₁ hK₁c = plancherelDensityConstant i ζ K hK :=
    plancherelDensityConstant_eq_of_conjugation i ζ g K K₁ hK hK₁c
      (fun x => hK₁ ▸ mem_conjugateCompact g x K)
  refine (congrArg
    (fun f => fieldConstant ig ζ hG (plancherelDensityConstant ig ζ K₁ hK₁c : ℂ) * f⁻¹)
    hscalar).trans ?_
  rw [hconst, plancherelDensity_def, map_mul, map_inv₀, fieldConstant_conjugation]

/-- **Target (Waldspurger V.2.1, third item, transport form).** Let `T → G` be a torus `i`
with a cocharacter `ζ`, `χ = ζ ≫ i`, `P = P_G(χ)`, `M = Z_G(χ)`, `K` a compact open subgroup with
`G = P K = P̄ K`, `A` a smooth representation of `M(F)` and `g ∈ G(F)`. Take conditional data of
the density `plancherelDensity` for `(i, ζ, K, A)` and, independently, for the conjugate torus
`innerConjugate i g = i ≫ Int(g)`, a compact open `K₁` equal to `gKg⁻¹` (for example `K` when
`g ∈ K`) and the conjugate representation `gA`. Then the density for the conjugate data is the
density for the original data transported along `Int(g)` on the parameter group:
`μ(gA ⊗ (z ∘ Int(g)⁻¹)) = μ(A ⊗ z)` as rational functions of the unramified character `z`. -/
def PlancherelDensityConjugationStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (g : RationalPoint F G.X)
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
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (_hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (K₁ : OpenSubgroup (RationalPoint F G.X)) (_hK₁ : conjugateCompact g K = K₁)
    (hK₁c : IsCompact (K₁ : Set (RationalPoint F G.X)))
    (hPK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : parabolic χg, ∃ k : K₁, x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK₁ : ∀ x : RationalPoint F G.X,
      ∃ p : oppositeParabolic χg, ∃ k : K₁,
        x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (p' : ForwardContinuation χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag)
    (q' : ReverseContinuation χg hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χg))}
    (_hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χg K₁ hK₁c Ag)
    (_hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χg K₁ hK₁c Ag)
    {D' : Set (unramifiedCharacters (normCharacters χg))}
    (_hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
        (leviNormCharacters χg) (parameterTransport χg z) Ag).IsIrreducible),
    plancherelDensity ig ζ hRefl hCST hG K₁ hK₁c hPK₁ hOppK₁ Ag p' q' hneForward' hDForwardΩ'
        hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldEquiv
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (parameterProjection_continuous χg) (parameterScheme_isConnectedReductive χg hG)
        (parameterConjugationIso χ g)
        (plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
          hneReverse hDReverseΩ hne hi)

/-- **The conjugation target for `j_P` gives the target for the density.** -/
theorem plancherelDensityConjugation_of_conjugationScalar
    (hconj : ConditionalDynamicOppositeConjugationScalarStatement.{u, uV}) :
    PlancherelDensityConjugationStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ T i ζ hRefl hCST hG g K hK hPK hOppK A p q DForward DReverse hDForward
    hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ D hD hne hi K₁ hK₁ hK₁c hPK₁ hOppK₁
    p' q' DForward' DReverse' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse'
    hDReverseΩ' D' hD' hne' hi'
  exact plancherelDensity_conjugation_of_conjugationScalar i ζ hG g hconj hRefl hCST K hK hPK
    hOppK A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    K₁ hK₁ hK₁c hPK₁ hOppK₁ p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse'
    hDReverseΩ' hD' hne' hi'

end Langlands.Plancherel.RationalPlancherelDensity
