import Langlands.Representation.Plancherel.RationalPlancherelDensity
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement
import Langlands.Representation.Plancherel.UnramifiedScalarTranslation
import Langlands.Representation.Plancherel.CompactNormalizedInductionDuality

/-! # Contragredient invariance of the scalar `j` (targets)

Waldspurger 2003, IV.3 (2) (printed p.286): `j(π) = j(π̌)`, deduced from the adjunction
IV.1 (11) (printed p.283) `⟨J_{P'|P}(π) f, f̌'⟩ = ⟨f, J_{P|P'}(π̌) f̌'⟩`. Lemma V.2.1
(printed p.292) uses it for `μ(ω̌) = μ(ω)`. Since `(π ⊗ χ)ˇ = π̌ ⊗ χ⁻¹`, on the unramified
parameter of the orbit the identity reads `j(Ǎ ⊗ z⁻¹) = j(A ⊗ z)`.

This module constructs inversion `b(χ) ↦ b(χ⁻¹)` of the parameter on the regular functions
(`unramifiedRegularInversion`) and on the field of rational functions
(`rationalUnramifiedFunctionFieldInversion`), with its transfer of regularity and of
nonnegative values from `z⁻¹` to `z`. It defines the compact-picture duality pairing
`⟨φ, φ̌⟩ = ∫_K φ̌(k)(φ(k)) dk` of sections for `A` and for its smooth contragredient `Ǎ`.
It states two targets for the Library's actual opposite standard integrals: the adjunction
IV.1 (11) on the convergence domains (`ConditionalDynamicOppositeDualAdjunctionStatement`)
and IV.3 (2) for the canonical scalar `conditionalCanonicalRationalScalar`
(`ConditionalDynamicOppositeContragredientScalarStatement`). It proves that the second target
gives the same invariance for the density `plancherelDensity`. Neither target is proved here.
-/

noncomputable section

universe u uG uI uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped NNReal CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Inversion of the unramified parameter -/

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- The inverse unramified character takes the value `χ(g⁻¹) = χ(g)⁻¹` at `g`. -/
theorem unramifiedCharacters_inv_val_apply (χ : unramifiedCharacters ν) (g : G) :
    (((χ⁻¹ : unramifiedCharacters ν).val g : ℂˣ) : ℂ) = ((χ.val g⁻¹ : ℂˣ) : ℂ) := by
  rw [map_inv]
  rfl

/-- The inverse of a unitary unramified character is unitary. -/
theorem inv_mem_unitaryUnramifiedCharacters {χ : unramifiedCharacters ν}
    (hχ : χ.val ∈ unitaryUnramifiedCharacters ν) :
    (χ⁻¹ : unramifiedCharacters ν).val ∈ unitaryUnramifiedCharacters ν :=
  (unitaryUnramifiedCharacters ν).inv_mem hχ

private def inversionFunctionAlgEquiv :
    (unramifiedCharacters ν → ℂ) ≃ₐ[ℂ] (unramifiedCharacters ν → ℂ) where
  toFun f χ := f χ⁻¹
  invFun f χ := f χ⁻¹
  left_inv f := by funext χ; simp
  right_inv f := by funext χ; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem inversionFunctionAlgEquiv_evaluation (g : G) :
    inversionFunctionAlgEquiv ν (unramifiedEvaluation ν g) = unramifiedEvaluation ν g⁻¹ := by
  funext χ
  exact unramifiedCharacters_inv_val_apply ν χ g

private theorem inversionFunctionAlgEquiv_mem (b : unramifiedRegularFunctions ν) :
    inversionFunctionAlgEquiv ν b.val ∈ unramifiedRegularFunctions ν := by
  change b.val ∈ (unramifiedRegularFunctions ν).comap (inversionFunctionAlgEquiv ν).toAlgHom
  refine Algebra.adjoin_le (S := (unramifiedRegularFunctions ν).comap
    (inversionFunctionAlgEquiv ν).toAlgHom) ?_ b.property
  rintro _ ⟨g, rfl⟩
  change inversionFunctionAlgEquiv ν (unramifiedEvaluation ν g) ∈ unramifiedRegularFunctions ν
  rw [inversionFunctionAlgEquiv_evaluation]
  exact (unramifiedEvaluationRegular ν g⁻¹).property

/-- Pullback `b(χ) ↦ b(χ⁻¹)` along inversion of the parameter preserves the actual
evaluation-generated regular algebra: it sends the evaluation at `g` to the evaluation at
`g⁻¹`. It is an involution. -/
def unramifiedRegularInversion :
    unramifiedRegularFunctions ν ≃ₐ[ℂ] unramifiedRegularFunctions ν where
  toFun b := ⟨inversionFunctionAlgEquiv ν b.val, inversionFunctionAlgEquiv_mem ν b⟩
  invFun b := ⟨inversionFunctionAlgEquiv ν b.val, inversionFunctionAlgEquiv_mem ν b⟩
  left_inv b := by
    apply Subtype.ext
    exact (inversionFunctionAlgEquiv ν).left_inv b.val
  right_inv b := by
    apply Subtype.ext
    exact (inversionFunctionAlgEquiv ν).right_inv b.val
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Values of the inverted function: `(σ b)(χ) = b(χ⁻¹)`. -/
@[simp]
theorem unramifiedRegularInversion_apply (b : unramifiedRegularFunctions ν)
    (χ : unramifiedCharacters ν) :
    (unramifiedRegularInversion ν b).val χ = b.val χ⁻¹ := rfl

/-- The inversion is its own inverse. -/
@[simp]
theorem unramifiedRegularInversion_symm :
    (unramifiedRegularInversion ν).symm = unramifiedRegularInversion ν := rfl

/-- The evaluation at `g` is sent to the evaluation at `g⁻¹`. -/
@[simp]
theorem unramifiedRegularInversion_evaluation (g : G) :
    unramifiedRegularInversion ν (unramifiedEvaluationRegular ν g) =
      unramifiedEvaluationRegular ν g⁻¹ := by
  apply Subtype.ext
  exact inversionFunctionAlgEquiv_evaluation ν g

/-- Applying the inversion twice gives back the function. -/
theorem unramifiedRegularInversion_unramifiedRegularInversion
    (b : unramifiedRegularFunctions ν) :
    unramifiedRegularInversion ν (unramifiedRegularInversion ν b) = b :=
  (unramifiedRegularInversion ν).apply_symm_apply b

end Generic

/-! ### Inversion on the actual function field -/

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "XG" => unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "FG" => rationalUnramifiedFunctionField G hp hG

/-- The ring automorphism `f(χ) ↦ f(χ⁻¹)` of the actual field of rational functions on the
unramified characters, extending `unramifiedRegularInversion` to fractions. -/
def rationalUnramifiedFunctionFieldInversion : FG ≃+* FG :=
  IsFractionRing.ringEquivOfRingEquiv
    (unramifiedRegularInversion (fun ψ => (rationalNormCharacters G ψ).toMul)).toRingEquiv

/-- On regular functions the field inversion is `unramifiedRegularInversion`. -/
@[simp]
theorem rationalUnramifiedFunctionFieldInversion_algebraMap (b : RG) :
    rationalUnramifiedFunctionFieldInversion G hp hG (algebraMap RG FG b) =
      algebraMap RG FG
        (unramifiedRegularInversion (fun ψ => (rationalNormCharacters G ψ).toMul) b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b

/-- Complex constants are fixed. -/
theorem rationalUnramifiedFunctionFieldInversion_constant (c : ℂ) :
    rationalUnramifiedFunctionFieldInversion G hp hG (algebraMap RG FG (algebraMap ℂ RG c)) =
      algebraMap RG FG (algebraMap ℂ RG c) := by
  rw [rationalUnramifiedFunctionFieldInversion_algebraMap, AlgEquiv.commutes]

/-- Inversion of the parameter is an involution of the function field. -/
theorem rationalUnramifiedFunctionFieldInversion_involutive (f : FG) :
    rationalUnramifiedFunctionFieldInversion G hp hG
      (rationalUnramifiedFunctionFieldInversion G hp hG f) = f := by
  obtain ⟨m, n, hn, rfl⟩ := IsFractionRing.div_surjective (A := RG) f
  simp only [map_div₀, rationalUnramifiedFunctionFieldInversion_algebraMap,
    unramifiedRegularInversion_unramifiedRegularInversion]

set_option hygiene false in
local notation "σG" => unramifiedRegularInversion (fun ψ => (rationalNormCharacters G ψ).toMul)

/-- Evaluating the inverted regular function at `z⁻¹` gives the original value at `z`. -/
theorem unramifiedRegularInversion_val_inv (b : RG) (z : XG) :
    (σG b).val z⁻¹ = b.val z := by
  rw [unramifiedRegularInversion_apply, inv_inv]

private theorem inversion_presentation {f : FG} {m n : RG}
    (hf : rationalUnramifiedFunctionFieldInversion G hp hG f =
      algebraMap RG FG m / algebraMap RG FG n) :
    f = algebraMap RG FG (σG m) / algebraMap RG FG (σG n) := by
  have h := congrArg (rationalUnramifiedFunctionFieldInversion G hp hG) hf
  rw [rationalUnramifiedFunctionFieldInversion_involutive, map_div₀,
    rationalUnramifiedFunctionFieldInversion_algebraMap,
    rationalUnramifiedFunctionFieldInversion_algebraMap] at h
  exact h

private theorem inversion_presentation' {f : FG} {m n : RG}
    (hf : f = algebraMap RG FG m / algebraMap RG FG n) :
    rationalUnramifiedFunctionFieldInversion G hp hG f =
      algebraMap RG FG (σG m) / algebraMap RG FG (σG n) := by
  rw [hf, map_div₀, rationalUnramifiedFunctionFieldInversion_algebraMap,
    rationalUnramifiedFunctionFieldInversion_algebraMap]

/-- A rational function is regular at `z` after inversion exactly when it is regular at
`z⁻¹`. -/
theorem rationalFunctionRegularAt_inversion_iff (f : FG) (z : XG) :
    RationalFunctionRegularAt G hp hG (rationalUnramifiedFunctionFieldInversion G hp hG f) z ↔
      RationalFunctionRegularAt G hp hG f z⁻¹ := by
  constructor
  · intro h
    obtain ⟨m, n, hn, hf⟩ := h
    refine ⟨σG m, σG n, ?_, inversion_presentation G hp hG hf⟩
    rw [unramifiedRegularInversion_val_inv]
    exact hn
  · intro h
    obtain ⟨m, n, hn, hf⟩ := h
    exact ⟨σG m, σG n, hn, inversion_presentation' G hp hG hf⟩

/-- Regularity with a nonnegative real value transfers in the same way. -/
theorem rationalFunctionNonnegAt_inversion_iff (f : FG) (z : XG) :
    RationalFunctionNonnegAt G hp hG (rationalUnramifiedFunctionFieldInversion G hp hG f) z ↔
      RationalFunctionNonnegAt G hp hG f z⁻¹ := by
  constructor
  · intro h
    obtain ⟨m, n, hn, hf, r, hr, hv⟩ := h
    refine ⟨σG m, σG n, ?_, inversion_presentation G hp hG hf, r, hr, ?_⟩
    · rw [unramifiedRegularInversion_val_inv]
      exact hn
    · rw [unramifiedRegularInversion_val_inv, unramifiedRegularInversion_val_inv]
      exact hv
  · intro h
    obtain ⟨m, n, hn, hf, r, hr, hv⟩ := h
    exact ⟨σG m, σG n, hn, inversion_presentation' G hp hG hf, r, hr, hv⟩

end ActualCharacters

/-! ### The compact-picture duality pairing -/

section Pairing

open Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The bilinear pairing `⟨φ, φ̌⟩ = ∫_K φ̌(k)(φ(k)) dk` of a compact-picture section for `A`
with one for the smooth contragredient `Ǎ`, against the Library's Haar probability
`CompactInduction.measure K hK` on `K`. -/
def compactPictureDualPairing (A : SmoothRep.{0, uG, uV} ℂ M)
    (φ : CompactInductionPicture h K A)
    (φ' : CompactInductionPicture h K A.contragredient) : ℂ :=
  ∫ k : K, smoothDualPairing A.representation
    (Induction.eval (P.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K A.contragredient) φ' k)
    (Induction.eval (P.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K A) φ k) ∂CompactInduction.measure K hK

end Pairing

/-! ### The targets -/

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

/-- The Borel structure on the actual rational points. -/
local instance contragredientScalarPointMeasurable {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    MeasurableSpace (RationalPoint F G.X) :=
  borel _

local instance contragredientScalarPointBorel {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    BorelSpace (RationalPoint F G.X) :=
  ⟨rfl⟩

/-- **Target (the duality adjunction IV.1 (11) on the convergence domains).** Let `χ` be a
cocharacter of `G`, `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`. Let `K` be a compact open
subgroup with `G = P K = P̄ K` whose intersections with `P` and `P̄` factor through `M`, and let
`A` be a smooth representation of `M(F)` with smooth contragredient `Ǎ`. For the pairing
`∫_K φ̌(k)(φ(k)) dk` of compact-picture sections:

* if `z` lies in the full convergence domain of the forward integral `J_{P̄|P}` for `A` and `z⁻¹`
  in that of the reverse integral `J_{P|P̄}` for `Ǎ`, then
  `⟨J_{P̄|P}(A ⊗ z) φ, φ̌⟩ = ⟨φ, J_{P|P̄}(Ǎ ⊗ z⁻¹) φ̌⟩`;
* if `z` lies in the full convergence domain of `J_{P|P̄}` for `A` and `z⁻¹` in that of
  `J_{P̄|P}` for `Ǎ`, then `⟨J_{P|P̄}(A ⊗ z) ψ, ψ̌⟩ = ⟨ψ, J_{P̄|P}(Ǎ ⊗ z⁻¹) ψ̌⟩`. -/
def ConditionalDynamicOppositeDualAdjunctionStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (_hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (_hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)),
    (∀ (z : forwardFullDomainRegion χ K hK A)
      (hz : z.val⁻¹ ∈ reverseFullDomainRegion χ K hK A.contragredient)
      (φ : CompactInductionPicture (decomposition χ) K A)
      (φ' : CompactInductionPicture (oppositeDecomposition χ) K A.contragredient),
      compactPictureDualPairing (oppositeDecomposition χ) K hK A
          (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A z φ) φ' =
        compactPictureDualPairing (decomposition χ) K hK A φ
          (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A.contragredient
            ⟨z.val⁻¹, hz⟩ φ')) ∧
    (∀ (z : reverseFullDomainRegion χ K hK A)
      (hz : z.val⁻¹ ∈ forwardFullDomainRegion χ K hK A.contragredient)
      (ψ : CompactInductionPicture (oppositeDecomposition χ) K A)
      (ψ' : CompactInductionPicture (decomposition χ) K A.contragredient),
      compactPictureDualPairing (decomposition χ) K hK A
          (conditionalReverseCompactFamily χ hRefl hCST hG K hK hPK hOppK A z ψ) ψ' =
        compactPictureDualPairing (oppositeDecomposition χ) K hK A ψ
          (conditionalForwardCompactFamily χ hRefl hCST hG K hK hPK hOppK A.contragredient
            ⟨z.val⁻¹, hz⟩ ψ'))

/-- **Target (Waldspurger IV.3 (2): `j(π̌) = j(π)`).** Let `χ` be a cocharacter of `G`,
`P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`. Let `K` be a compact open subgroup with
`G = P K = P̄ K` whose intersections with `P` and `P̄` factor through `M`, let `A` be a smooth
representation of `M(F)` and `Ǎ` its smooth contragredient. Take conditional data of the
canonical scalar `j_P` of `J_{P|P̄} J_{P̄|P}` for `A` and, independently, for `Ǎ`, and assume
that inversion `z ↦ z⁻¹` maps the open set `DForward` of the data for `A` into the full
convergence domain of `J_{P|P̄}` for `Ǎ`, and the open set `DReverse` into that of `J_{P̄|P}`
for `Ǎ`. Then the scalar for `Ǎ` is the scalar for `A` composed with inversion of the
parameter: `j_P(Ǎ ⊗ z⁻¹) = j_P(A ⊗ z)` as rational functions. -/
def ConditionalDynamicOppositeContragredientScalarStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (_hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (_hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
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
    (p' : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A.contragredient)
    (q' : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A.contragredient)
    {DForward' DReverse' : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χ K hK A.contragredient)
    (_hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χ K hK A.contragredient)
    {D' : Set (unramifiedCharacters (normCharacters χ))}
    (_hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A.contragredient).IsIrreducible)
    (_hinvForward : ∀ z ∈ DForward, z⁻¹ ∈ reverseFullDomainRegion χ K hK A.contragredient)
    (_hinvReverse : ∀ z ∈ DReverse, z⁻¹ ∈ forwardFullDomainRegion χ K hK A.contragredient),
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A.contragredient
        p' q' hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldInversion (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)

/-! ### The density `μ` -/

section Density

open RationalPlancherelDensity

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)

/-- Inversion of the parameter fixes the complex constants of `DensityField`. -/
theorem rationalUnramifiedFunctionFieldInversion_fieldConstant (hG : IsConnectedReductive G)
    (c : ℂ) :
    rationalUnramifiedFunctionFieldInversion (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (fieldConstant i ζ hG c) = fieldConstant i ζ hG c :=
  rationalUnramifiedFunctionFieldInversion_constant (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG) c

/-- **Contragredient invariance of the density (from IV.3 (2)).** Assume the target
`ConditionalDynamicOppositeContragredientScalarStatement`. For `χ = ζ ≫ i`, conditional data of
the density `μ = j_P⁻¹ ∏_α γ(M_α|M)²` for `A` and for its contragredient `Ǎ`, with the
inversion hypotheses of the target, the density for `Ǎ` is the density for `A` composed with
inversion of the parameter: `μ(Ǎ ⊗ z⁻¹) = μ(A ⊗ z)`. -/
theorem plancherelDensity_contragredient_of_contragredientScalar
    (H : ConditionalDynamicOppositeContragredientScalarStatement.{u, uV})
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ))
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters νL)}
    (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters νL)}
    (hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (p' : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A.contragredient)
    (q' : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A.contragredient)
    {DForward' DReverse' : Set (unramifiedCharacters νL)}
    (hDForward' : IsOpen DForward') (hneForward' : DForward'.Nonempty)
    (hDForwardΩ' : DForward' ⊆ forwardFullDomainRegion χ K hK A.contragredient)
    (hDReverse' : IsOpen DReverse') (hneReverse' : DReverse'.Nonempty)
    (hDReverseΩ' : DReverse' ⊆ reverseFullDomainRegion χ K hK A.contragredient)
    {D' : Set (unramifiedCharacters νL)}
    (hD' : IsOpen D') (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A.contragredient).IsIrreducible)
    (hinvForward : ∀ z ∈ DForward, z⁻¹ ∈ reverseFullDomainRegion χ K hK A.contragredient)
    (hinvReverse : ∀ z ∈ DReverse, z⁻¹ ∈ forwardFullDomainRegion χ K hK A.contragredient) :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A.contragredient p' q'
        hneForward' hDForwardΩ' hneReverse' hDReverseΩ' hne' hi' =
      rationalUnramifiedFunctionFieldInversion (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
        (plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q
          hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) := by
  have hj := H χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
    p' q' hDForward' hneForward' hDForwardΩ' hDReverse' hneReverse' hDReverseΩ' hD' hne' hi'
    hinvForward hinvReverse
  rw [plancherelDensity_def, plancherelDensity_def, hj, map_mul, map_inv₀,
    rationalUnramifiedFunctionFieldInversion_fieldConstant]

end Density

end Langlands.Plancherel
