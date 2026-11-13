import Langlands.Representation.Plancherel.RationalPlancherelDensity
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement

/-! # Regularity and nonnegativity of `μ` on the unitary orbit (Lemma V.2.1)

Waldspurger 2003, Lemma V.2.1 (printed p.292): `μ` is a rational function regular on `O`, and
`μ(ω) ≥ 0` for every `ω ∈ O`. This module states these two claims for the density
`plancherelDensity = ∏_α γ(M_α|M)² · j_P⁻¹`, together with `μ ≠ 0` when the product of the
`γ(M_α|M)` is finite, and derives them from the target
`ConditionalDynamicOppositeUnitaryScalarStatement` (IV.3(6) with positivity). Neither target is
proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Nonnegative constants times nonnegative functions -/

section Regular

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

/-- A nonnegative real constant times a function that is regular and nonnegative at `z` is again
regular and nonnegative at `z`. -/
theorem RationalFunctionNonnegAt.const_mul {f : rationalUnramifiedFunctionField G hp hG}
    {z : XG} (h : RationalFunctionNonnegAt G hp hG f z) {c : ℝ} (hc : 0 ≤ c) :
    RationalFunctionNonnegAt G hp hG
      (algebraMap RG (rationalUnramifiedFunctionField G hp hG) (algebraMap ℂ RG (c : ℂ)) * f)
      z :=
  h.elim fun m hm => hm.elim fun n hn => hn.2.2.elim fun r hr =>
    ⟨algebraMap ℂ RG (c : ℂ) * m, n, hn.1, by
      rw [hn.2.1, map_mul, mul_div_assoc], c * r, mul_nonneg hc hr.1, by
      have hval : (algebraMap ℂ RG (c : ℂ) * m).val z = (c : ℂ) * m.val z := by
        simp
      rw [hval, mul_div_assoc, hr.2]
      push_cast
      ring⟩

end Regular

namespace RationalPlancherelDensity

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource

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

/-! ### The target (Lemma V.2.1, first two claims) -/

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i

/-- **Target (Waldspurger, Lemma V.2.1, first two claims).** For `χ = ζ ≫ i`, the data of the
canonical scalar `j_P` and an inducing representation `A` of `M(F)` that is square-integrable
modulo a central subgroup `C` with `M(F) / (M¹ C)` finite, the density
`μ = ∏_α γ(M_α|M)² · j_P⁻¹` is a nonzero rational function when the product of the `γ(M_α|M)` is
finite, and it is regular with a nonnegative real value at every unitary unramified character. -/
def ConditionalPlancherelDensityUnitaryStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
    (ζ : cocharacterLattice T)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
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
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
    [Finite (levi χ ⧸ (commonNormKernel (leviNormCharacters χ) ⊔ C))]
    (_hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM),
    (rankOneGammaProduct i ζ K hK ≠ ⊤ →
      plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
        hneReverse hDReverseΩ hne hi ≠ 0) ∧
    ∀ z : unramifiedCharacters (normCharacters χ),
      z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
      RationalFunctionNonnegAt (parameterScheme χ) (parameterProjection_continuous χ)
        (parameterScheme_isConnectedReductive χ hG)
        (plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
          hneReverse hDReverseΩ hne hi) z

/-! ### Reduction to IV.3(6) with positivity -/

section Reduction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
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
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (μM : Measure (levi χ ⧸ C)) [μM.IsHaarMeasure]
  [Finite (levi χ ⧸ (commonNormKernel (leviNormCharacters χ) ⊔ C))]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)

include hDForward hDReverse hD hC hsq in
/-- Under IV.3(6) with positivity, `μ` is regular with a nonnegative real value at every unitary
unramified character: `μ = c · j_P⁻¹` with `c = ∏_α γ(M_α|M)² ≥ 0`. -/
theorem plancherelDensity_nonnegAt_of_unitaryScalar
    (H : ConditionalDynamicOppositeUnitaryScalarStatement.{u, uV})
    (z : unramifiedCharacters (normCharacters χ))
    (hz : z.val ∈ unitaryUnramifiedCharacters (normCharacters χ)) :
    RationalFunctionNonnegAt (parameterScheme χ) (parameterProjection_continuous χ)
      (parameterScheme_isConnectedReductive χ hG)
      (plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
        hneReverse hDReverseΩ hne hi) z :=
  ((H χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hi C hC μM hsq).2 z hz).const_mul
    (parameterScheme χ) (parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) (plancherelDensityConstant_nonneg i ζ K hK)

include hDForward hDReverse hD hC hsq in
/-- Under IV.3(6) with positivity, `μ ≠ 0` when the product `∏_α γ(M_α|M)` is finite. -/
theorem plancherelDensity_ne_zero_of_unitaryScalar
    (H : ConditionalDynamicOppositeUnitaryScalarStatement.{u, uV})
    (hfin : rankOneGammaProduct i ζ K hK ≠ ⊤) :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
      hneReverse hDReverseΩ hne hi ≠ 0 :=
  fun h0 => (H χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hi C hC μM hsq).1
    ((plancherelDensity_eq_zero_iff i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
      hDForwardΩ hneReverse hDReverseΩ hne hi hfin).1 h0)

end Reduction

/-- **Reduction.** IV.3(6) with positivity implies the first two claims of Lemma V.2.1 for `μ`,
together with `μ ≠ 0` for a finite product. -/
theorem conditionalPlancherelDensityUnitaryStatement_of_unitaryScalar
    (H : ConditionalDynamicOppositeUnitaryScalarStatement.{u, uV}) :
    ConditionalPlancherelDensityUnitaryStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ T i ζ hRefl hCST hG K hK hPK hOppK A p q DForward DReverse hDForward
    hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ D hD hne hi C _ hC _ _ μM _ _ hsq
  exact ⟨fun hfin => plancherelDensity_ne_zero_of_unitaryScalar i ζ hRefl hCST hG K hK hPK hOppK
      A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq
      H hfin,
    plancherelDensity_nonnegAt_of_unitaryScalar i ζ hRefl hCST hG K hK hPK hOppK A p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi C hC μM hsq H⟩

end RationalPlancherelDensity

end Langlands.Plancherel
