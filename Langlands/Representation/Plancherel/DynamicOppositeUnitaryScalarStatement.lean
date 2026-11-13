import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients

/-! # Regularity and nonnegativity of `j⁻¹` at unitary points (target)

Waldspurger 2003, IV.3(6) (printed p.287): if `π` is square-integrable, `j(π) ≠ 0`. The proof
shows `j(π ⊗ χ) (e, e) = (J_{P̄|P}(π ⊗ χ) e, J_{P̄|P}(π ⊗ χ) e)` for unitary `χ`. Lemma V.2.1
(printed p.292) then makes `μ = j⁻¹ ∏_α γ(M_α|M)²` a rational function regular on `O` with
`μ ≥ 0`. This module defines regularity and nonnegative real value at a point for the rational
functions on unramified characters, and states the corresponding property of `j_P⁻¹` for the
Library's `conditionalCanonicalRationalScalar`. Nothing here is proved about `j_P`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Regular values of rational functions -/

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

/-- A rational function `f` on the unramified characters is **regular at `z`**: it is a quotient
`m / n` of regular functions with `n(z) ≠ 0`. -/
def RationalFunctionRegularAt (f : rationalUnramifiedFunctionField G hp hG) (z : XG) : Prop :=
  ∃ m n : RG, n.val z ≠ 0 ∧
    f = algebraMap RG (rationalUnramifiedFunctionField G hp hG) m /
      algebraMap RG (rationalUnramifiedFunctionField G hp hG) n

/-- A rational function `f` is regular at `z` with **nonnegative real value** there: some
presentation `f = m / n` with `n(z) ≠ 0` has `m(z) / n(z) ∈ [0, ∞)`. -/
def RationalFunctionNonnegAt (f : rationalUnramifiedFunctionField G hp hG) (z : XG) : Prop :=
  ∃ m n : RG, n.val z ≠ 0 ∧
    f = algebraMap RG (rationalUnramifiedFunctionField G hp hG) m /
      algebraMap RG (rationalUnramifiedFunctionField G hp hG) n ∧
    ∃ r : ℝ, 0 ≤ r ∧ m.val z / n.val z = (r : ℂ)

/-- The value at a point of regularity does not depend on the presentation: two presentations
`f = m / n = m' / n'` with `n(z) ≠ 0 ≠ n'(z)` give `m(z) / n(z) = m'(z) / n'(z)`. -/
theorem rationalFunction_value_eq {f : rationalUnramifiedFunctionField G hp hG} {z : XG}
    {m n m' n' : RG} (hn : n.val z ≠ 0) (hn' : n'.val z ≠ 0)
    (h : f = algebraMap RG (rationalUnramifiedFunctionField G hp hG) m /
      algebraMap RG (rationalUnramifiedFunctionField G hp hG) n)
    (h' : f = algebraMap RG (rationalUnramifiedFunctionField G hp hG) m' /
      algebraMap RG (rationalUnramifiedFunctionField G hp hG) n') :
    m.val z / n.val z = m'.val z / n'.val z := by
  have hinj := rationalUnramifiedFunctionField_algebraMap_injective G hp hG
  have hn0 : algebraMap RG (rationalUnramifiedFunctionField G hp hG) n ≠ 0 := by
    intro h0
    apply hn
    have : n = 0 := hinj (h0.trans (map_zero _).symm)
    simp [this]
  have hn0' : algebraMap RG (rationalUnramifiedFunctionField G hp hG) n' ≠ 0 := by
    intro h0
    apply hn'
    have : n' = 0 := hinj (h0.trans (map_zero _).symm)
    simp [this]
  have hcross : m * n' = m' * n := by
    apply hinj
    have := h.symm.trans h'
    rw [div_eq_div_iff hn0 hn0'] at this
    simpa only [map_mul] using this
  have hz := congrArg (fun g : RG => g.val z) hcross
  simp only [Subalgebra.coe_mul, Pi.mul_apply] at hz
  rw [div_eq_div_iff hn hn']
  exact hz

/-- Nonnegativity at a point includes regularity there. -/
theorem RationalFunctionNonnegAt.regularAt {f : rationalUnramifiedFunctionField G hp hG}
    {z : XG} (h : RationalFunctionNonnegAt G hp hG f z) : RationalFunctionRegularAt G hp hG f z :=
  h.elim fun m hm => hm.elim fun n hn => ⟨m, n, hn.1, hn.2.1⟩

end Regular

/-! ### The target for `j_P` -/

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

/-- **Target (Waldspurger IV.3(6), with the positivity from its proof).** Let `χ` be a cocharacter
of `G`, `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`. Let `A` be a smooth representation of
`M(F)` that is square-integrable modulo a central subgroup `C` with `M(F) / (M¹ C)` finite. Take
the conditional data of the canonical scalar `j_P` of `J_{P|P̄} J_{P̄|P}`: Iwasawa decompositions
for the compact open subgroup `K`, whole-operator continuations `p, q`, convergence domains and
a nonempty open locus where the induced representation is irreducible. Then `j_P ≠ 0`, and at
every unitary unramified character `z` the function `j_P⁻¹` is regular with a nonnegative real
value. -/
def ConditionalDynamicOppositeUnitaryScalarStatement : Prop :=
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
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi ≠ 0 ∧
      ∀ z : unramifiedCharacters (normCharacters χ),
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionNonnegAt (parameterScheme χ) (parameterProjection_continuous χ)
          (parameterScheme_isConnectedReductive χ hG)
          (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
            p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z

end Langlands.Plancherel
