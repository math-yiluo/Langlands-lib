import Langlands.Representation.Plancherel.RationalPlancherelConstant
import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar

/-! # Waldspurger's density `μ` of V.2 on actual data

Waldspurger 2003, V.2 (printed p.292): `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²`, where `α` runs over the
reduced roots of `A_M` up to sign and `j` is the scalar of IV.3 (printed p.285) by which
`J_{P|P̄}(π) J_{P̄|P}(π)` acts.

Here `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)` for `χ = ζ ≫ i`. For `j_P` this module takes
the Library's `conditionalCanonicalRationalScalar`: the rational function on the unramified
characters of `M` by which the continued composite `J_{P|P̄} J_{P̄|P}` acts, defined from
explicit continuation and irreducibility inputs. For the product it takes `rankOneGammaProduct`,
indexed by the submodules `X_*(A_α)`. Both use the Haar measures normalized by the same compact
open subgroup `K`. The density is the element `∏_α γ(M_α|M)² · j_P⁻¹` of the same field.
Identification of these objects with Waldspurger's `j` and `γ(M_α|M)` is not proved here.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

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

/-! ### The constant `∏_α γ(M_α|M)²` -/

section Constant

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The real number `∏_α γ(M_α|M)²` of V.2, with `α` over the reduced roots of `A_M` up to sign. -/
def plancherelDensityConstant : ℝ :=
  (rankOneGammaProduct i ζ K hK).toReal ^ 2

/-- The constant is a square, hence nonnegative. -/
theorem plancherelDensityConstant_nonneg : 0 ≤ plancherelDensityConstant i ζ K hK :=
  sq_nonneg _

/-- When the product is finite, the constant is at least `1`, since every `γ(M_α|M) ≥ 1`. -/
theorem one_le_plancherelDensityConstant (h : rankOneGammaProduct i ζ K hK ≠ ⊤) :
    1 ≤ plancherelDensityConstant i ζ K hK := by
  have h1 : (1 : ℝ) ≤ (rankOneGammaProduct i ζ K hK).toReal := by
    have := ENNReal.toReal_mono h (one_le_rankOneGammaProduct i ζ K hK)
    simpa using this
  unfold plancherelDensityConstant
  nlinarith

theorem plancherelDensityConstant_pos (h : rankOneGammaProduct i ζ K hK ≠ ⊤) :
    0 < plancherelDensityConstant i ζ K hK :=
  lt_of_lt_of_le one_pos (one_le_plancherelDensityConstant i ζ K hK h)

end Constant

/-! ### Elementary algebra used for the pointwise statement -/

section Elementary

/-- Two fraction presentations `r = c · (b / a)` and `r = m / n` with `m, n ≠ 0` give
`m a = c b n` in the ring. -/
private theorem mul_eq_of_div_presentations {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (hinj : Function.Injective (algebraMap R L)) {r : L} {a b c m n : R}
    (hab : r = algebraMap R L c * (algebraMap R L b / algebraMap R L a))
    (hmn : r = algebraMap R L m / algebraMap R L n) (hm : m ≠ 0) (hn : n ≠ 0) :
    m * a = c * b * n := by
  have hm' : algebraMap R L m ≠ 0 := fun h => hm (hinj (h.trans (map_zero _).symm))
  have hn' : algebraMap R L n ≠ 0 := fun h => hn (hinj (h.trans (map_zero _).symm))
  have ha' : algebraMap R L a ≠ 0 := by
    intro ha
    rw [ha, div_zero, mul_zero] at hab
    exact div_ne_zero hm' hn' (hmn.symm.trans hab)
  apply hinj
  have h := hab.symm.trans hmn
  rw [mul_div_assoc', div_eq_div_iff ha' hn'] at h
  simp only [map_mul]
  exact h.symm

/-- Evaluating a product identity in a subalgebra of complex-valued functions. -/
private theorem subalgebra_val_mul_eq {X : Type*} {S : Subalgebra ℂ (X → ℂ)} {m a b n : S}
    {c : ℂ} (h : m * a = algebraMap ℂ S c * b * n) (x : X) :
    m.val x * a.val x = c * b.val x * n.val x := by
  have h' := congrArg (fun f : S => f.val x) h
  simpa using h'

/-- A function that does not vanish at one point is a nonzero element of the subalgebra. -/
private theorem ne_zero_of_val_ne_zero {X : Type*} {S : Subalgebra ℂ (X → ℂ)} {m : S} {x : X}
    (h : m.val x ≠ 0) : m ≠ 0 := by
  intro hm
  apply h
  simp [hm]

/-- Solving `u x = c y v` for `x / y`. -/
private theorem div_eq_of_mul_eq {x y u v c : ℂ} (hy : y ≠ 0) (hu : u ≠ 0)
    (h : u * x = c * y * v) : x / y = c * v / u := by
  rw [div_eq_div_iff hy hu]
  linear_combination h

/-- Replacing the scalar in `f = c • x` by an equal scalar. -/
private theorem eq_smul_of_eq_smul {M : Type*} [SMul ℂ M] {f x : M} {c d : ℂ}
    (hf : f = c • x) (h : c = d) : f = d • x :=
  h ▸ hf

end Elementary

/-! ### The density as a rational function -/

section Density

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "RL" => unramifiedRegularFunctions (normCharacters (CommGroupScheme.groupHom ζ ≫ i))

variable
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

/-- The field of rational functions on the unramified characters of `M = Z_G(ζ ≫ i)`. -/
abbrev DensityField :=
  rationalUnramifiedFunctionField (parameterScheme χ) (parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG)

/-- A complex constant as an element of the field of rational functions. -/
def fieldConstant (c : ℂ) : DensityField i ζ hG :=
  algebraMap RL (DensityField i ζ hG) (algebraMap ℂ RL c)

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

/-- **Waldspurger's density** `μ = j_P⁻¹ ∏_α γ(M_α|M)²` (V.2, p.292), as a rational function on
the unramified characters of `M`, with `j_P` the canonical scalar of `J_{P|P̄} J_{P̄|P}`. -/
def plancherelDensity : DensityField i ζ hG :=
  fieldConstant i ζ hG (plancherelDensityConstant i ζ K hK : ℂ) * (jP)⁻¹

/-- Unfolding equation for `plancherelDensity`. -/
theorem plancherelDensity_def :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi =
      fieldConstant i ζ hG (plancherelDensityConstant i ζ K hK : ℂ) * (jP)⁻¹ :=
  rfl

/-- A nonzero complex constant is a nonzero rational function (evaluate at the trivial
character). -/
theorem fieldConstant_ne_zero {c : ℂ} (hc : c ≠ 0) : fieldConstant i ζ hG c ≠ 0 := by
  unfold fieldConstant
  intro h
  have h1 := rationalUnramifiedFunctionField_algebraMap_injective (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    (h.trans (map_zero _).symm)
  apply hc
  have h2 := congrArg (fun f : RL => f.val 1) h1
  simpa using h2

/-- `μ · j_P = ∏_α γ(M_α|M)²` whenever `j_P ≠ 0`. -/
theorem plancherelDensity_mul_scalar (hj : jP ≠ 0) :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi * jP =
      fieldConstant i ζ hG (plancherelDensityConstant i ζ K hK : ℂ) := by
  rw [plancherelDensity_def, mul_assoc, inv_mul_cancel₀ hj, mul_one]

/-- For a finite product, `μ` vanishes exactly when `j_P` does. -/
theorem plancherelDensity_eq_zero_iff (h : rankOneGammaProduct i ζ K hK ≠ ⊤) :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi = 0 ↔ jP = 0 := by
  have hc : fieldConstant i ζ hG (plancherelDensityConstant i ζ K hK : ℂ) ≠ 0 :=
    fieldConstant_ne_zero i ζ hG
      (Complex.ofReal_ne_zero.mpr (plancherelDensityConstant_pos i ζ K hK h).ne')
  rw [plancherelDensity_def, mul_eq_zero, inv_eq_zero]
  exact ⟨fun h' => h'.resolve_left hc, Or.inr⟩

include hDForward hDReverse in
/-- `μ` does not depend on the chosen whole-operator continuations. -/
theorem plancherelDensity_continuation_independent
    (p' : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q' : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A) :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi =
      plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p' q' hneForward hDForwardΩ
        hneReverse hDReverseΩ hne hi := by
  rw [plancherelDensity_def, plancherelDensity_def,
    conditionalCanonicalRationalScalar_continuation_independent χ hRefl hCST hG K hK hPK hOppK A
      p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hne hi p' q']

include hDForward hDReverse hD in
/-- `μ` does not depend on the open irreducibility locus used to extract `j_P`. -/
theorem plancherelDensity_irreducibility_locus_independent
    {D' : Set (unramifiedCharacters νL)} (hne' : D'.Nonempty)
    (hi' : ∀ z ∈ D',
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible) :
    plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi =
      plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
        hneReverse hDReverseΩ hne' hi' := by
  rw [plancherelDensity_def, plancherelDensity_def,
    conditionalCanonicalRationalScalar_irreducibility_locus_independent χ hRefl hCST hG K hK hPK
      hOppK A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
      hne' hi']

include hDForward hDReverse hD in
/-- `μ` is fixed by translation by every unramified self-twist of the inducing representation
(V.2.1, third item, for the stabilizer of `π`). -/
theorem plancherelDensity_stabilizer_fixed
    (τ : smoothRepUnramifiedTwistStabilizer νL (SmoothRep.pullback (parameterHomeomorph χ) A)) :
    rationalUnramifiedFunctionFieldTranslation (parameterScheme χ)
        (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG) τ.val
        (plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
          hneReverse hDReverseΩ hne hi) =
      plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi := by
  rw [plancherelDensity_def, map_mul, map_inv₀,
    conditionalCanonicalRationalScalar_stabilizer_fixed χ hRefl hCST hG K hK hPK hOppK A
      p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi τ]
  unfold fieldConstant
  rw [rationalUnramifiedFunctionFieldTranslation_constant]

include hDForward hDReverse hD in
/-- A regular presentation `j_P = a / b` gives `μ = (∏_α γ(M_α|M)²) · b / a`, while the continued
composite `J_{P|P̄} J_{P̄|P}` acts by `a(z) / b(z)` on the common regular region of the two
continuations, where `b` does not vanish. -/
theorem plancherelDensity_spec :
    ∃ a b : RL, b ≠ 0 ∧
      (∀ z : ↥(p.regularRegion ∩ q.regularRegion), b.val z.val ≠ 0) ∧
      plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
          hDReverseΩ hne hi =
        fieldConstant i ζ hG (plancherelDensityConstant i ζ K hK : ℂ) *
          (algebraMap RL (DensityField i ζ hG) b / algebraMap RL (DensityField i ζ hG) a) ∧
      ∀ z : ↥(p.regularRegion ∩ q.regularRegion),
        conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A
          p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z =
          (a.val z.val / b.val z.val) • Representation.IntertwiningMap.id
            (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
              (leviNormCharacters χ) (parameterTransport χ z.val) A).representation := by
  have hs := conditionalCanonicalRationalScalar_spec χ hRefl hCST hG K
    hK hPK hOppK A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
  refine hs.elim fun a ha => ha.elim fun b h => ⟨a, b, h.1, h.2.1, ?_, h.2.2.2⟩
  rw [plancherelDensity_def, h.2.2.1, inv_div]

include hDForward hDReverse hD in
/-- **Pointwise form of `μ = j_P⁻¹ ∏_α γ(M_α|M)²`.** If `μ = m / n` with regular `m, n` that do
not vanish at a point `z` of the common regular region, then the continued composite
`J_{P|P̄} J_{P̄|P}` acts at `z` by the scalar `(∏_α γ(M_α|M)²) · n(z) / m(z)`; that is,
`j_P(z) · μ(z) = ∏_α γ(M_α|M)²`. -/
theorem conditionalContinuedComposite_eq_plancherelDensity_value (m n : RL)
    (hμ : plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
        hneReverse hDReverseΩ hne hi =
      algebraMap RL (DensityField i ζ hG) m / algebraMap RL (DensityField i ζ hG) n)
    (z : ↥(p.regularRegion ∩ q.regularRegion)) (hm : m.val z.val ≠ 0)
    (hn : n.val z.val ≠ 0) :
    conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A
        p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ z =
      ((plancherelDensityConstant i ζ K hK : ℂ) * n.val z.val / m.val z.val) •
        Representation.IntertwiningMap.id
          (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
            (leviNormCharacters χ) (parameterTransport χ z.val) A).representation := by
  have hinj : Function.Injective (algebraMap RL (DensityField i ζ hG)) :=
    rationalUnramifiedFunctionField_algebraMap_injective (parameterScheme χ)
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
  have hspec := plancherelDensity_spec i ζ hRefl hCST hG K hK hPK hOppK
    A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi
  refine hspec.elim fun a ha => ha.elim fun b h => ?_
  have key := mul_eq_of_div_presentations hinj h.2.2.1 hμ (ne_zero_of_val_ne_zero hm)
    (ne_zero_of_val_ne_zero hn)
  exact eq_smul_of_eq_smul (h.2.2.2 z)
    (div_eq_of_mul_eq (h.2.1 z) hm (subalgebra_val_mul_eq key z.val))

end Density

end Langlands.Plancherel.RationalPlancherelDensity
