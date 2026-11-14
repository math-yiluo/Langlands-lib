import Langlands.Representation.Plancherel.DynamicOppositeUniformNonvanishing

/-! # Nonnegativity of `j_P⁻¹` on the unitary axis, reduced to regularity

Derived from the proof of Waldspurger IV.3 (6) (printed p.287). Module
`DynamicOppositeUniformNonvanishing` shows that `j_P⁻¹` has a positive real value at every
unitary point where both chosen continuations are regular. This module shows that, once
`j_P⁻¹` is known to be regular at a unitary point, its value there is a nonnegative real number.
The proof goes by density of the common regular unitary points.

* `continuous_finiteLaurentEvaluation_circle`: Laurent evaluation on circle tuples is
  continuous.
* `circle_infinite_of_mem_nhds`: every neighbourhood of a point of the circle is infinite.
* `rationalUnitaryRegularRestriction_coordinates_symm`: in the Library's circle coordinates, a
  regular function on the unitary characters is the Laurent evaluation of its Laurent
  preimage.
* `RationalFunctionRegularAt.nonnegAt_of_unitary` (generic): a rational function regular at a
  unitary point `z`, with nonnegative real values at the unitary points off the zero set of a
  nonzero regular function `g`, has a nonnegative real value at `z`.
* `ConditionalDynamicOppositeUnitaryInverseRegularStatement` is the target: under the
  hypotheses of `ConditionalDynamicOppositeUnitaryPositiveStatement`, `j_P⁻¹` is regular at
  every unitary unramified character.
* `ConditionalDynamicOppositeUnitaryInverseNonnegStatement`: under the same hypotheses,
  `j_P ≠ 0` and `j_P⁻¹` has a nonnegative real value at every unitary unramified character.
* `conditionalDynamicOppositeUnitaryInverseNonneg_of_regular` proves the second statement from
  the Hermitian adjunction target and the regularity target.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Laurent evaluation on circle tuples -/

section Circle

/-- Including a circle element in the complex units commutes with integer powers. -/
theorem circleToUnits_zpow_val (z : Circle) (k : ℤ) :
    ((Circle.toUnits z ^ k : ℂˣ) : ℂ) = ((z ^ k : Circle) : ℂ) := by
  rw [← map_zpow]
  rfl

/-- Laurent evaluation on circle tuples is continuous in the tuple. -/
theorem continuous_finiteLaurentEvaluation_circle {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    Continuous fun c : Fin n → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (c i)) p := by
  induction p using AddMonoidAlgebra.induction_on with
  | of m =>
      have he : ∀ c : Fin n → Circle,
          finiteLaurentEvaluation (fun i => Circle.toUnits (c i))
            (AddMonoidAlgebra.of ℂ (Fin n → ℤ) (Multiplicative.ofAdd m)) =
            ∏ i, ((c i ^ m i : Circle) : ℂ) := by
        intro c
        rw [AddMonoidAlgebra.of_apply, finiteLaurentEvaluation_single, one_mul]
        exact Finset.prod_congr rfl fun i _ => circleToUnits_zpow_val (c i) (m i)
      simp only [he]
      refine continuous_finsetProd _ fun i _ => ?_
      have h1 : Continuous fun c : Fin n → Circle => c i ^ m i :=
        (continuous_apply i).zpow (m i)
      exact continuous_subtype_val.comp h1
  | add x y hx hy =>
      simp only [map_add]
      exact hx.add hy
  | smul r x hx =>
      simp only [map_smul, smul_eq_mul]
      exact continuous_const.mul hx

/-- Every neighbourhood of a point of the circle is infinite. -/
theorem circle_infinite_of_mem_nhds {x : Circle} {s : Set Circle} (hs : s ∈ 𝓝 x) :
    s.Infinite := by
  have hI : (Set.Ioc (-Real.pi) Real.pi).Infinite :=
    Set.Ioc_infinite (by linarith [Real.pi_pos])
  let := hI.to_subtype
  have : Infinite Circle :=
    Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective
  exact infinite_of_mem_nhds x hs

end Circle

/-! ### Nonnegative values by density on the unitary characters -/

section Density

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance dynamicOppositeUnitaryInverseRegularityPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "XG" => unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "UG" =>
  unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

/-- In circle coordinates, a regular function restricted to the unitary characters is the
Laurent evaluation of its Laurent preimage. -/
theorem rationalUnitaryRegularRestriction_coordinates_symm
    (hG : GroupScheme.IsConnectedReductive G) (b : RG)
    (c : Fin (rationalImageRank G) → Circle) :
    rationalUnitaryRegularRestriction G b
        ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).symm c) =
      finiteLaurentEvaluation (fun i => Circle.toUnits (c i))
        ((rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG).symm b) := by
  rw [← rationalUnramifiedLaurentAlgebraEquiv_eval_unitary G hG, AlgEquiv.apply_symm_apply]

/-- The closed set of nonnegative real complex numbers, written with real and imaginary
parts. -/
theorem isClosed_nonnegReal_complex :
    IsClosed {w : ℂ | 0 ≤ w.re ∧ w.im = 0} :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

/-- A complex number is a nonnegative real number exactly when its imaginary part vanishes and
its real part is nonnegative. -/
theorem exists_nonneg_real_iff (w : ℂ) :
    (∃ r : ℝ, 0 ≤ r ∧ w = (r : ℂ)) ↔ 0 ≤ w.re ∧ w.im = 0 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp [hr]
  · rintro ⟨hre, him⟩
    exact ⟨w.re, hre, Complex.ext (by simp) (by simp [him])⟩

/-- **Nonnegativity by density.** Let `f` be a rational function regular at a unitary point
`z`. Suppose that `f` has a nonnegative real value at every unitary point outside the zero set
of a nonzero regular function `g`. Then the value of `f` at `z` is also a nonnegative real
number. -/
theorem RationalFunctionRegularAt.nonnegAt_of_unitary
    (hG : GroupScheme.IsConnectedReductive G)
    {f : rationalUnramifiedFunctionField G (continuous_rationalValuationImageProjection G) hG}
    {z : XG}
    (hf : RationalFunctionRegularAt G (continuous_rationalValuationImageProjection G) hG f z)
    (hz : z.val ∈ UG) (g : RG) (hg : g ≠ 0)
    (hpos : ∀ w : XG, w.val ∈ UG → g.val w ≠ 0 →
      RationalFunctionNonnegAt G (continuous_rationalValuationImageProjection G) hG f w) :
    RationalFunctionNonnegAt G (continuous_rationalValuationImageProjection G) hG f z := by
  obtain ⟨m, n, hn, hfmn⟩ := hf
  let := rationalUnramifiedRegularFunctions_isDomain G
    (continuous_rationalValuationImageProjection G) hG
  let Φ := rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG
  let a := rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG
  let ev : RG → (Fin (rationalImageRank G) → Circle) → ℂ := fun b c =>
    finiteLaurentEvaluation (fun i => Circle.toUnits (c i)) (a.symm b)
  have hev : ∀ (b : RG) (c : Fin (rationalImageRank G) → Circle),
      b.val ⟨(Φ.symm c).val, (Φ.symm c).property.1⟩ = ev b c :=
    fun b c => rationalUnitaryRegularRestriction_coordinates_symm G hG b c
  let zu : UG := ⟨z.val, hz⟩
  have hzΦ : (⟨(Φ.symm (Φ zu)).val, (Φ.symm (Φ zu)).property.1⟩ : XG) = z := by
    apply Subtype.ext
    rw [ContinuousMulEquiv.symm_apply_apply]
  have hnz : ev n (Φ zu) ≠ 0 := by
    rw [← hev, hzΦ]
    exact hn
  refine ⟨m, n, hn, hfmn, ?_⟩
  rw [show (∃ r : ℝ, 0 ≤ r ∧ m.val z / n.val z = (r : ℂ)) ↔ _ from
    exists_nonneg_real_iff (m.val z / n.val z)]
  by_contra hbad
  -- the bad set: a neighbourhood of the coordinates of `z`
  let S := {w : ℂ | 0 ≤ w.re ∧ w.im = 0}
  have hcont : ContinuousAt (fun c => ev m c / ev n c) (Φ zu) :=
    ((continuous_finiteLaurentEvaluation_circle _).continuousAt).div
      ((continuous_finiteLaurentEvaluation_circle _).continuousAt) hnz
  have hval : ev m (Φ zu) / ev n (Φ zu) = m.val z / n.val z := by
    rw [← hev, ← hev, hzΦ]
  have hU : {c | ev n c ≠ 0 ∧ ev m c / ev n c ∉ S} ∈ 𝓝 (Φ zu) := by
    refine inter_mem ?_ ?_
    · exact (continuous_finiteLaurentEvaluation_circle _).continuousAt.eventually_ne hnz
    · change (fun c => ev m c / ev n c) ⁻¹' Sᶜ ∈ 𝓝 (Φ zu)
      exact hcont.preimage_mem_nhds
        (isClosed_nonnegReal_complex.isOpen_compl.mem_nhds (by rw [hval]; exact hbad))
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  -- the product `g n` does not vanish on the box `∏ t i`
  have hgn : g * n ≠ 0 := by
    refine mul_ne_zero hg ?_
    intro h0
    apply hn
    rw [h0]
    rfl
  have hbox : ¬ ∀ c ∈ Set.pi Set.univ (fun i => Circle.toUnits '' t i),
      finiteLaurentEvaluation c (a.symm (g * n)) = 0 := by
    intro hall
    apply hgn
    apply a.symm.injective
    rw [map_zero]
    exact finiteLaurent_eq_zero_of_eval_on_box _ _
      (fun i => (circle_infinite_of_mem_nhds (ht i)).image
        (fun x _ y _ h => Circle.coe_injective (congrArg Units.val h))) _ hall
  push Not at hbox
  obtain ⟨c, hc, hc0⟩ := hbox
  choose t' ht' hct' using fun i => hc i (Set.mem_univ i)
  have hct : c = fun i => Circle.toUnits (t' i) := funext fun i => (hct' i).symm
  rw [hct] at hc0
  obtain ⟨hnt, hnotS⟩ := hsub (fun i _ => ht' i)
  let w : XG := ⟨(Φ.symm t').val, (Φ.symm t').property.1⟩
  have hw : w.val ∈ UG := (Φ.symm t').property
  have hgnw : g.val w * n.val w ≠ 0 := by
    have h1 := hev (g * n) t'
    rw [Subalgebra.coe_mul, Pi.mul_apply] at h1
    rw [h1]
    exact hc0
  have hnw : n.val w ≠ 0 := right_ne_zero_of_mul hgnw
  obtain ⟨m', n', hn', hf', r, hr, hv⟩ := hpos w hw (left_ne_zero_of_mul hgnw)
  have heq := rationalFunction_value_eq G (continuous_rationalValuationImageProjection G) hG
    hnw hn' hfmn hf'
  apply hnotS
  rw [← hev, ← hev]
  change m.val w / n.val w ∈ S
  rw [heq, hv]
  exact (exists_nonneg_real_iff _).mp ⟨r, hr, rfl⟩

end Density

/-! ### Regularity and nonnegativity of `j_P⁻¹` on the unitary axis -/

section Target

open Aubert.General Induction UnramifiedOperatorFamily
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
  hermitianAdjunctionPointMeasurable
  hermitianAdjunctionPointBorel

/-- **Target (regularity of `j_P⁻¹` on the unitary axis).** Under the hypotheses of
`ConditionalDynamicOppositeUnitaryPositiveStatement`, the function `j_P⁻¹` is regular at every
unitary unramified character. -/
def ConditionalDynamicOppositeUnitaryInverseRegularStatement : Prop :=
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
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (_hA : IsUnitarizable A.representation)
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
    (_hdag : ∀ z ∈ DForward,
      unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A),
    ∀ z : unramifiedCharacters (normCharacters χ),
      z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
      RationalFunctionRegularAt (parameterScheme χ) (parameterProjection_continuous χ)
        (parameterScheme_isConnectedReductive χ hG)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z

/-- **Target (nonnegativity of `j_P⁻¹` on the unitary axis).** Under the hypotheses of
`ConditionalDynamicOppositeUnitaryPositiveStatement`, `j_P ≠ 0`, and at every unitary
unramified character `j_P⁻¹` is regular with a nonnegative real value. -/
def ConditionalDynamicOppositeUnitaryInverseNonnegStatement : Prop :=
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
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (_hA : IsUnitarizable A.representation)
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
    (_hdag : ∀ z ∈ DForward,
      unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A),
    conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
        p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi ≠ 0 ∧
      ∀ z : unramifiedCharacters (normCharacters χ),
        z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
        RationalFunctionNonnegAt (parameterScheme χ) (parameterProjection_continuous χ)
          (parameterScheme_isConnectedReductive χ hG)
          (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
            p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi)⁻¹ z

/-- **Reduction.** The Hermitian adjunction of IV.1 (11) and the regularity of `j_P⁻¹` on the
unitary axis imply that `j_P⁻¹` has a nonnegative real value at every unitary unramified
character. At unitary common regular points of the continuations the value is positive by the
Hermitian adjunction; these points are the unitary points off the zero set of the product of the
two denominators, and nonnegativity extends to the remaining unitary points by density. -/
theorem conditionalDynamicOppositeUnitaryInverseNonneg_of_regular
    (H : ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV})
    (R : ConditionalDynamicOppositeUnitaryInverseRegularStatement.{u, uV}) :
    ConditionalDynamicOppositeUnitaryInverseNonnegStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A hA p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi hdag
  have hP := conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction H χ hRefl hCST
    hG K hK hPK hOppK hKsplit hOppKsplit A hA p q hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hi hdag
  have hR := R χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A hA p q hDForward hneForward
    hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi hdag
  have hpd : p.denominator ≠ 0 := fun h0 => hneForward.elim fun w hw =>
    p.denominator_nonzero ⟨w, hDForwardΩ hw⟩ (by rw [h0]; rfl)
  have hqd : q.denominator ≠ 0 := fun h0 => hneReverse.elim fun w hw =>
    q.denominator_nonzero ⟨w, hDReverseΩ hw⟩ (by rw [h0]; rfl)
  refine ⟨hP.1, fun z hz => ?_⟩
  let := rationalUnramifiedRegularFunctions_isDomain (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
  exact RationalFunctionRegularAt.nonnegAt_of_unitary (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) (hR z hz) hz
    (p.denominator * q.denominator) (mul_ne_zero hpd hqd)
    (fun w hw hgw =>
      have hgw' : p.denominator.val w * q.denominator.val w ≠ 0 := hgw
      ((hP.2 w ⟨left_ne_zero_of_mul hgw', right_ne_zero_of_mul hgw'⟩ hw).2).nonnegAt)

end Target

end Langlands.Plancherel
