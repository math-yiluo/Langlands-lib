import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicStandardUnipotentProduct

/-! # Composition of constant terms along standard parabolics

For a compatible standard parabolic family, a continuous left `G(F)`-invariant function `f` and
standard indices `R, Q`, the constant terms satisfy `C_R (C_Q f) = C_{R ∩ Q} f`. The generic part
extends the Library's nested-average identity to inputs that are invariant only under the rational
points of the outer radical; the standard part uses `U_{R ∩ Q}(𝔸) ⊆ U_R(𝔸) U_Q(𝔸)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.ConstantTermComposition

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

section Generic

/-- Left invariance of a function on `G(𝔸)` under the actual rational subgroup of `V`. -/
def IsRationalInvariant (V : SubgroupFunctor G) (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ c : adelicPoints F G V, c ∈ rationalSubgroup F G V →
    ∀ x, φ ((c : AdelicGroupPoints F G) * x) = φ x

variable {F G}

/-- The function `[v] ↦ φ(v g)` on `V(F) \ V(𝔸)` of a `V(F)`-invariant `φ`. -/
def descendedIntegrand {V : SubgroupFunctor G} {φ : AdelicGroupPoints F G → ℂ}
    (hinv : IsRationalInvariant F G V φ) (g : AdelicGroupPoints F G) :
    RationalQuotient F G V → ℂ :=
  LeftCosetSpace.lift (rationalSubgroup F G V) (fun v => φ ((v : AdelicGroupPoints F G) * g))
    (fun c v => by
      change φ (((c.val : AdelicGroupPoints F G) * v.val) * g) = φ (v.val * g)
      rw [mul_assoc]
      exact hinv _ c.2 _)

/-- On chosen representatives the descended integrand is the original integrand. -/
theorem descendedIntegrand_out {V : SubgroupFunctor G} {φ : AdelicGroupPoints F G → ℂ}
    (hinv : IsRationalInvariant F G V φ) (g : AdelicGroupPoints F G)
    (x : RationalQuotient F G V) :
    descendedIntegrand hinv g x =
      φ (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g) := by
  conv_lhs => rw [← (Quotient.out_eq x : LeftCosetSpace.mk _ (Quotient.out x) = x)]
  rfl

/-- The descended integrand of a continuous function is continuous. -/
theorem continuous_descendedIntegrand {V : SubgroupFunctor G} {φ : AdelicGroupPoints F G → ℂ}
    (hinv : IsRationalInvariant F G V φ) (hφ : Continuous φ) (g : AdelicGroupPoints F G) :
    Continuous (descendedIntegrand hinv g) :=
  LeftCosetSpace.continuous_lift _ _ _ (hφ.comp (continuous_subtype_val.mul continuous_const))

end Generic

section Nested

variable {U V : SubgroupFunctor G} (h : U ≤ V) (hUV : U.IsNormalizedBy V)
  [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [hV : IsClosed (adelicPoints F G V : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)] [CompactSpace (RationalQuotient F G V)]

local instance outerLocallyCompact : LocallyCompactSpace (adelicPoints F G V) :=
  hV.locallyCompactSpace

local instance innerBorel : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

local instance outerBorel : BorelSpace (RationalQuotient F G V) :=
  rationalQuotientBorelSpace F G V

omit hV [CompactSpace (RationalQuotient F G V)] in
/-- Counting measure on the discrete rational subgroup is a Haar measure. -/
theorem rationalSubgroup_count_isHaarMeasure' :
    (Measure.count : Measure (rationalSubgroup F G V)).IsHaarMeasure := by
  let := LeftCosetSpace.isFiniteMeasureOnCompacts_count (rationalSubgroup F G V)
    (isDiscrete_rationalSubgroup F G V)
  exact { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }

include h hUV in
/-- Nested averages on the actual compact radical quotients, for a continuous function that is
only invariant under the rational points of the outer subgroup `V`. -/
theorem integral_integral_out_eq {φ : AdelicGroupPoints F G → ℂ} (hφ : Continuous φ)
    (hinv : IsRationalInvariant F G V φ) (g : AdelicGroupPoints F G) :
    (∫ x : RationalQuotient F G V,
      (∫ y : RationalQuotient F G U,
        φ (((Quotient.out y : adelicPoints F G U) : AdelicGroupPoints F G) *
          (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g))
        ∂normalizedRationalQuotientHaarMeasure F G U)
      ∂normalizedRationalQuotientHaarMeasure F G V) =
    ∫ x : RationalQuotient F G V,
      φ (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g)
      ∂normalizedRationalQuotientHaarMeasure F G V := by
  let Γ := rationalSubgroup F G V
  let Δ := rationalSubgroup F G U
  let j := adelicInclusion F G h
  let mU := normalizedRationalQuotientHaarMeasure F G U
  let mV := normalizedRationalQuotientHaarMeasure F G V
  let fG := descendedIntegrand hinv g
  have hΓ : IsDiscrete (Γ : Set (adelicPoints F G V)) := isDiscrete_rationalSubgroup F G V
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let : (Measure.count : Measure Γ).IsHaarMeasure := rationalSubgroup_count_isHaarMeasure' F G
  let : IsProbabilityMeasure mU := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  let : IsProbabilityMeasure mV := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let : mV.Regular :=
    (compactCompatibleNormalizedRationalQuotientMeasure F G V).property.2.regular
  have hj : Δ ≤ Γ.comap j := rationalSubgroup_le_comap_adelicInclusion F G h
  have hjc : Continuous j := continuous_subtype_val.subtype_mk _
  have hconj := LeftCosetSpace.subgroupAverageConjugation Γ Δ j hj mU (by
    rintro ⟨_, q, rfl⟩
    let a := adelicNormalizerConj F G hUV (rational F G V q⁻¹)
    have ha := adelicNormalizerConj_mem_rationalSubgroup_iff F G hUV q⁻¹
    refine ⟨a, ha, measurePreserving_rationalQuotientAutomorphism F G U a ha, fun n => ?_⟩
    apply Subtype.ext
    change (a n : AdelicGroupPoints F G) =
      (rational F G V q : AdelicGroupPoints F G)⁻¹ * n * (rational F G V q : AdelicGroupPoints F G)
    simp [a])
  have hi := LeftCosetSpace.integral_compactSubgroupAverage Γ Δ j hj hjc mU hconj
    (Γ.isClosed_of_isDiscrete hΓ) Measure.count mV
    (measurePreserving_rightTranslate_of_compactRationalQuotient F G V)
    (continuous_descendedIntegrand hinv hφ g)
  refine Eq.trans ?_ (hi.trans ?_)
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      have hx : LeftCosetSpace.mk Γ (Quotient.out x) = x := Quotient.out_eq x
      rw [← hx, LeftCosetSpace.compactSubgroupAverage_mk, hx]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        have hy : LeftCosetSpace.mk Δ (Quotient.out y) = y := Quotient.out_eq y
        conv_rhs => rw [← hy]
        change φ _ = φ (((j (Quotient.out y) * Quotient.out x : adelicPoints F G V) :
          AdelicGroupPoints F G) * g)
        exact congrArg φ (mul_assoc _ _ _).symm))
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => descendedIntegrand_out hinv g x)

end Nested

section Average

variable {F G} {U : SubgroupFunctor G}
  [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)]

local instance averageBorel : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

variable (U) in
/-- The average `∫_{U(F) \ U(𝔸)} φ(u g) du` on chosen representatives, with the normalized
quotient measure; this is the integral of `AdelicGroupPoints.subgroupConstantTerm`. -/
def average (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) : ℂ :=
  ∫ x : RationalQuotient F G U,
    φ (((Quotient.out x : adelicPoints F G U) : AdelicGroupPoints F G) * g)
    ∂normalizedRationalQuotientHaarMeasure F G U

/-- A function invariant under all of `U(𝔸)` equals its average. -/
theorem average_eq_self {φ : AdelicGroupPoints F G → ℂ}
    (hinv : ∀ n : adelicPoints F G U, ∀ x, φ ((n : AdelicGroupPoints F G) * x) = φ x)
    (g : AdelicGroupPoints F G) : average U φ g = φ g := by
  let : IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F G U) :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  unfold average
  simp_rw [hinv]
  rw [integral_const]
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- The average of a `U(F)`-invariant function is left `U(𝔸)`-invariant. -/
theorem average_subgroup_mul {φ : AdelicGroupPoints F G → ℂ}
    (hinv : IsRationalInvariant F G U φ) (n : adelicPoints F G U) (g : AdelicGroupPoints F G) :
    average U φ ((n : AdelicGroupPoints F G) * g) = average U φ g := by
  have hrep : ∀ h : AdelicGroupPoints F G, average U φ h =
      ∫ x, descendedIntegrand hinv h x ∂normalizedRationalQuotientHaarMeasure F G U := by
    intro h
    unfold average
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (descendedIntegrand_out hinv h x).symm))
  have hfun : descendedIntegrand hinv ((n : AdelicGroupPoints F G) * g) =
      descendedIntegrand hinv g ∘ LeftCosetSpace.rightTranslate (rationalSubgroup F G U) n := by
    funext x
    obtain ⟨m, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F G U) x
    rw [Function.comp_apply, LeftCosetSpace.rightTranslate_mk]
    change φ ((m : AdelicGroupPoints F G) * ((n : AdelicGroupPoints F G) * g)) =
      φ (((m * n : adelicPoints F G U) : AdelicGroupPoints F G) * g)
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hrep, hrep, hfun]
  exact (measurePreserving_rightTranslate_of_compactRationalQuotient F G U n).integral_comp
    (LeftCosetSpace.rightTranslateHomeomorph (rationalSubgroup F G U) n).measurableEmbedding _

/-- If `U` normalizes `W` and `φ` is left `W(𝔸)`-invariant, so is its average along `U`. -/
theorem average_normal_mul {W : SubgroupFunctor G} (hWU : W.IsNormalizedBy U)
    {φ : AdelicGroupPoints F G → ℂ}
    (hinv : ∀ n : adelicPoints F G W, ∀ x, φ ((n : AdelicGroupPoints F G) * x) = φ x)
    (n : adelicPoints F G W) (g : AdelicGroupPoints F G) :
    average U φ ((n : AdelicGroupPoints F G) * g) = average U φ g := by
  unfold average
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  set v : AdelicGroupPoints F G := ((Quotient.out x : adelicPoints F G U) : AdelicGroupPoints F G)
  have hv : v ∈ adelicPoints F G U := (Quotient.out x : adelicPoints F G U).2
  have hc : v * (n : AdelicGroupPoints F G) * v⁻¹ ∈ adelicPoints F G W := hWU _ _ _ hv n.2
  have heq : v * ((n : AdelicGroupPoints F G) * g) =
      (v * (n : AdelicGroupPoints F G) * v⁻¹) * (v * g) := by group
  change φ (v * ((n : AdelicGroupPoints F G) * g)) = φ (v * g)
  rw [heq]
  exact hinv ⟨_, hc⟩ _

end Average

end Langlands.Global.ConstantTermComposition

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.AdelicSubgroupPoints Langlands.Global.ConstantTermComposition

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

/-- The index `R ∩ Q` of the standard parabolic `P_R ∩ P_Q`. -/
def interIndex (R Q : Idx) : Idx := ⟨R.1 ∩ Q.1, Set.inter_subset_left.trans R.2⟩

/-- `P_{R ∩ Q} ≤ P_R`. -/
theorem interIndex_le_left (R Q : Idx) : 𝓕.interIndex R Q ≤ R := Set.inter_subset_left

/-- `P_{R ∩ Q} ≤ P_Q`. -/
theorem interIndex_le_right (R Q : Idx) : 𝓕.interIndex R Q ≤ Q := Set.inter_subset_right

/-- Every adelic point of `U_{R ∩ Q}` is a product of adelic points of `U_R` and `U_Q`. -/
theorem exists_mul_of_mem_radical_inter (R Q : Idx)
    (n : adelicPoints F G rad(𝓕.interIndex R Q)) :
    ∃ a : adelicPoints F G rad(R), ∃ b : adelicPoints F G rad(Q),
      (n : AdelicGroupPoints F G) = (a : AdelicGroupPoints F G) * (b : AdelicGroupPoints F G) := by
  obtain ⟨x, hn⟩ := n
  change x ∈ (rad(𝓕.interIndex R Q)).carrier _ at hn
  rw [𝓕.range_radical_eq_standardUnipotent] at hn
  obtain ⟨a, ha, b, hb, hab⟩ := StandardConstantTerm.standardUnipotent_inter_subset_mul
    𝓕.i 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic R.2 Q.2 _ hn
  have ha' : a ∈ adelicPoints F G rad(R) := by
    change a ∈ (rad(R)).carrier _
    rw [𝓕.range_radical_eq_standardUnipotent]
    exact ha
  have hb' : b ∈ adelicPoints F G rad(Q) := by
    change b ∈ (rad(Q)).carrier _
    rw [𝓕.range_radical_eq_standardUnipotent]
    exact hb
  exact ⟨⟨a, ha'⟩, ⟨b, hb'⟩, hab.symm⟩

/-- **Composition of constant terms.** For a continuous left `G(F)`-invariant `f` and standard
indices `R, Q`, the constant term along `P_R` of the constant term along `P_Q` is the constant term
along `P_{R ∩ Q}`: `C_R (C_Q f) = C_{R ∩ Q} f`. -/
theorem constantTerm_constantTerm (R Q : Idx) (f : ContinuousRationalFunctions F G) :
    𝓕.constantTerm R (𝓕.constantTerm Q (evaluate F G f)) =
      𝓕.constantTerm (𝓕.interIndex R Q) (evaluate F G f) := by
  have hIR : 𝓕.interIndex R Q ≤ R := 𝓕.interIndex_le_left R Q
  have hIQ : 𝓕.interIndex R Q ≤ Q := 𝓕.interIndex_le_right R Q
  let : IsClosed (adelicPoints F G rad(R) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU R ≫ 𝓕.p R)
  let : IsClosed (adelicPoints F G rad(Q) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let : IsClosed (adelicPoints F G rad(𝓕.interIndex R Q) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU (𝓕.interIndex R Q) ≫ 𝓕.p (𝓕.interIndex R Q))
  let := 𝓕.compactSpace_radicalRationalQuotient R
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  let := 𝓕.compactSpace_radicalRationalQuotient (𝓕.interIndex R Q)
  have hφ : 𝓕.constantTerm Q (evaluate F G f) = normalizedConstantTerm F G rad(Q) f :=
    funext fun x => (normalizedConstantTerm_range_eq_subgroupConstantTerm F G
      (𝓕.iU Q ≫ 𝓕.p Q) f x).symm
  have hφc : Continuous (𝓕.constantTerm Q (evaluate F G f)) :=
    hφ ▸ continuous_normalizedConstantTerm F G rad(Q) f
  have hRI : rad(R) ≤ rad(𝓕.interIndex R Q) := 𝓕.radical_le_of_le hIR
  have hQnI : rad(Q).IsNormalizedBy rad(𝓕.interIndex R Q) := 𝓕.radical_isNormalizedBy_of_le hIQ
  have hRnI : rad(R).IsNormalizedBy rad(𝓕.interIndex R Q) := 𝓕.radical_isNormalizedBy_of_le hIR
  have hQnR : rad(Q).IsNormalizedBy rad(R) := fun X v u hv hu => hQnI X v u (hRI X hv) hu
  have hφI : IsRationalInvariant F G rad(𝓕.interIndex R Q)
      (𝓕.constantTerm Q (evaluate F G f)) := by
    rintro _ ⟨q, rfl⟩ x
    rw [hφ]
    exact normalizedConstantTerm_rationalNormalizer_mul F G rad(Q) hQnI q f x
  have hφR : IsRationalInvariant F G rad(R) (𝓕.constantTerm Q (evaluate F G f)) := by
    rintro _ ⟨q, rfl⟩ x
    exact hφI (rational F G rad(𝓕.interIndex R Q) ⟨q.val, hRI _ q.2⟩) ⟨_, rfl⟩ x
  have hφQ : ∀ n : adelicPoints F G rad(Q), ∀ x,
      𝓕.constantTerm Q (evaluate F G f) ((n : AdelicGroupPoints F G) * x) =
        𝓕.constantTerm Q (evaluate F G f) x := by
    intro n x
    rw [hφ]
    exact normalizedConstantTerm_subgroup_mul F G rad(Q) f n x
  have hψ : 𝓕.constantTerm R (𝓕.constantTerm Q (evaluate F G f)) =
      average rad(R) (𝓕.constantTerm Q (evaluate F G f)) := rfl
  have hψI : ∀ n : adelicPoints F G rad(𝓕.interIndex R Q), ∀ x,
      average rad(R) (𝓕.constantTerm Q (evaluate F G f)) ((n : AdelicGroupPoints F G) * x) =
        average rad(R) (𝓕.constantTerm Q (evaluate F G f)) x := by
    intro n x
    obtain ⟨a, b, hab⟩ := 𝓕.exists_mul_of_mem_radical_inter R Q n
    rw [hab, mul_assoc, average_subgroup_mul hφR a, average_normal_mul hQnR hφQ b]
  funext g
  rw [hψ, ← average_eq_self hψI g]
  exact (integral_integral_out_eq F G hRI hRnI hφc hφI g).trans
    (congrFun (𝓕.constantTerm_constantTerm_of_le hIQ f) g)

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

/-- **Statement form.** For every compatible standard parabolic family of a connected reductive
group over a number field, every pair of standard indices `R, Q` and every continuous left
`G(F)`-invariant `f`, the constant term along `P_R` of the constant term along `P_Q` of `f` is the
constant term of `f` along `P_{R ∩ Q}`. -/
def ConstantTermCompositionStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (R Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (f : ContinuousRationalFunctions F G),
    𝓕.constantTerm R (𝓕.constantTerm Q (evaluate F G f)) =
      𝓕.constantTerm ⟨R.1 ∩ Q.1, Set.inter_subset_left.trans R.2⟩ (evaluate F G f)

/-- Proof of `ConstantTermCompositionStatement`. -/
theorem constantTermComposition : ConstantTermCompositionStatement.{u} :=
  fun 𝓕 R Q f => 𝓕.constantTerm_constantTerm R Q f

end Langlands.Global
