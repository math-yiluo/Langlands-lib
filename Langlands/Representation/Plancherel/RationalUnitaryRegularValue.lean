import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement
import Langlands.Representation.Plancherel.RationalUnitaryNonvanishing
import Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions
import Langlands.Representation.Plancherel.UnramifiedScalarTranslation
import Langlands.Representation.Plancherel.RationalPlancherelDensity

/-! # Values on the unitary characters of rational functions regular there

Waldspurger 2003, V.2 and Lemma V.2.1 (printed p.292): the density `μ` is a rational function
on the unramified characters that is regular on the unitary orbit, so it defines a function
`ω ↦ μ(ω)` there. VI.3 (printed p.302) integrates it against smooth sections. This module
constructs that function for any rational function regular at every unitary point and proves:

* `rationalUnitaryValue_eq`: the value at a unitary point is `m(z) / n(z)` for every
  presentation `f = m / n` with `n(z) ≠ 0`;
* `isSmoothFiniteTorusFunction_rationalUnitaryValue`: the value function is smooth in the
  Library's circle coordinates, in the sense of `IsSmoothFiniteTorusFunction`;
* `continuous_rationalUnitaryValue`: it is continuous on the unitary characters;
* the algebra of the construction: regular functions (in particular constants), sums and
  products
  (`rationalUnitaryValue_add`, `rationalUnitaryValue_mul`, ...);
* `rationalUnitaryValue_translation`: compatibility with translation by a unitary character;
* `rationalUnitaryValue_nonneg`: the value is a nonnegative real number at every unitary point
  where `f` has a nonnegative real value.

The last section applies this to the Library's density `μ = (∏_α γ(M_α|M)²) j_P⁻¹`
(`plancherelDensity`). Under the hypothesis that `j_P⁻¹` is regular at every unitary character
(a part of Waldspurger IV.3 (6) not proved here), `plancherelWeight` is the function
`χ ↦ μ(π ⊗ χ)` on the unitary unramified characters of `M`. It is smooth in circle
coordinates, continuous, a nonnegative real number wherever `j_P⁻¹` has a nonnegative real value,
and invariant under translation by unitary self-twists of the inducing representation, in
particular by self-twists of finite order (`mem_unitaryCharacters_of_isOfFinOrder`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj ContDiff
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Laurent evaluation along the angle covering -/

section Angle

private theorem circleToUnits_zpow_coe (z : Circle) (k : ℤ) :
    ((Circle.toUnits z ^ k : ℂˣ) : ℂ) = ((z ^ k : Circle) : ℂ) := by
  rw [← map_zpow]
  rfl

/-- A Laurent monomial along the angle covering is an exponential. -/
theorem finiteLaurentEvaluation_finiteTorusExp_single {n : ℕ} (θ : Fin n → ℝ)
    (m : Fin n → ℤ) (a : ℂ) :
    finiteLaurentEvaluation (fun i => Circle.toUnits (finiteTorusExp θ i))
        (AddMonoidAlgebra.single m a) =
      a * ∏ i, Complex.exp ((((m i : ℝ) * θ i : ℝ) : ℂ) * Complex.I) := by
  rw [finiteLaurentEvaluation_single]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [circleToUnits_zpow_coe]
  change ((Circle.exp (θ i) ^ m i : Circle) : ℂ) = _
  rw [← Circle.exp_intCast_mul, Circle.coe_exp]

/-- Laurent evaluation along the angle covering `θ ↦ (e^{iθ_j})_j` is smooth. -/
theorem contDiff_finiteLaurentEvaluation_finiteTorusExp {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    ContDiff ℝ ∞ fun θ : Fin n → ℝ =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (finiteTorusExp θ i)) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin n → ℝ => (0 : ℂ))
  | add x y hx hy =>
      simp only [map_add]
      exact hx.add hy
  | single m a =>
      simp only [finiteLaurentEvaluation_finiteTorusExp_single]
      refine contDiff_const.mul (contDiff_prod fun i _ => ?_)
      refine Complex.contDiff_exp.comp (ContDiff.mul ?_ contDiff_const)
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_apply ℝ ℝ i))

end Angle

/-! ### The value function -/

section Value

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : GroupScheme.IsConnectedReductive G)

local instance rationalUnitaryRegularValuePointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "XG" => unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "UG" =>
  unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "KG" =>
  rationalUnramifiedFunctionField G (continuous_rationalValuationImageProjection G) hG

set_option hygiene false in
local notation "hpG" => continuous_rationalValuationImageProjection G

/-- A unitary unramified character, viewed as an unramified character. -/
def unitaryToUnramified (z : UG) : XG :=
  ⟨z.val, z.property.1⟩

/-- A rational function on the unramified characters is **regular on the unitary
characters** when it is regular, in the sense of `RationalFunctionRegularAt`, at every
unitary unramified character. -/
def RationalFunctionUnitaryRegular (f : KG) : Prop :=
  ∀ z : UG, RationalFunctionRegularAt G hpG hG f (unitaryToUnramified G z)

/-- **The value function** `z ↦ f(z)` on the unitary unramified characters of a rational
function `f` regular there: `m(z) / n(z)` for a chosen presentation `f = m / n` with
`n(z) ≠ 0`. By `rationalUnitaryValue_eq` the choice does not matter. -/
def rationalUnitaryValue (f : KG) (hf : RationalFunctionUnitaryRegular G hG f) (z : UG) : ℂ :=
  (Classical.choose (hf z)).val (unitaryToUnramified G z) /
    (Classical.choose (Classical.choose_spec (hf z))).val (unitaryToUnramified G z)

/-- The value at `z` is `m(z) / n(z)` for every presentation `f = m / n` with `n(z) ≠ 0`. -/
theorem rationalUnitaryValue_eq {f : KG} (hf : RationalFunctionUnitaryRegular G hG f)
    (z : UG) {m n : RG} (hn : n.val (unitaryToUnramified G z) ≠ 0)
    (hfmn : f = algebraMap RG KG m / algebraMap RG KG n) :
    rationalUnitaryValue G hG f hf z =
      m.val (unitaryToUnramified G z) / n.val (unitaryToUnramified G z) := by
  have hspec := Classical.choose_spec (Classical.choose_spec (hf z))
  exact rationalFunction_value_eq G hpG hG hspec.1 hn hspec.2 hfmn

/-- The value function does not depend on the proof of regularity. -/
theorem rationalUnitaryValue_congr {f g : KG} (hfg : f = g)
    (hf : RationalFunctionUnitaryRegular G hG f) (hg : RationalFunctionUnitaryRegular G hG g) :
    rationalUnitaryValue G hG f hf = rationalUnitaryValue G hG g hg := by
  subst hfg
  rfl

/-! #### Smoothness in the circle coordinates -/

set_option hygiene false in
local notation "Φ" => rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG

set_option hygiene false in
local notation "ΛG" => rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG

/-- In circle coordinates, a regular function at a unitary character is the Laurent
evaluation of its Laurent preimage. -/
theorem regular_val_unitaryToUnramified_coordinates_symm (b : RG)
    (c : Fin (rationalImageRank G) → Circle) :
    b.val (unitaryToUnramified G ((Φ).symm c)) =
      finiteLaurentEvaluation (fun i => Circle.toUnits (c i)) ((ΛG).symm b) := by
  rw [← rationalUnramifiedLaurentAlgebraEquiv_eval_unitary G hG, AlgEquiv.apply_symm_apply]
  rfl

/-- **Smoothness.** The value function of a rational function regular on the unitary
characters is smooth in the Library's circle coordinates. -/
theorem isSmoothFiniteTorusFunction_rationalUnitaryValue {f : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) :
    IsSmoothFiniteTorusFunction fun c => rationalUnitaryValue G hG f hf ((Φ).symm c) := by
  unfold IsSmoothFiniteTorusFunction
  rw [contDiff_iff_contDiffAt]
  intro θ
  obtain ⟨m, n, hn, hfmn⟩ := hf ((Φ).symm (finiteTorusExp θ))
  let ev : RG → (Fin (rationalImageRank G) → ℝ) → ℂ := fun b θ' =>
    finiteLaurentEvaluation (fun i => Circle.toUnits (finiteTorusExp θ' i)) ((ΛG).symm b)
  have hev : ∀ (b : RG) (θ' : Fin (rationalImageRank G) → ℝ),
      b.val (unitaryToUnramified G ((Φ).symm (finiteTorusExp θ'))) = ev b θ' :=
    fun b θ' => regular_val_unitaryToUnramified_coordinates_symm G hG b (finiteTorusExp θ')
  have hsmooth : ∀ b : RG, ContDiff ℝ ∞ (ev b) :=
    fun b => contDiff_finiteLaurentEvaluation_finiteTorusExp _
  have hnθ : ev n θ ≠ 0 := by
    rw [← hev]
    exact hn
  have hnear : ∀ᶠ θ' in 𝓝 θ, ev n θ' ≠ 0 :=
    (hsmooth n).continuous.continuousAt.eventually_ne hnθ
  have hquot : ContDiffAt ℝ ∞ (fun θ' => ev m θ' * (ev n θ')⁻¹) θ :=
    (hsmooth m).contDiffAt.mul ((hsmooth n).contDiffAt.inv hnθ)
  refine hquot.congr_of_eventuallyEq ?_
  filter_upwards [hnear] with θ' hθ'
  have hθ'' : n.val (unitaryToUnramified G ((Φ).symm (finiteTorusExp θ'))) ≠ 0 := by
    rw [hev]
    exact hθ'
  change rationalUnitaryValue G hG f hf ((Φ).symm (finiteTorusExp θ')) = _
  rw [rationalUnitaryValue_eq G hG hf _ hθ'' hfmn, hev, hev, div_eq_mul_inv]

/-- The value function is continuous on the unitary characters. -/
theorem continuous_rationalUnitaryValue {f : KG} (hf : RationalFunctionUnitaryRegular G hG f) :
    Continuous (rationalUnitaryValue G hG f hf) := by
  have h := (isSmoothFiniteTorusFunction_rationalUnitaryValue G hG hf).continuous
  have he : rationalUnitaryValue G hG f hf =
      (fun c => rationalUnitaryValue G hG f hf ((Φ).symm c)) ∘ (Φ) := by
    funext z
    simp
  rw [he]
  exact h.comp (Φ).continuous

/-! #### Algebra -/

/-- Regular functions are regular on the unitary characters. -/
theorem rationalFunctionUnitaryRegular_algebraMap (b : RG) :
    RationalFunctionUnitaryRegular G hG (algebraMap RG KG b) := by
  intro z
  refine ⟨b, 1, by simp, by simp⟩

/-- The value of a regular function is its value. -/
theorem rationalUnitaryValue_algebraMap (b : RG) (z : UG) :
    rationalUnitaryValue G hG (algebraMap RG KG b)
        (rationalFunctionUnitaryRegular_algebraMap G hG b) z =
      b.val (unitaryToUnramified G z) := by
  rw [rationalUnitaryValue_eq G hG _ z (m := b) (n := 1) (by simp) (by simp)]
  simp

/-- Products of functions regular on the unitary characters are regular there. -/
theorem RationalFunctionUnitaryRegular.mul {f g : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (hg : RationalFunctionUnitaryRegular G hG g) :
    RationalFunctionUnitaryRegular G hG (f * g) := by
  intro z
  obtain ⟨m, n, hn, hfmn⟩ := hf z
  obtain ⟨m', n', hn', hgmn⟩ := hg z
  refine ⟨m * m', n * n', ?_, ?_⟩
  · change n.val _ * n'.val _ ≠ 0
    exact mul_ne_zero hn hn'
  · rw [hfmn, hgmn, map_mul, map_mul, div_mul_div_comm]

/-- Sums of functions regular on the unitary characters are regular there. -/
theorem RationalFunctionUnitaryRegular.add {f g : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (hg : RationalFunctionUnitaryRegular G hG g) :
    RationalFunctionUnitaryRegular G hG (f + g) := by
  have hinj := rationalUnramifiedFunctionField_algebraMap_injective G hpG hG
  intro z
  obtain ⟨m, n, hn, hfmn⟩ := hf z
  obtain ⟨m', n', hn', hgmn⟩ := hg z
  have hn0 : algebraMap RG KG n ≠ 0 := by
    intro h0
    apply hn
    have : n = 0 := hinj (h0.trans (map_zero _).symm)
    simp [this]
  have hn0' : algebraMap RG KG n' ≠ 0 := by
    intro h0
    apply hn'
    have : n' = 0 := hinj (h0.trans (map_zero _).symm)
    simp [this]
  refine ⟨m * n' + n * m', n * n', ?_, ?_⟩
  · change n.val _ * n'.val _ ≠ 0
    exact mul_ne_zero hn hn'
  · rw [hfmn, hgmn, div_add_div _ _ hn0 hn0']
    simp only [map_add, map_mul]

/-- The value of a product is the product of the values. -/
theorem rationalUnitaryValue_mul {f g : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (hg : RationalFunctionUnitaryRegular G hG g)
    (z : UG) :
    rationalUnitaryValue G hG (f * g) (hf.mul G hG hg) z =
      rationalUnitaryValue G hG f hf z * rationalUnitaryValue G hG g hg z := by
  obtain ⟨m, n, hn, hfmn⟩ := hf z
  obtain ⟨m', n', hn', hgmn⟩ := hg z
  have hnn : (n * n').val (unitaryToUnramified G z) ≠ 0 := by
    change n.val _ * n'.val _ ≠ 0
    exact mul_ne_zero hn hn'
  rw [rationalUnitaryValue_eq G hG hf z hn hfmn, rationalUnitaryValue_eq G hG hg z hn' hgmn,
    rationalUnitaryValue_eq G hG _ z (m := m * m') hnn
      (by rw [hfmn, hgmn, map_mul, map_mul, div_mul_div_comm])]
  change m.val _ * m'.val _ / (n.val _ * n'.val _) = _
  rw [mul_div_mul_comm]

/-- The value of a sum is the sum of the values. -/
theorem rationalUnitaryValue_add {f g : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (hg : RationalFunctionUnitaryRegular G hG g)
    (z : UG) :
    rationalUnitaryValue G hG (f + g) (hf.add G hG hg) z =
      rationalUnitaryValue G hG f hf z + rationalUnitaryValue G hG g hg z := by
  have hinj := rationalUnramifiedFunctionField_algebraMap_injective G hpG hG
  obtain ⟨m, n, hn, hfmn⟩ := hf z
  obtain ⟨m', n', hn', hgmn⟩ := hg z
  have hn0 : algebraMap RG KG n ≠ 0 := by
    intro h0
    apply hn
    have : n = 0 := hinj (h0.trans (map_zero _).symm)
    simp [this]
  have hn0' : algebraMap RG KG n' ≠ 0 := by
    intro h0
    apply hn'
    have : n' = 0 := hinj (h0.trans (map_zero _).symm)
    simp [this]
  have hnn : (n * n').val (unitaryToUnramified G z) ≠ 0 := by
    change n.val _ * n'.val _ ≠ 0
    exact mul_ne_zero hn hn'
  rw [rationalUnitaryValue_eq G hG hf z hn hfmn, rationalUnitaryValue_eq G hG hg z hn' hgmn,
    rationalUnitaryValue_eq G hG _ z (m := m * n' + n * m') hnn
      (by rw [hfmn, hgmn, div_add_div _ _ hn0 hn0']; simp only [map_add, map_mul])]
  change (m.val _ * n'.val _ + n.val _ * m'.val _) / (n.val _ * n'.val _) = _
  rw [div_add_div _ _ hn hn']

/-! #### Translation by a unitary character -/

/-- Translating by a unitary character `τ` preserves regularity on the unitary characters. -/
theorem RationalFunctionUnitaryRegular.translation {f : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (τ : UG) :
    RationalFunctionUnitaryRegular G hG
      (rationalUnramifiedFunctionFieldTranslation G hpG hG (unitaryToUnramified G τ) f) := by
  intro z
  obtain ⟨m, n, hn, hfmn⟩ := hf (τ * z)
  refine ⟨unramifiedRegularTranslation _ (unitaryToUnramified G τ) m,
    unramifiedRegularTranslation _ (unitaryToUnramified G τ) n, ?_, ?_⟩
  · rw [unramifiedRegularTranslation_apply]
    exact hn
  · rw [hfmn, map_div₀, rationalUnramifiedFunctionFieldTranslation_algebraMap,
      rationalUnramifiedFunctionFieldTranslation_algebraMap]

/-- **Translation.** The value of the translate of `f` by a unitary character `τ` at `z` is the
value of `f` at `τ z`. -/
theorem rationalUnitaryValue_translation {f : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (τ z : UG) :
    rationalUnitaryValue G hG
        (rationalUnramifiedFunctionFieldTranslation G hpG hG (unitaryToUnramified G τ) f)
        (hf.translation G hG τ) z =
      rationalUnitaryValue G hG f hf (τ * z) := by
  obtain ⟨m, n, hn, hfmn⟩ := hf (τ * z)
  have hn' : (unramifiedRegularTranslation _ (unitaryToUnramified G τ) n).val
      (unitaryToUnramified G z) ≠ 0 := by
    rw [unramifiedRegularTranslation_apply]
    exact hn
  rw [rationalUnitaryValue_eq G hG hf (τ * z) hn hfmn,
    rationalUnitaryValue_eq G hG _ z hn'
      (by rw [hfmn, map_div₀, rationalUnramifiedFunctionFieldTranslation_algebraMap,
        rationalUnramifiedFunctionFieldTranslation_algebraMap]),
    unramifiedRegularTranslation_apply, unramifiedRegularTranslation_apply]
  rfl

/-- A function fixed by translation by a unitary character `τ` has a `τ`-invariant value
function. -/
theorem rationalUnitaryValue_mul_left_of_translation_eq {f : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (τ : UG)
    (hτ : rationalUnramifiedFunctionFieldTranslation G hpG hG (unitaryToUnramified G τ) f = f)
    (z : UG) :
    rationalUnitaryValue G hG f hf (τ * z) = rationalUnitaryValue G hG f hf z := by
  rw [← rationalUnitaryValue_translation G hG hf τ z]
  exact congrFun (rationalUnitaryValue_congr G hG hτ _ hf) z

/-! #### Nonnegative values -/

/-- If `f` has a nonnegative real value at every unitary character, then `f` is regular on
the unitary characters. -/
theorem RationalFunctionUnitaryRegular.of_nonnegAt {f : KG}
    (hf : ∀ z : UG, RationalFunctionNonnegAt G hpG hG f (unitaryToUnramified G z)) :
    RationalFunctionUnitaryRegular G hG f :=
  fun z => (hf z).regularAt

/-- **Nonnegativity.** If `f` has a nonnegative real value at a unitary character `z`, the
value function at `z` is that nonnegative real number. -/
theorem rationalUnitaryValue_nonneg {f : KG} (hf : RationalFunctionUnitaryRegular G hG f)
    {z : UG} (hz : RationalFunctionNonnegAt G hpG hG f (unitaryToUnramified G z)) :
    ∃ r : ℝ, 0 ≤ r ∧ rationalUnitaryValue G hG f hf z = (r : ℂ) := by
  obtain ⟨m, n, hn, hfmn, r, hr, hval⟩ := hz
  exact ⟨r, hr, (rationalUnitaryValue_eq G hG hf z hn hfmn).trans hval⟩

end Value

/-! ### Characters of finite order are unitary -/

section FiniteOrder

/-- A continuous complex character of finite order is unitary. -/
theorem mem_unitaryCharacters_of_isOfFinOrder {M : Type*} [Group M] [TopologicalSpace M]
    {τ : M →ₜ* ℂˣ} (hτ : IsOfFinOrder τ) : τ ∈ unitaryCharacters M := by
  obtain ⟨n, hn, hpow⟩ := hτ.exists_pow_eq_one
  intro g
  have h1 : (τ g) ^ n = 1 := by
    have := congrArg (fun σ : M →ₜ* ℂˣ => σ g) hpow
    simpa using this
  have h2 : ‖((τ g : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]
    simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

end FiniteOrder

/-! ### The Plancherel weight on the unitary characters -/

section Weight

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity

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
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom ζ ≫ i)) ψ).toMul)

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

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

set_option hygiene false in
local notation "μP" => plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
  hDForwardΩ hneReverse hDReverseΩ hne hi

set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG

/-- If `j_P⁻¹` is regular on the unitary characters, so is `μ = (∏_α γ(M_α|M)²) j_P⁻¹`. -/
theorem plancherelDensity_unitaryRegular
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    RationalFunctionUnitaryRegular MS hMS μP :=
  (rationalFunctionUnitaryRegular_algebraMap MS hMS _).mul MS hMS hreg

/-- **The Plancherel weight** `χ ↦ μ(π ⊗ χ)` on the unitary unramified characters of `M`
(Waldspurger V.2, V.2.1, printed p.292): the value function of the rational function `μ`,
under the hypothesis that `j_P⁻¹` is regular at every unitary character. -/
def plancherelWeight (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) : UL → ℂ :=
  rationalUnitaryValue MS hMS μP
    (plancherelDensity_unitaryRegular i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
      hDForwardΩ hneReverse hDReverseΩ hne hi hreg)

/-- The Plancherel weight is `∏_α γ(M_α|M)²` times the value of `j_P⁻¹`. -/
theorem plancherelWeight_eq (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (z : UL) :
    plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi hreg z =
      (plancherelDensityConstant i ζ K hK : ℂ) * rationalUnitaryValue MS hMS (jP)⁻¹ hreg z := by
  have h := rationalUnitaryValue_mul MS hMS (rationalFunctionUnitaryRegular_algebraMap MS hMS
    (algebraMap ℂ (unramifiedRegularFunctions νL) (plancherelDensityConstant i ζ K hK : ℂ)))
    hreg z
  have h2 := rationalUnitaryValue_algebraMap MS hMS
    (algebraMap ℂ (unramifiedRegularFunctions νL) (plancherelDensityConstant i ζ K hK : ℂ)) z
  have h3 : (algebraMap ℂ (unramifiedRegularFunctions νL)
      (plancherelDensityConstant i ζ K hK : ℂ)).val (unitaryToUnramified MS z) =
      (plancherelDensityConstant i ζ K hK : ℂ) := rfl
  exact h.trans (congrArg (fun w => w * rationalUnitaryValue MS hMS (jP)⁻¹ hreg z) (h2.trans h3))

/-- **Smoothness.** The Plancherel weight is smooth in the Library's circle coordinates. -/
theorem isSmoothFiniteTorusFunction_plancherelWeight
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    IsSmoothFiniteTorusFunction fun c =>
      plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
        hneReverse hDReverseΩ hne hi hreg
        ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).symm c) :=
  isSmoothFiniteTorusFunction_rationalUnitaryValue MS hMS _

/-- The Plancherel weight is continuous on the unitary characters. -/
theorem continuous_plancherelWeight (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Continuous (plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
      hneReverse hDReverseΩ hne hi hreg) :=
  continuous_rationalUnitaryValue MS hMS _

/-- **Nonnegativity.** At a unitary character where `j_P⁻¹` has a nonnegative real value, the
Plancherel weight is a nonnegative real number. -/
theorem plancherelWeight_nonneg (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) {z : UL}
    (hz : RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    ∃ r : ℝ, 0 ≤ r ∧ plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
        hDForwardΩ hneReverse hDReverseΩ hne hi hreg z = (r : ℂ) := by
  obtain ⟨r, hr, hval⟩ := rationalUnitaryValue_nonneg MS hMS hreg hz
  refine ⟨plancherelDensityConstant i ζ K hK * r,
    mul_nonneg (plancherelDensityConstant_nonneg i ζ K hK) hr, ?_⟩
  rw [plancherelWeight_eq, hval]
  push_cast
  rfl

include hDForward hDReverse hD in
/-- **Invariance.** Translation by a unitary unramified self-twist `τ` of the inducing
representation fixes the Plancherel weight (V.2.1, third item). -/
theorem plancherelWeight_stabilizer_invariant
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (τ : smoothRepUnramifiedTwistStabilizer νL (SmoothRep.pullback (parameterHomeomorph χ) A))
    (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL) :
    plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi hreg (⟨τ.val.val, τ.val.property, hτ⟩ * z) =
      plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi hreg z :=
  rationalUnitaryValue_mul_left_of_translation_eq MS hMS _ ⟨τ.val.val, τ.val.property, hτ⟩
    (plancherelDensity_stabilizer_fixed i ζ hRefl hCST hG K hK hPK hOppK A p q hDForward
      hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi τ) z

include hDForward hDReverse hD in
/-- A self-twist of finite order (for instance any element of a finite stabilizer) is unitary,
so it fixes the Plancherel weight. -/
theorem plancherelWeight_stabilizer_invariant_of_isOfFinOrder
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (τ : smoothRepUnramifiedTwistStabilizer νL (SmoothRep.pullback (parameterHomeomorph χ) A))
    (hτ : IsOfFinOrder τ) (z : UL) :
    plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi hreg
        (⟨τ.val.val, τ.val.property,
          mem_unitaryCharacters_of_isOfFinOrder ((Subgroup.subtype _).isOfFinOrder
            ((Subgroup.subtype _).isOfFinOrder hτ))⟩ * z) =
      plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hi hreg z :=
  plancherelWeight_stabilizer_invariant i ζ hRefl hCST hG K hK hPK hOppK A p q hDForward
    hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi hreg τ
    (mem_unitaryCharacters_of_isOfFinOrder ((Subgroup.subtype _).isOfFinOrder
      ((Subgroup.subtype _).isOfFinOrder hτ))) z

end Weight

end Langlands.Plancherel
