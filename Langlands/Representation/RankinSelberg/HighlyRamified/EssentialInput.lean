import Langlands.Representation.Conductor.EssentialStatement
import Langlands.Representation.Conductor.SphericalIntegrals
import Langlands.Representation.RankinSelberg.UniformRankOneTwistStatement
import Langlands.Representation.RankinSelberg.SphericalPairTorusReduction
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.EqualRankUnitNormalization
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.Whittaker.ModelKirillovProof
import Langlands.Representation.Whittaker.WhittakerTypeKirillovProof
import Langlands.HarmonicAnalysis.UnboundedConductorProof
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.Group.GL.ReindexCongr
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.RankinSelberg.HighlyRamified.DualTarget

/-!
# Essential vectors after a highly ramified twist

Jacquet and Shalika 1985, (4.4), first paragraph (printed page 327). Fix a level `m`
and twist by a quasicharacter `ξ` of large conductor `a(ξ)`. By the uniform rank-one
statement (JS85, Proposition (2.2)) every generic `π` of `GL_(n+3)(F)` with a level-`m`
vector has `L(s, π ⊗ ξ) = 1` and `ε(s, π ⊗ ξ, ψ) = c q^(-(n+3) a(ξ) s)`.

The Whittaker function `W₀` on `GL_(n+3)` supported on `N · GL_(n+3)(O)` with
`W₀(u k) = ψ(u)` is a compactly supported test function on the mirabolic subgroup, so by
the Kirillov theorem it is the restriction to the mirabolic of a vector `w` of the
Whittaker model of `π ⊗ ξ`. The corank-one integral of `w` against every spherical
Whittaker function `W(·; x; ψ̄)` of `GL_(n+2)` is the integral of the indicator of the
image of `GL_(n+2)(O)` in `N \ GL_(n+2)`, which is `1`. So `w` is an essential vector in
Jacquet's sense with `L(s, π ⊗ ξ) = 1`, and the level statement of JPSS 1981,
Theorem (5.1)(ii), makes it fixed by `K_1((n+3) a(ξ))`. Two such representations thus have
model vectors fixed at one common level which agree on the mirabolic subgroup and take
the value `1` at the identity. Such a vector also makes every central character trivial
on `1 + 𝔭^f`, since these scalars lie in `K_1(f)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration
open Langlands.GeneralLinear.Iwasawa
open scoped WithZero

universe uF uV

/-! ### The zero-cell Whittaker function -/

section ZeroCell

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  {ψ : UnitaryAdditiveCharacter F} (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

open scoped Classical in
/-- The indicator of the zero exponent. -/
def zeroExponentIndicator {m : ℕ} (lam : Fin m → ℤ) : ℂ := if lam = 0 then 1 else 0

/-- The `ψ`-Whittaker function on `GL_(m+1)` with value `ψ(u)` at `u k`, `u` upper
unipotent and `k ∈ GL_(m+1)(O)`, and value `0` off `N · GL_(m+1)(O)`: the cell function
of the indicator of the zero exponent. -/
def zeroCellWhittaker (m : ℕ) : WhittakerFunctions ψ m :=
  ⟨cellFunction hϖ (standardCharacter ψ m) zeroExponentIndicator,
    cellFunction_mem hϖ zeroExponentIndicator (isIntegrallyTrivial_standardCharacter hψ m)⟩

omit [ValuativeRel F] [TopologicalSpace F] in
/-- The torus element of the zero exponent is the identity. -/
theorem torus_zero {m : ℕ} : Iwasawa.torus ϖ (0 : Fin m → ℤ) = 1 := by
  rw [Iwasawa.torus]
  simp only [Pi.zero_apply, zpow_zero]
  exact map_one diagonalUnits

theorem zeroCellWhittaker_one (m : ℕ) : (zeroCellWhittaker hϖ hψ m).val 1 = 1 := by
  change cellFunction hϖ (standardCharacter ψ m) zeroExponentIndicator 1 = 1
  rw [cellFunction_one hϖ _ (isIntegrallyTrivial_standardCharacter hψ m)]
  simp [zeroExponentIndicator]

theorem zeroCellWhittaker_mul_integral (m : ℕ) (g : Langlands.GeneralLinear (m + 1) F)
    {k : Langlands.GeneralLinear (m + 1) F}
    (hk : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m) :
    (zeroCellWhittaker hϖ hψ m).val (g * k) = (zeroCellWhittaker hϖ hψ m).val g :=
  cellFunction_mul_integral hϖ _ (isIntegrallyTrivial_standardCharacter hψ m) g hk

/-- The zero-cell function vanishes off `N · GL_(m+1)(O)`. -/
theorem exists_eq_mul_of_zeroCellWhittaker_ne_zero (m : ℕ)
    {g : Langlands.GeneralLinear (m + 1) F} (hg : (zeroCellWhittaker hϖ hψ m).val g ≠ 0) :
    ∃ (u : upperUnipotent (m + 1) F) (k : Langlands.GeneralLinear (m + 1) F),
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m ∧ g = u.val * k := by
  obtain ⟨k, hk, hgk⟩ := exists_eq_unipotentPart hϖ g
  have he : exponent hϖ g = 0 := by
    by_contra hne
    apply hg
    change cellFunction hϖ (standardCharacter ψ m) zeroExponentIndicator g = 0
    rw [cellFunction]
    simp [zeroExponentIndicator, hne]
  refine ⟨unipotentPart hϖ g, k, hk, ?_⟩
  rw [he, torus_zero, mul_one] at hgk
  exact hgk

omit [ValuativeRel F] [TopologicalSpace F] in
/-- `diag(ϖ^lam, 1)` is the torus element of the exponent `(lam, 0)`. -/
theorem rankInclusion_torus {m : ℕ} (lam : Fin m → ℤ) :
    rankInclusion 1 (Iwasawa.torus ϖ lam) =
      Iwasawa.torus ϖ (Fin.snoc lam 0 : Fin (m + 1) → ℤ) := by
  apply Units.ext
  ext i j
  rw [Iwasawa.torus_val]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [(Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [(Fin.castSucc_lt_last i).ne]
    | cast j => simp [Iwasawa.torus_val, Matrix.diagonal_apply]

/-- On `diag(ϖ^lam, 1)` the zero-cell function is the indicator of `lam = 0`. -/
theorem zeroCellWhittaker_rankInclusion_torus (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    (zeroCellWhittaker hϖ hψ (m + 1)).val (rankInclusion 1 (Iwasawa.torus ϖ lam)) =
      if lam = 0 then 1 else 0 := by
  change cellFunction hϖ (standardCharacter ψ (m + 1)) zeroExponentIndicator
    (rankInclusion 1 (Iwasawa.torus ϖ lam)) = _
  rw [rankInclusion_torus, cellFunction_torus hϖ _ (isIntegrallyTrivial_standardCharacter hψ _)]
  by_cases hlam : lam = 0
  · subst hlam
    have h0 : (Fin.snoc (0 : Fin (m + 1) → ℤ) 0 : Fin (m + 1 + 1) → ℤ) = 0 := by
      funext i
      induction i using Fin.lastCases <;> simp
    have hA : Antitone (0 : Fin (m + 1 + 1) → ℤ) := fun _ _ _ => le_rfl
    rw [h0]
    simp [zeroExponentIndicator, hA]
  · have h0 : (Fin.snoc lam 0 : Fin (m + 1 + 1) → ℤ) ≠ 0 := by
      intro h
      apply hlam
      funext i
      simpa using congrFun h i.castSucc
    simp [zeroExponentIndicator, h0, hlam]

omit [ValuativeRel F] [TopologicalSpace F] in
/-- `diag(g, 1)` lies in the mirabolic subgroup. -/
theorem rankInclusion_lastRow {m : ℕ} (g : Langlands.GeneralLinear (m + 1) F)
    (j : Fin (m + 1 + 1)) :
    (rankInclusion 1 g).val (Fin.last (m + 1)) j = if j = Fin.last (m + 1) then 1 else 0 := by
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp [(Fin.castSucc_lt_last j).ne]

omit [TopologicalSpace F] in
/-- `diag(k, 1)` is integral for integral `k`. -/
theorem rankInclusion_mem_integralSubgroup {m : ℕ} {k : Langlands.GeneralLinear (m + 1) F}
    (hk : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m) :
    rankInclusion 1 k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer (m + 1) := by
  rw [← Conductor.levelSubgroup_zero]
  exact Conductor.rankInclusion_mem_congruenceSubgroup _ m _ ⟨k, hk⟩

/-- The zero-cell function is a compactly supported smooth test function on the
mirabolic subgroup: it is right `GL_(m+1)(O)`-invariant and supported on
`N · GL_(m+1)(O)`. -/
theorem isMirabolicTestFunction_zeroCellWhittaker [IsNonarchimedeanLocalField F] (m : ℕ) :
    IsMirabolicTestFunction ψ m (zeroCellWhittaker hϖ hψ m) := by
  refine ⟨⟨Conductor.levelOpenSubgroup F m 0, fun q k _ _ hk => ?_⟩,
    ⟨(Conductor.levelOpenSubgroup F m 0 : Set (Langlands.GeneralLinear (m + 1) F)),
      Conductor.isCompact_levelOpenSubgroup F m 0, fun q _ hq => ?_⟩⟩
  · have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m := by
      rw [← Conductor.levelSubgroup_zero]
      exact hk
    exact zeroCellWhittaker_mul_integral hϖ hψ m q hk'
  · obtain ⟨u, k, hk, rfl⟩ := exists_eq_mul_of_zeroCellWhittaker_ne_zero hϖ hψ m hq
    refine ⟨u, k, ?_, rfl⟩
    change k ∈ Conductor.levelSubgroup F m 0
    rw [Conductor.levelSubgroup_zero]
    exact hk

/-- A function on a topological group that is right invariant under an open subgroup
has open preimages. -/
theorem isOpen_preimage_of_mul_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : OpenSubgroup G) (f : G → X)
    (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) (S : Set X) : IsOpen (f ⁻¹' S) := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (K : Set G), ?_, isOpenMap_mul_left g _ K.isOpen,
    ⟨1, K.one_mem, mul_one g⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  change f (g * k) ∈ S
  rw [hf g k hk]
  exact hg

variable {abv : AbsoluteValue F ℝ}

/-- The corank-one function of the zero-cell function against a right
`GL_(n+1)(O)`-invariant inverse Whittaker function is right `GL_(n+1)(O)`-invariant. -/
theorem corankOneFunction_zeroCell_mul_integral
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) {n : ℕ}
    (W' : InverseWhittakerFunctions ψ n)
    (hW' : ∀ g k, k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer n →
      W'.val (g * k) = W'.val g) (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer n) :
    corankOneFunction ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s (g * k) =
      corankOneFunction ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s g := by
  unfold corankOneFunction
  rw [Conductor.determinantWeight_mul_integral habv g k hk, hW' g k hk, map_mul,
    zeroCellWhittaker_mul_integral hϖ hψ (n + 1) _ (rankInclusion_mem_integralSubgroup hk)]

/-- A Whittaker function agreeing with the zero-cell function on the mirabolic subgroup
has the same corank-one integrand. -/
theorem corankOneIntegrand_eq_zeroCell {n : ℕ} (W : WhittakerFunctions ψ (n + 1))
    (hW : ∀ g : Langlands.GeneralLinear (n + 1 + 1) F,
      (∀ j, g.val (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then 1 else 0) →
      W.val g = (zeroCellWhittaker hϖ hψ (n + 1)).val g)
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    corankOneIntegrand ψ abv W W' s =
      corankOneIntegrand ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s := by
  funext x
  induction x using Quotient.inductionOn with
  | h g =>
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk, hW _ (rankInclusion_lastRow g)]

end ZeroCell

/-! ### Jacquet's normalizations for a p-adic field -/

section Normalization

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An additive character of conductor exponent `0` has conductor `O` in Jacquet's sense:
it is trivial on `O`, and `ψ(x O) = 1` forces `x ∈ O`, since otherwise `x O ⊇ 𝔭^(-1)`. -/
theorem hasIntegerConductor_of_additiveConductor_eq_zero
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    Conductor.HasIntegerConductor ψ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  have h0 : T.AdditiveTrivialAt ψ 0 := (T.additiveTrivialAt_iff_le_conductor ψ 0).mpr hψ.ge
  refine ⟨fun x hx => h0 x ((T.mem_additiveLattice_zero x).mpr hx), fun x hx => ?_⟩
  by_contra hxO
  have hv : 1 < T.discreteValuation x := by
    rw [← not_le, ← T.mem_integers_iff_discreteValuation_le_one]
    exact hxO
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact not_lt_of_ge zero_le hv
  have hvx0 : T.discreteValuation x ≠ 0 := (_root_.map_ne_zero T.discreteValuation).mpr hx0
  have hexp : WithZero.exp 1 ≤ T.discreteValuation x := by
    rw [← WithZero.exp_log hvx0] at hv ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hv
    exact WithZero.exp_le_exp.mpr (by omega)
  have h1 : T.AdditiveTrivialAt ψ 1 := by
    intro z hz
    have hzx : z / x ∈ (ValuativeRel.valuation F.Carrier).integer := by
      change z / x ∈ T.Integers
      rw [T.mem_integers_iff_discreteValuation_le_one, map_div₀,
        div_le_one₀ (zero_lt_iff.mpr hvx0)]
      exact ((T.mem_additiveLattice 1 z).mp hz).trans hexp
    have h := hx (z / x) hzx
    rwa [mul_div_cancel₀ z hx0] at h
  have h2 : (1 : ℤ) ≤ 0 := le_of_le_of_eq ((T.additiveTrivialAt_iff_le_conductor ψ 1).mp h1) hψ
  omega

/-- The chosen uniformizer of the canonical data is a uniformizing element of
normalized absolute value `q⁻¹`. -/
theorem exists_uniformizingElement_normalizedAbs :
    letI := F.canonicalTopologicalData.valuativeRel
    ∃ ϖ : F.Carrierˣ, IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ ∧
      normalizedAbsoluteValue F.canonicalTopologicalData (ϖ : F.Carrier) =
        (F.canonicalTopologicalData.residueCardinality : ℝ)⁻¹ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hex : e (ValuativeRel.valuation F.Carrier T.uniformizer) = WithZero.exp (-1) :=
    T.discreteValuation_uniformizer
  have hx0 : T.uniformizer ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hex
    exact WithZero.exp_ne_zero hex.symm
  refine ⟨Units.mk0 T.uniformizer hx0, ⟨?_, fun y hy => ?_⟩, ?_⟩
  · rw [Units.val_mk0, ← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation F.Carrier y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation F.Carrier y)), ?_⟩
    have key : e (ValuativeRel.valuation F.Carrier y) =
        e (ValuativeRel.valuation F.Carrier (Units.mk0 T.uniformizer hx0 : F.Carrier) ^
          (-WithZero.log (e (ValuativeRel.valuation F.Carrier y)))) := by
      rw [map_zpow₀, Units.val_mk0, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one,
        neg_neg, WithZero.exp_log hy0]
    exact e.injective key
  · rw [Units.val_mk0, normalizedAbsoluteValue_apply, T.normalizedAbs_uniformizer, zpow_neg_one]

/-- The normalized absolute value is one on valuation units. -/
theorem normalizedAbsoluteValue_eq_one (x : F.Carrier)
    (hx : letI := F.canonicalTopologicalData.valuativeRel
      ValuativeRel.valuation F.Carrier x = 1) :
    normalizedAbsoluteValue F.canonicalTopologicalData x = 1 := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [normalizedAbsoluteValue_apply, T.normalizedAbs_eq_one_iff_discreteValuation]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
    (ValuativeRel.valuation F.Carrier x) = 1
  rw [hx, map_one]

/-- Every additive character of the canonical data has a self-dual Haar measure. -/
theorem nonempty_selfDualHaar
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier) :
    Nonempty (LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  obtain ⟨htd, hμ⟩ := HarmonicAnalysis.padicSelfDualMeasureExists F T
  let := htd
  obtain ⟨μ, hμ⟩ := hμ ψ
  exact ⟨⟨μ, hμ⟩⟩

end Normalization

/-! ### The corank-one integral of the zero-cell function -/

section Integral

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The density of the zero exponent is one. -/
theorem density_zero {T : F.TopologicalData} {n : ℕ} (ϖ : F.Carrierˣ) :
    QuotientTorusEnvelope.density F T ϖ (0 : Fin (n + 1) → ℤ) = 1 := by
  simp [QuotientTorusEnvelope.density, PadicField.TopologicalData.normalizedAbs_one]

/-- Against a right `GL_(n+1)(O)`-invariant inverse Whittaker function `W'` with
`W'(1) = 1`, the corank-one integrand of the zero-cell function is integrable for every
compatible quotient measure and has integral one, for every `s`: it is the indicator of
the image of `GL_(n+1)(O)`, and only the zero torus term of the Iwasawa sum survives. -/
theorem integrable_integral_corankOneIntegrand_zeroCell (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
    ∀ {ϖ : F.Carrierˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
      {ψ : UnitaryAdditiveCharacter F.Carrier}
      (hψ : ∀ x ∈ (ValuativeRel.valuation F.Carrier).integer, ψ x = 1)
      (W' : InverseWhittakerFunctions ψ n),
      (∀ g k, k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
        W'.val (g * k) = W'.val g) →
      W'.val 1 = 1 → ∀ s : ℂ,
      Integrable (corankOneIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        (zeroCellWhittaker hϖ hψ (n + 1)) W' s) μ ∧
      ∫ x, corankOneIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        (zeroCellWhittaker hϖ hψ (n + 1)) W' s x ∂μ = 1 := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  intro μ hμ ϖ hϖ ψ hψ W' hW' hW'1 s
  let abv := normalizedAbsoluteValue T
  have habv : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 → abv x = 1 :=
    fun x hx => normalizedAbsoluteValue_eq_one F x hx
  let E := corankOneIntegrand ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s
  have hinv : ∀ g, ∀ k ∈ Conductor.levelOpenSubgroup F.Carrier n 0,
      corankOneFunction ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s (g * k) =
        corankOneFunction ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s g := by
    intro g k hk
    have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n := by
      rw [← Conductor.levelSubgroup_zero]
      exact hk
    exact corankOneFunction_zeroCell_mul_integral hϖ hψ habv W' hW' s g hk'
  have hE : Measurable E := by
    intro S _
    apply IsOpen.measurableSet
    apply (leftQuotient_isOpenQuotientMap
      (upperUnipotent (n + 1) F.Carrier)).isQuotientMap.isOpen_preimage.mp
    exact isOpen_preimage_of_mul_invariant (Conductor.levelOpenSubgroup F.Carrier n 0)
      (corankOneFunction ψ abv (zeroCellWhittaker hϖ hψ (n + 1)) W' s) hinv S
  have hK : ∀ (lam : Fin (n + 1) → ℤ) (k : Langlands.GeneralLinear (n + 1) F.Carrier),
      k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
      E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam * k)) =
        E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam)) :=
    fun lam k hk => corankOneFunction_zeroCell_mul_integral hϖ hψ habv W' hW' s _ hk
  have hval : ∀ lam : Fin (n + 1) → ℤ,
      QuotientTorusEnvelope.torusCoefficient F T ϖ E lam = if lam = 0 then 1 else 0 := by
    intro lam
    change (QuotientTorusEnvelope.density F T ϖ lam : ℂ) *
      ((zeroCellWhittaker hϖ hψ (n + 1)).val (rankInclusion 1 (Iwasawa.torus ϖ lam)) *
        W'.val (Iwasawa.torus ϖ lam) * determinantWeight abv (Iwasawa.torus ϖ lam) (s - 1 / 2)) = _
    rw [zeroCellWhittaker_rankInclusion_torus]
    by_cases hlam : lam = 0
    · subst hlam
      rw [ite_eq_left rfl, density_zero, torus_zero, hW'1]
      simp [determinantWeight]
    · rw [ite_eq_right hlam, zero_mul, zero_mul, mul_zero]
  have hsum : Summable (fun lam => ‖QuotientTorusEnvelope.torusCoefficient F T ϖ E lam‖) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro lam hlam
    rw [Finset.mem_singleton] at hlam
    rw [hval, ite_eq_right hlam, norm_zero]
  obtain ⟨hi, heq⟩ := QuotientTorusEnvelope.integrable_integral_eq_tsum_torus F T n μ hμ ϖ hϖ
    E hE hK hsum
  refine ⟨hi, ?_⟩
  rw [heq]
  simp_rw [hval]
  exact tsum_ite_eq 0 1

end Integral

/-! ### The standard L-polynomial from the pair L-polynomial -/

section CharacterZeta

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient 0 F))

omit [MeasurableSpace F] in
/-- With an empty rectangular variable, the block zeta values against the unit point
mass do not depend on the σ-algebra of the one-point variable space. -/
theorem unequalRankZetaValues_dirac_congr {k : ℕ}
    (m₁ m₂ : MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F)) (h : m₁ = m₂)
    (π : Representation ℂ (Langlands.GeneralLinear (0 + (0 + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) ℂ) :
    (letI := m₁; unequalRankZetaValues q ψ abv 0 k μ (Measure.dirac 0) π σ) =
      (letI := m₂; unequalRankZetaValues q ψ abv 0 k μ (Measure.dirac 0) π σ) := by
  subst h
  rfl

/-- The zeta values of `π × 1` on `GL_(k+2)` are the block zeta values of the pair with the
trivial character of `GL_1` for the block `j = 0`, whatever the Haar measure on the
(empty) rectangular variable. -/
theorem characterZetaValues_succ_eq (ν : AdditiveHaarMeasure F) {k : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F) V) :
    characterZetaValues q ψ abv μ 1 (k + 1) π =
      unequalRankZetaValuesAt 0 k (by omega) q ψ abv μ (rectangularMeasure ν 0 (0 + 1)) π
        (rankOneCharacter (1 : Fˣ →* ℂˣ)) := by
  have key : ∀ (r : ℕ) (hr : r = 0 + (0 + k + 1))
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
      unequalRankZetaValuesAt 0 k hr q ψ abv μ (rectangularMeasure ν 0 (0 + 1)) π
          (rankOneCharacter (1 : Fˣ →* ℂˣ)) =
        unequalRankZetaValues q ψ abv 0 k μ (rectangularMeasure ν 0 (0 + 1))
          (π.comp (GeneralLinear.reindex (R := F)
            (finCongr (by omega : 0 + (0 + k + 1) + 1 = r + 1))).toMonoidHom)
          (rankOneCharacter (1 : Fˣ →* ℂˣ)) := by
    intro r hr π
    subst hr
    rw [unequalRankZetaValuesAt_rfl]
    congr 1
  rw [key (k + 1) _ π, rectangularMeasure_zero_rows]
  have : Subsingleton (Matrix (Fin 0) (Fin (0 + 1)) F) :=
    inferInstanceAs (Subsingleton (Fin 0 → Fin (0 + 1) → F))
  exact unequalRankZetaValues_dirac_congr q ψ abv μ ⊤ _
    (MeasurableSpace.ext fun _ => ⟨fun _ => Subsingleton.measurableSet,
      fun _ => MeasurableSpace.measurableSet_top⟩) _ _

end CharacterZeta

/-- A p-adic pair L-polynomial of `π` on `GL_(k+2)` against the trivial character of `GL_1`
is the standard L-polynomial of `π` for the rank-one quotient Haar measure. -/
theorem isCharacterLPolynomial_of_isPadicSymmetricLPolynomial {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V) {P : ℂ[X]}
    (h : IsPadicSymmetricLPolynomial F ψ ν π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) P) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient 0 F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
    IsCharacterLPolynomial F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) (rankOneQuotientHaar F.Carrier) 1
      π P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (0 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
  rw [IsPadicSymmetricLPolynomial, ite_eq_left (Nat.zero_le _)] at h
  obtain ⟨-, hP⟩ := h
  have h1 := hP (rankOneQuotientHaar F.Carrier) (rankOneQuotientHaar_isCompatible F.Carrier)
  rw [isPairLPolynomial_of_lt (by omega)] at h1
  unfold IsCharacterLPolynomial
  rw [characterZetaValues_succ_eq _ _ _ _ ν π]
  exact h1 0 k (by omega)

/-! ### Central characters of representations with a level-fixed model vector -/

section CentralCharacter

variable {F : Type uF} [Field F] [ValuativeRel F]

/-- A scalar `u = 1 + y` with `y ∈ 𝔭^f` and `f ≥ 1` lies in `K_1(f)`. -/
theorem scalar_mem_levelSubgroup {n f : ℕ} (hf : 0 < f) (u : Fˣ)
    (hu : ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (u : F) = 1 + y) :
    Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) u ∈ Conductor.levelSubgroup F n f := by
  obtain ⟨y, hy, hyu⟩ := hu
  have hym : y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer :=
    Ideal.pow_le_self (by omega) hy
  have hU : IsUnit (1 + y) := by
    by_contra h
    have h1 : (1 + y) ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer :=
      (IsLocalRing.mem_maximalIdeal _).mpr h
    have h2 := Ideal.sub_mem _ h1 hym
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  let U := hU.unit
  apply Conductor.principalLevelSubgroup_le_levelSubgroup F n f
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) U, ?_, ?_⟩
  · rw [SetLike.mem_coe, Conductor.mem_integralPrincipalCongruence]
    intro i j
    by_cases hij : i = j
    · subst hij
      have hy' : (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) U) i i -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) _) i i = y := by
        simp [Matrix.scalar_apply, U]
      rw [hy']
      exact hy
    · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, U, Matrix.GeneralLinearGroup.map, hyu]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.GeneralLinearGroup.map]

variable [TopologicalSpace F]

/-- A Whittaker model vector fixed by `K_1(f)`, `f ≥ 1`, with value `1` at the identity
makes every central character of the representation trivial on `1 + 𝔭^f`: for `u` in
`1 + 𝔭^f`, `ω(u) = ω(u) w(1) = w(u · 1) = w(1) = 1`. -/
theorem trivialOnPrincipalUnits_of_levelFixed {ψ : UnitaryAdditiveCharacter F} {r f : ℕ}
    (hf : 0 < f) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V} {ℓ : glFunctionals ψ r π}
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : ∀ g k, k ∈ Conductor.levelSubgroup F r f → w.val.val (g * k) = w.val.val g)
    (h1 : w.val.val 1 = 1) {ω : Fˣ →* ℂˣ}
    (hω : Classification.HasGLCentralCharacter F (r + 1) π ω) :
    TrivialOnPrincipalUnits ω f := by
  intro u hu
  obtain ⟨v, hv⟩ := w.property
  have hval : ∀ g, w.val.val g = ℓ.val (π g v) := fun g => by
    rw [← hv]
    rfl
  have h := hw 1 _ (scalar_mem_levelSubgroup hf u hu)
  have hv1 : ℓ.val v = 1 := by
    rw [← h1, hval 1, map_one, Module.End.one_apply]
  rw [one_mul, hval, hval, hω u v, map_smul, smul_eq_mul, map_one, Module.End.one_apply,
    hv1, mul_one] at h
  exact Units.ext h

end CentralCharacter

/-! ### Level-fixed essential vectors of the twisted representations -/

section Essential

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- For a generic `π` on `GL_(n+3)` with `L(s, π) = 1` and `ε(s, π, ψ) = c q^(-f s)`, the
Kirillov lift `w` of the zero-cell function is an essential vector with the polynomial
`1`, hence fixed by `K_1(f)`; it agrees with the zero-cell function on the mirabolic
subgroup. -/
theorem exists_levelFixed_zeroCell_modelVector
    (h2 : Conductor.EssentialVectorLevelStatement.{uF, uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (hψ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      Conductor.HasIntegerConductor ψ)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {ϖ : F.Carrierˣ}
    (hϖ : letI := F.canonicalTopologicalData.valuativeRel
      IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (hϖabv : normalizedAbsoluteValue F.canonicalTopologicalData (ϖ : F.Carrier) =
      (F.canonicalTopologicalData.residueCardinality : ℝ)⁻¹)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) V)
    (hπ : letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (n + 2) π)
    (hL : IsPadicSymmetricLPolynomial F ψ ν.val π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1)
    {c : ℂˣ} {f : ℕ}
    (hε : IsPadicSymmetricEpsilonFactor F ψ ν.val π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (c, (f : ℤ))) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    ∃ ℓ : glFunctionals ψ (n + 2) π, ℓ.val ≠ 0 ∧
      ∃ w : (coefficientModel π ℓ).toSubmodule,
        (∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (n + 2) f →
          w.val.val (g * k) = w.val.val g) ∧
        ∀ g : Langlands.GeneralLinear (n + 2 + 1) F.Carrier,
          (∀ j, g.val (Fin.last (n + 2)) j = if j = Fin.last (n + 2) then 1 else 0) →
          w.val.val g = (zeroCellWhittaker hϖ hψ.1 (n + 2)).val g := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  obtain ⟨w, hw⟩ := Whittaker.modelKirillovTransfer whittakerTypeKirillov p inferInstance F T
    (n + 2) V π ψ (isOfWhittakerType_of_isGeneric F hπ) ℓ hℓ (zeroCellWhittaker hϖ hψ.1 (n + 2))
    (isMirabolicTestFunction_zeroCellWhittaker hϖ hψ.1 (n + 2))
  refine ⟨ℓ, hℓ, w, ?_, hw⟩
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := T.fieldT2
  obtain ⟨htd, -⟩ := HarmonicAnalysis.padicSelfDualMeasureExists F T
  let := borel (Langlands.GeneralLinear (n + 1 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + 1) F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (0 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
  let μ := unipotentQuotientHaar F.Carrier (n + 1)
  have hμ : IsCompatible (upperUnipotent (n + 1 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (n + 1)) (unipotentHaar F.Carrier (n + 1)) μ :=
    unipotentQuotientHaar_isCompatible F.Carrier (n + 1)
  have hJ : Conductor.IsJacquetNormalization T.residueCardinality ψ
      (normalizedAbsoluteValue T) ϖ μ :=
    { residueCardinality := rfl
      uniformizer := hϖ
      abv_uniformizer := hϖabv
      abv_unit := normalizedAbsoluteValue_eq_one F
      conductor := hψ
      measure := hμ
      borel := ⟨rfl⟩
      borel_rankOne := ⟨rfl⟩ }
  have hess : Conductor.IsEssentialVector hJ π ℓ w := by
    refine ⟨⟨1, isCharacterLPolynomial_of_isPadicSymmetricLPolynomial F ψ ν.val π hL, ?_⟩, ?_⟩
    · intro x
      have hint := integrable_integral_corankOneIntegrand_zeroCell F (n + 1) μ hμ hϖ hψ.1
        (Conductor.inverseSphericalWhittaker hψ.1 hϖ T.residueCardinality x)
        (fun g k hk => Conductor.inverseSphericalWhittaker_mul_integral hψ.1 hϖ _ x g hk)
        (Conductor.inverseSphericalWhittaker_one hψ.1 hϖ _ x)
      have hrw : ∀ s, corankOneIntegrand ψ (normalizedAbsoluteValue T) w.val
          (Conductor.inverseSphericalWhittaker hψ.1 hϖ T.residueCardinality x) s =
          corankOneIntegrand ψ (normalizedAbsoluteValue T)
            (zeroCellWhittaker hϖ hψ.1 (n + 1 + 1))
            (Conductor.inverseSphericalWhittaker hψ.1 hϖ T.residueCardinality x) s :=
        fun s => corankOneIntegrand_eq_zeroCell hϖ hψ.1 w.val hw _ s
      refine ⟨⟨0, fun s _ => ?_⟩, ?_⟩
      · unfold CorankOneConverges
        rw [hrw]
        exact (hint s).1
      · have hfac : Conductor.essentialFactor (1 : ℂ[X]) x = 1 := by
          simp [Conductor.essentialFactor]
        rw [hfac]
        apply hasRationalContinuation_one_of_eq_on_halfPlane 0
        intro s _
        unfold corankOneIntegral
        rw [hrw]
        exact (hint s).2
    · intro g k
      rw [hw (rankInclusion 1 (g * k.val)) (rankInclusion_lastRow _),
        hw (rankInclusion 1 g) (rankInclusion_lastRow _), map_mul]
      exact zeroCellWhittaker_mul_integral hϖ hψ.1 (n + 2) _
        (rankInclusion_mem_integralSubgroup k.property)
  rw [IsPadicSymmetricEpsilonFactor, ite_eq_left (Nat.zero_le _)] at hε
  have hlev := h2 F.Carrier (n + 1) T.residueCardinality ψ (normalizedAbsoluteValue T) ϖ μ hJ
    ν.val ν.property π hπ ℓ hℓ w hess c f hε
  intro g k hk
  have he := (Conductor.mem_levelFixedVectors _ _ _).1 hlev k hk
  exact congrArg (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val g) he

end Essential

/-- Jacquet and Shalika 1985, (4.4), first paragraph (printed page 327), for candidates of
rank `n + 3`. Let `ψ` have conductor exponent `0`. For every level `m` there are a
quasicharacter `ξ` and a positive level `f` such that for any two generic representations
`π₁, π₂` of `GL_(n+3)(F)` with nonzero vectors fixed by `1 + ϖ^m M(O)`, the Whittaker
models of nonzero Whittaker functionals of `π_i ⊗ ξ ∘ det` contain vectors `w_i` fixed by
`K_1(f)` that agree on the mirabolic subgroup and take the value `1` at the identity;
every central character of `π_i ⊗ ξ ∘ det` is then trivial on `1 + 𝔭^f`. -/
def EssentialPairInput (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier),
    F.canonicalTopologicalData.additiveConductor ψ = 0 →
    ∀ m : ℕ, ∃ (ξ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier))
      (f : ℕ), 0 < f ∧
      ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
        (π₁ : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) V₁)
        (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) V₂),
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (n + 2) π₁) →
        (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (n + 2) π₂) →
        HasPrincipalLevelVector F π₁ m → HasPrincipalLevelVector F π₂ m →
        letI := F.canonicalTopologicalData.topology
        letI := F.canonicalTopologicalData.valuativeRel
        ∃ (ℓ₁ : glFunctionals ψ (n + 2)
            (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π₁))
          (ℓ₂ : glFunctionals ψ (n + 2)
            (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π₂)),
          ℓ₁.val ≠ 0 ∧ ℓ₂.val ≠ 0 ∧
          ∃ (w₁ : (coefficientModel _ ℓ₁).toSubmodule) (w₂ : (coefficientModel _ ℓ₂).toSubmodule),
            (∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (n + 2) f →
              w₁.val.val (g * k) = w₁.val.val g) ∧
            (∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (n + 2) f →
              w₂.val.val (g * k) = w₂.val.val g) ∧
            (∀ g : Langlands.GeneralLinear (n + 2 + 1) F.Carrier,
              (∀ j, g.val (Fin.last (n + 2)) j = if j = Fin.last (n + 2) then 1 else 0) →
              w₁.val.val g = w₂.val.val g) ∧
            w₁.val.val 1 = 1 ∧ w₂.val.val 1 = 1 ∧
            (∀ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (n + 2 + 1)
              (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) ω →
              TrivialOnPrincipalUnits ω f) ∧
            (∀ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (n + 2 + 1)
              (Langlands.twist ((ξ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) ω →
              TrivialOnPrincipalUnits ω f)

/-- The essential-vector input follows from the essential-vector level statement
(JPSS 1981, Theorem (5.1)(ii)) and the uniform rank-one statement (JS85, Proposition
(2.2)): `ξ` has conductor at least the rank-one bound and at least `1`, and
`f = (n + 3) a(ξ)`. -/
theorem essentialPairInput (h2 : Conductor.EssentialVectorLevelStatement.{uF, uV})
    (h3 : UniformRankOneTwistStatement.{uF, uV}) (n : ℕ) : EssentialPairInput.{uF, uV} n := by
  intro p _ F ψ hψ0 m
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  obtain ⟨ν⟩ := nonempty_selfDualHaar F ψ
  obtain ⟨B, hB, -⟩ := h3 p F ψ ν hψ0 (n + 2) m
  obtain ⟨ξ, hξ⟩ := padicQuasicharacterUnboundedConductor p F (max B 1)
  have hψ := hasIntegerConductor_of_additiveConductor_eq_zero F ψ hψ0
  obtain ⟨ϖ, hϖ, hϖabv⟩ := exists_uniformizingElement_normalizedAbs F
  have hξB : B ≤ T.multiplicativeConductor ξ := le_of_max_le_left hξ
  have hξ1 : 0 < T.multiplicativeConductor ξ := lt_of_lt_of_le one_pos (le_of_max_le_right hξ)
  have hf : 0 < (n + 2 + 1) * T.multiplicativeConductor ξ := Nat.mul_pos (by omega) hξ1
  refine ⟨ξ, (n + 2 + 1) * T.multiplicativeConductor ξ, hf, ?_⟩
  intro V₁ V₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂ hl₁ hl₂
  obtain ⟨hL₁, c₁, hε₁⟩ := hB π₁ hπ₁ hl₁ ξ hξB
  obtain ⟨hL₂, c₂, hε₂⟩ := hB π₂ hπ₂ hl₂ ξ hξB
  obtain ⟨ℓ₁, hℓ₁, w₁, hw₁, hP₁⟩ := exists_levelFixed_zeroCell_modelVector F h2 ψ hψ ν hϖ hϖabv
    _ (isGeneric_quasicharacter_twist T ψ ξ hπ₁) hL₁ hε₁
  obtain ⟨ℓ₂, hℓ₂, w₂, hw₂, hP₂⟩ := exists_levelFixed_zeroCell_modelVector F h2 ψ hψ ν hϖ hϖabv
    _ (isGeneric_quasicharacter_twist T ψ ξ hπ₂) hL₂ hε₂
  have h1 : ∀ j : Fin (n + 2 + 1),
      (1 : Langlands.GeneralLinear (n + 2 + 1) F.Carrier).val (Fin.last (n + 2)) j =
        if j = Fin.last (n + 2) then 1 else 0 := by
    intro j
    simp [Matrix.one_apply, eq_comm]
  have hw₁1 : w₁.val.val 1 = 1 := by rw [hP₁ 1 h1, zeroCellWhittaker_one]
  have hw₂1 : w₂.val.val 1 = 1 := by rw [hP₂ 1 h1, zeroCellWhittaker_one]
  exact ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, w₁, w₂, hw₁, hw₂,
    fun g hg => (hP₁ g hg).trans (hP₂ g hg).symm, hw₁1, hw₂1,
    fun _ hω => trivialOnPrincipalUnits_of_levelFixed hf w₁ hw₁ hw₁1 hω,
    fun _ hω => trivialOnPrincipalUnits_of_levelFixed hf w₂ hw₂ hw₂1 hω⟩

end Langlands.RankinSelberg.HighlyRamified
