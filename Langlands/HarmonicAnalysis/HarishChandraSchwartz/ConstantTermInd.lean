import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Langlands.Group.HaarModulus

/-! # The induced constant term and transitivity of constant terms

Waldspurger 2003, III.6: for `f ∈ C(G)` and a semi-standard parabolic subgroup `P = M U`,
`f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)}` defines a `G × G`-equivariant map from `C(G)`
to the induced space `I_{P×P}^{G×G} C(M)`, and for `P ⊆ P' = M' U'` the constant terms
along `P'` and along `P ∩ M'` compose to the constant term along `P` (the commutative
diagram of III.6, as in I.6).

Here `M, U, M', U'` are subgroups of a topological group `G`, `ν, ν'` are measures on `U`,
`U'`, and `δ, δ'` are positive characters of `M`, `M'`. The modulus relation
`d(m u m⁻¹) = δ(m) du` is the hypothesis `IsConjModulus`. The hypothesis `TransitivityData`
gives the measure on `U` as the image of a product measure on `(U ∩ M') × U'` under
multiplication, together with identities between the characters; in Waldspurger's setting
this is the integration formula for `U = (U ∩ M') U'`, but the hypothesis itself asserts no
decomposition of `U`. For a regular Haar measure `ν` and the Haar modulus
`HaarModulus.restrictCharacter` of the Library, `IsConjModulus` and (for nonarchimedean `U`
and closed `M`) the hypotheses `ConstantTermData` of `ConstantTerm` are proved.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

section Modulus

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M U : Subgroup G} (hMU : M ≤ Subgroup.normalizer (U : Set G))

/-- Conjugation `u ↦ m u m⁻¹` by `m ∈ M` as a homeomorphism of `U`. -/
def conjUnipotentHomeomorph (m : M) : U ≃ₜ U where
  toFun := conjUnipotent hMU m
  invFun := conjUnipotent hMU m⁻¹
  left_inv u := Subtype.ext <| by
    change ((m⁻¹ : M) : G) * ((m : G) * u * (m : G)⁻¹) * ((m⁻¹ : M) : G)⁻¹ = u
    simp only [InvMemClass.coe_inv]
    group
  right_inv u := Subtype.ext <| by
    change (m : G) * (((m⁻¹ : M) : G) * u * ((m⁻¹ : M) : G)⁻¹) * (m : G)⁻¹ = u
    simp only [InvMemClass.coe_inv]
    group
  continuous_toFun := continuous_conjUnipotent hMU m
  continuous_invFun := continuous_conjUnipotent hMU m⁻¹

variable [MeasurableSpace G]

/-- The modulus relation between `ν` and `δ`: conjugation by `m ∈ M` scales `ν` by
`δ(m)⁻¹`, that is `ν(m S m⁻¹) = δ(m) ν(S)`. For Waldspurger's `P = M U`, a Haar measure
`ν` on `U` and `δ = δ_P` this is the defining property of the modulus character. -/
def IsConjModulus (ν : Measure U) (δ : M →* ℝ≥0ˣ) : Prop :=
  ∀ m : M, ν.map (conjUnipotent hMU m) = (δ m : ℝ≥0)⁻¹ • ν

variable [BorelSpace G] {ν : Measure U} {δ : M →* ℝ≥0ˣ}

variable {hMU} in
/-- Change of variables `u ↦ m u m⁻¹`: `∫_U φ(m u m⁻¹) dν(u) = δ(m)⁻¹ ∫_U φ dν`. -/
theorem IsConjModulus.integral_comp (hν : IsConjModulus hMU ν δ) (m : M) (φ : U → ℂ) :
    ∫ u, φ (conjUnipotent hMU m u) ∂ν =
      ((((δ m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ u, φ u ∂ν := by
  calc ∫ u, φ (conjUnipotent hMU m u) ∂ν
      = ∫ u, φ ((conjUnipotentHomeomorph hMU m).toMeasurableEquiv u) ∂ν := rfl
    _ = ∫ u, φ u ∂(ν.map (conjUnipotentHomeomorph hMU m).toMeasurableEquiv) :=
        (integral_map_equiv _ φ).symm
    _ = ∫ u, φ u ∂(ν.map (conjUnipotent hMU m)) := rfl
    _ = _ := by rw [hν m, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

omit [IsTopologicalGroup G] [BorelSpace G] in
variable {hMU} in
/-- Under the modulus relation, `ν` is invariant under conjugation by the elements of
`M ∩ H` at which `δ` is trivial; so the hypotheses `ConstantTermData` of `ConstantTerm`
follow from `IsConjModulus` and triviality of `δ` on every `M ∩ H`. -/
theorem ConstantTermData.of_isConjModulus (hM : IsClosed (M : Set G))
    (hν : IsConjModulus hMU ν δ)
    (hδ : ∀ H : CompactOpenSubgroup G, ∀ m : M, (m : G) ∈ H.toSubgroup → δ m = 1) :
    ConstantTermData ν δ :=
  ⟨hM, hMU, hδ, fun H m hm => by rw [hν m, hδ H m hm]; simp⟩

/-- For a Haar measure `ν` on `U`, the modulus relation holds for the Haar modulus
`HaarModulus.restrictCharacter U M hMU` of the conjugation action of `M` on `U`. -/
theorem isConjModulus_restrictCharacter [LocallyCompactSpace U] (ν : Measure U)
    [ν.IsHaarMeasure] [ν.Regular] :
    IsConjModulus hMU ν (HaarModulus.restrictCharacter U M hMU) := by
  intro m
  have : BorelSpace U := Subtype.borelSpace (U : Set G)
  set φ := HaarModulus.normalizerConj U ⟨m, hMU m.2⟩
  have hφ : (conjUnipotent hMU m : U → U) = φ := rfl
  have key : ∀ (mU : MeasurableSpace U) (_ : @BorelSpace U _ mU),
      @mulEquivHaarChar U _ _ mU _ _ _ φ =
        (HaarModulus.restrictCharacter U M hMU m : ℝ≥0) := by
    intro mU hmU
    obtain rfl : mU = borel U := hmU.measurable_eq
    rfl
  have h := mulEquivHaarChar_smul_map ν φ
  rw [key _ inferInstance] at h
  rw [hφ]
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

omit [MeasurableSpace G] [BorelSpace G] in
/-- A character `χ : M →* ℝ≥0ˣ` with open kernel is trivial on every compact subgroup:
the kernel has finite index there, and `ℝ≥0ˣ` has no nontrivial torsion. -/
theorem eq_one_of_isOpen_ker_of_isCompact (χ : M →* ℝ≥0ˣ) (hχ : IsOpen (χ.ker : Set M))
    {K : Subgroup M} (hK : IsCompact (K : Set M)) {m : M} (hm : m ∈ K) : χ m = 1 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let χK := χ.comp K.subtype
  have hopen : IsOpen (χK.ker : Set K) := hχ.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen χK.ker hopen
  have hn := Subgroup.index_ne_zero_of_finite (H := χK.ker)
  have hpow : (⟨m, hm⟩ : K) ^ χK.ker.index ∈ χK.ker := Subgroup.pow_index_mem _ _
  rw [MonoidHom.mem_ker, map_pow] at hpow
  have h1 : ((χ m : ℝ≥0) ^ χK.ker.index) = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hpow
  exact Units.ext ((pow_eq_one_iff_of_nonneg zero_le hn).mp h1)

/-- For a Haar measure `ν` on a nonarchimedean `U` and the Haar modulus of the conjugation
action of a closed `M`, the hypotheses `ConstantTermData` of `ConstantTerm` hold. -/
theorem constantTermData_restrictCharacter [LocallyCompactSpace U] [NonarchimedeanGroup U]
    (hM : IsClosed (M : Set G))
    (ν : Measure U) [ν.IsHaarMeasure] [ν.Regular] :
    ConstantTermData ν (HaarModulus.restrictCharacter U M hMU) :=
  ConstantTermData.of_isConjModulus hM (isConjModulus_restrictCharacter hMU ν)
    fun H _ hm => eq_one_of_isOpen_ker_of_isCompact _
      (HaarModulus.isOpen_ker_restrictCharacter U M hMU) (H.subgroupOf hM).2
      (CompactOpenSubgroup.mem_subgroupOf.mpr hm)

omit [IsTopologicalGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The scalar identity `δ(m₁)^{1/2} δ(m₂)^{1/2} δ(m₂⁻¹ m m₁)^{1/2} = δ(m)^{1/2} δ(m₁)`. -/
theorem sqrt_mul_sqrt_mul_sqrt_conj (δ : M →* ℝ≥0ˣ) (m₁ m₂ m : M) :
    NNReal.sqrt (δ m₁) * NNReal.sqrt (δ m₂) * NNReal.sqrt (δ (m₂⁻¹ * m * m₁)) =
      NNReal.sqrt (δ m) * δ m₁ := by
  have h2 : NNReal.sqrt (δ m₂) ≠ 0 := by simp
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
    NNReal.sqrt_mul, NNReal.sqrt_mul, NNReal.sqrt_inv]
  rw [show ((δ m₁ : ℝ≥0)) = NNReal.sqrt (δ m₁) * NNReal.sqrt (δ m₁) from
    (NNReal.mul_self_sqrt _).symm]
  set a := NNReal.sqrt (δ m₂)
  set b := NNReal.sqrt (δ m)
  set c := NNReal.sqrt (NNReal.sqrt (δ m₁) * NNReal.sqrt (δ m₁))
  rw [show c * a * (a⁻¹ * b * c) = b * (c * c) * (a * a⁻¹) by ring, mul_inv_cancel₀ h2,
    mul_one]
  simp only [c, NNReal.sqrt_mul, NNReal.mul_self_sqrt]

variable {hMU} in
/-- Translations by `M`: `(ρ(m₁)λ(m₂)f)^{(P)}(m) = δ(m₁)^{1/2} δ(m₂)^{1/2} f^{(P)}(m₂⁻¹ m m₁)`. -/
theorem IsConjModulus.constantTerm_translate (hν : IsConjModulus hMU ν δ) (m₁ m₂ : M)
    (f : G → ℂ) (m : M) :
    constantTerm ν δ (translate (m₁ : G) m₂ f) m =
      ((NNReal.sqrt (δ m₁) : ℝ) : ℂ) * ((NNReal.sqrt (δ m₂) : ℝ) : ℂ) *
        constantTerm ν δ f (m₂⁻¹ * m * m₁) := by
  have key : (fun u : U => translate (m₁ : G) m₂ f ((m : G) * u)) =
      fun u => f (((m₂⁻¹ * m * m₁ : M) : G) * conjUnipotent hMU m₁⁻¹ u) := by
    funext u
    simp only [translate_apply, conjUnipotent, Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv]
    congr 1
    group
  have hI : ∫ u : U, translate (m₁ : G) m₂ f ((m : G) * u) ∂ν =
      (((δ m₁ : ℝ≥0) : ℝ) : ℂ) * ∫ u : U, f (((m₂⁻¹ * m * m₁ : M) : G) * u) ∂ν := by
    rw [key, hν.integral_comp m₁⁻¹ (fun u => f (((m₂⁻¹ * m * m₁ : M) : G) * u)), map_inv,
      Units.val_inv_eq_inv_val, inv_inv]
  have hs := congrArg (fun x : ℝ≥0 => ((x : ℝ) : ℂ)) (sqrt_mul_sqrt_mul_sqrt_conj δ m₁ m₂ m)
  simp only [NNReal.coe_mul, Complex.ofReal_mul] at hs
  simp only [constantTerm]
  rw [hI]
  linear_combination (-∫ u : U, f (((m₂⁻¹ * m * m₁ : M) : G) * u) ∂ν) * hs

include hMU in
variable (ν δ) in
/-- Translations by `U` do not change the constant term, for a left and right invariant
measure `ν` on `U`. -/
theorem constantTerm_translate_unipotent [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (u₁ u₂ : U) (f : G → ℂ) :
    constantTerm ν δ (translate (u₁ : G) u₂ f) = constantTerm ν δ f := by
  funext m
  simp only [constantTerm]
  congr 1
  set a : U := conjUnipotent hMU m⁻¹ u₂⁻¹
  have key : (fun u : U => translate (u₁ : G) u₂ f ((m : G) * u)) =
      fun u => (fun x : U => (fun y : U => f ((m : G) * y)) (a * x)) (u * u₁) := by
    funext u
    simp only [a, translate_apply, conjUnipotent, Subgroup.coe_mul, InvMemClass.coe_inv,
      inv_inv]
    congr 1
    group
  rw [key, integral_mul_right_eq_self (fun x : U => (fun y : U => f ((m : G) * y)) (a * x)),
    integral_mul_left_eq_self (fun y : U => f ((m : G) * y))]

end Modulus

section Induced

variable {G : Type u} [Group G] [MeasurableSpace G] {M U : Subgroup G}

/-- Waldspurger III.6: `f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)}`, a function on `M` for
each `(g₁, g₂) ∈ G × G`. -/
def constantTermInd (ν : Measure U) (δ : M →* ℝ≥0ˣ) (f : G → ℂ) (g : G × G) : M → ℂ :=
  constantTerm ν δ (translate g.1 g.2 f)

variable (ν : Measure U) (δ : M →* ℝ≥0ˣ)

/-- `G × G`-equivariance: `(ρ(h₁)λ(h₂)f)^{(P),Ind}(g₁, g₂) = f^{(P),Ind}(g₁ h₁, g₂ h₂)`. -/
theorem constantTermInd_translate (h₁ h₂ : G) (f : G → ℂ) (g : G × G) :
    constantTermInd ν δ (translate h₁ h₂ f) g = constantTermInd ν δ f (g.1 * h₁, g.2 * h₂) := by
  simp only [constantTermInd, translate_translate]

/-- Smoothness: if `f` is bi-invariant under `H`, then `f^{(P),Ind}` is right invariant
under `H × H`. -/
theorem IsBiInvariant.constantTermInd_mul {H : Subgroup G} {f : G → ℂ}
    (hf : IsBiInvariant H f) {h₁ h₂ : G} (h₁m : h₁ ∈ H) (h₂m : h₂ ∈ H) (g : G × G) :
    constantTermInd ν δ f (g.1 * h₁, g.2 * h₂) = constantTermInd ν δ f g := by
  rw [← constantTermInd_translate, hf.translate_eq h₁m h₂m]

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  {hMU : M ≤ Subgroup.normalizer (U : Set G)}

variable {ν δ} in
/-- Waldspurger III.6: for `f ∈ C(G)` the values `f^{(P),Ind}(g₁, g₂)` lie in `C(M)`, when
the translations `ρ(g₁)λ(g₂)` preserve `C(G)` (`TranslationWeights`). -/
theorem ConstantTermData.constantTermInd_mem_schwartzSubmodule
    [Nonempty (CompactOpenSubgroup G)] (hD : ConstantTermData ν δ) {Ξ σ : G → ℝ}
    {ΞM σM : M → ℝ} (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hw : TranslationWeights Ξ σ)
    (hΞM : ∀ m, 0 < ΞM m) (hσM : ∀ m, 0 ≤ σM m) {f : G → ℂ}
    (hf : f ∈ schwartzSubmodule Ξ σ) (g : G × G) :
    constantTermInd ν δ f g ∈ schwartzSubmodule ΞM σM :=
  hD.constantTerm_mem_schwartzSubmodule h hw.pos hw.nonneg hΞM hσM
    (hw.translate_mem_schwartzSubmodule g.1 g.2 hf)

variable {ν δ} in
/-- Waldspurger III.6: `f^{(P),Ind}` lies in `I_{P×P}^{G×G} C(M)`. For `m₁, m₂ ∈ M`,
`u₁, u₂ ∈ U` and `g₁, g₂ ∈ G`,
`f^{(P),Ind}(m₁ u₁ g₁, m₂ u₂ g₂) = δ(m₁)^{1/2} δ(m₂)^{1/2} ρ(m₁)λ(m₂) f^{(P),Ind}(g₁, g₂)`. -/
theorem IsConjModulus.constantTermInd_mul [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (hν : IsConjModulus hMU ν δ) (f : G → ℂ) (m₁ m₂ : M) (u₁ u₂ : U) (g₁ g₂ : G) (m : M) :
    constantTermInd ν δ f ((m₁ : G) * u₁ * g₁, (m₂ : G) * u₂ * g₂) m =
      ((NNReal.sqrt (δ m₁) : ℝ) : ℂ) * ((NNReal.sqrt (δ m₂) : ℝ) : ℂ) *
        translate m₁ m₂ (constantTermInd ν δ f (g₁, g₂)) m := by
  have e : translate ((m₁ : G) * u₁ * g₁) ((m₂ : G) * u₂ * g₂) f =
      translate (m₁ : G) m₂ (translate (u₁ : G) u₂ (translate g₁ g₂ f)) := by
    rw [translate_translate, translate_translate]
  simp only [constantTermInd]
  rw [e, hν.constantTerm_translate, constantTerm_translate_unipotent hMU ν δ, translate_apply]

end Induced

section Transitivity

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {M U M' U' : Subgroup G}

/-- The multiplication map `(U ∩ M') × U' → U`, `(v, u') ↦ v u'`, when `U' ≤ U`. -/
def unipotentMul (hU' : U' ≤ U) (p : U.subgroupOf M' × U') : U :=
  ⟨((p.1 : M') : G) * p.2, U.mul_mem (Subgroup.mem_subgroupOf.mp p.1.2) (hU' p.2.2)⟩

/-- The data relating the constant terms along `P = M U`, along `P' = M' U' ⊇ P`, and
along the parabolic subgroup `P ∩ M' = (M ∩ M')(U ∩ M')` of `M'`: `U' ≤ U`; the measure
`ν` on `U` is the image of `νi ⊗ ν'` under `(v, u') ↦ v u'`, for a measure `νi` on
`U ∩ M'`; `δ = δ' δi` on `M ∩ M'`; and `δ'` is trivial on `U ∩ M'`. These are an
integration formula and character identities; they do not assert that multiplication
`(U ∩ M') × U' → U` is surjective or injective. -/
structure TransitivityData (ν : Measure U) (δ : M →* ℝ≥0ˣ) (ν' : Measure U')
    (δ' : M' →* ℝ≥0ˣ) (νi : Measure (U.subgroupOf M')) (δi : M.subgroupOf M' →* ℝ≥0ˣ) :
    Prop where
  le_unipotent : U' ≤ U
  measure_eq_map : ν = (νi.prod ν').map (unipotentMul le_unipotent)
  delta_mul : ∀ m : M.subgroupOf M', δ ⟨((m : M') : G), m.2⟩ = δ' m * δi m
  delta_unipotent : ∀ v : U.subgroupOf M', δ' v = 1

variable {ν : Measure U} {δ : M →* ℝ≥0ˣ} {ν' : Measure U'} {δ' : M' →* ℝ≥0ˣ}
  {νi : Measure (U.subgroupOf M')} {δi : M.subgroupOf M' →* ℝ≥0ˣ}

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_unipotentMul (hU' : U' ≤ U) :
    Continuous (unipotentMul (M' := M') hU') :=
  ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- Transitivity of constant terms (Waldspurger III.6, commutative diagram): for `m` in
`M ∩ M'`, `(f^{(P')})^{(P ∩ M')}(m) = f^{(P)}(m)`, if `u ↦ f(m u)` is `ν`-integrable. -/
theorem TransitivityData.constantTerm_constantTerm (hT : TransitivityData ν δ ν' δ' νi δi)
    [SFinite νi] [SFinite ν'] (f : G → ℂ) (m : M.subgroupOf M')
    (hf : Integrable (fun u : U => f (((m : M') : G) * u)) ν) :
    constantTerm νi δi (constantTerm ν' δ' f) m = constantTerm ν δ f ⟨((m : M') : G), m.2⟩ := by
  obtain ⟨hU', hν, hδ, hδ'⟩ := hT
  subst hν
  have : SecondCountableTopology M' := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology U' := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (U.subgroupOf M') :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hmeas : Measurable (unipotentMul (M' := M') hU') := (continuous_unipotentMul hU').measurable
  set φ : U → ℂ := fun u => f (((m : M') : G) * u)
  have hφ : Integrable (φ ∘ unipotentMul hU') (νi.prod ν') :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas.aemeasurable).mp hf
  have hR : ∫ u, φ u ∂((νi.prod ν').map (unipotentMul hU')) =
      ∫ v, ∫ u', φ (unipotentMul hU' (v, u')) ∂ν' ∂νi := by
    rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    exact integral_prod _ hφ
  have hL : ∀ v : U.subgroupOf M',
      ((NNReal.sqrt (δ' ((m : M') * v)) : ℝ) : ℂ) *
          ∫ u' : U', f ((((m : M') * v : M') : G) * u') ∂ν' =
        ((NNReal.sqrt (δ' m) : ℝ) : ℂ) * ∫ u', φ (unipotentMul hU' (v, u')) ∂ν' := by
    intro v
    rw [map_mul, hδ' v, mul_one]
    congr 2
    funext u'
    simp only [φ, unipotentMul, Subgroup.coe_mul, mul_assoc]
  simp only [constantTerm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hL), integral_const_mul]
  change _ = ((NNReal.sqrt (δ ⟨((m : M') : G), m.2⟩) : ℝ) : ℂ) * ∫ u, φ u ∂_
  rw [hR, hδ, Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul, Complex.ofReal_mul]
  ring

/-- Transitivity of constant terms on `C(G)`: under the estimate of Proposition II.4.5 for
`P`, `(f^{(P')})^{(P ∩ M')}(m) = f^{(P)}(m)` for `f ∈ C(G)` and `m ∈ M ∩ M'`. -/
theorem TransitivityData.constantTerm_constantTerm_of_mem [Nonempty (CompactOpenSubgroup G)]
    (hT : TransitivityData ν δ ν' δ' νi δi) [SFinite νi] [SFinite ν'] {Ξ σ : G → ℝ}
    {ΞM σM : M → ℝ} (h : ConstantTermEstimate ν δ Ξ σ ΞM σM) (hΞ : ∀ g, 0 < Ξ g)
    (hσ : ∀ g, 0 ≤ σ g) {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) (m : M.subgroupOf M') :
    constantTerm νi δi (constantTerm ν' δ' f) m = constantTerm ν δ f ⟨((m : M') : G), m.2⟩ :=
  hT.constantTerm_constantTerm f m
    (h.integrable_of_mem_schwartzSubmodule hΞ hσ hf ⟨((m : M') : G), m.2⟩)

/-- The commutative diagram of Waldspurger III.6 for the induced constant terms. For
`g₁, g₂ ∈ G`, `m₁, m₂ ∈ M'` and `m ∈ M ∩ M'`,
`(f^{(P'),Ind}(g₁, g₂))^{(P ∩ M'),Ind}(m₁, m₂)(m)
  = δ'(m₁)^{-1/2} δ'(m₂)^{-1/2} f^{(P),Ind}(m₁ g₁, m₂ g₂)(m)`,
the right side being the image of `f^{(P),Ind}` under the isomorphism of induction in
stages. -/
theorem TransitivityData.constantTermInd_constantTermInd
    (hT : TransitivityData ν δ ν' δ' νi δi) [SFinite νi] [SFinite ν']
    {hMU' : M' ≤ Subgroup.normalizer (U' : Set G)} (hν' : IsConjModulus hMU' ν' δ')
    (f : G → ℂ) (g₁ g₂ : G) (m₁ m₂ : M') (m : M.subgroupOf M')
    (hf : Integrable (fun u : U =>
      translate ((m₁ : G) * g₁) ((m₂ : G) * g₂) f (((m : M') : G) * u)) ν) :
    constantTermInd νi δi (constantTermInd ν' δ' f (g₁, g₂)) (m₁, m₂) m =
      (((NNReal.sqrt (δ' m₁) : ℝ) : ℂ) * ((NNReal.sqrt (δ' m₂) : ℝ) : ℂ))⁻¹ *
        constantTermInd ν δ f ((m₁ : G) * g₁, (m₂ : G) * g₂) ⟨((m : M') : G), m.2⟩ := by
  set c : ℂ := ((NNReal.sqrt (δ' m₁) : ℝ) : ℂ) * ((NNReal.sqrt (δ' m₂) : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, NNReal.coe_eq_zero,
      NNReal.sqrt_eq_zero, Units.ne_zero, or_self, not_false_eq_true]
  have e : translate m₁ m₂ (constantTerm ν' δ' (translate g₁ g₂ f)) =
      c⁻¹ • constantTerm ν' δ' (translate (m₁ : G) m₂ (translate g₁ g₂ f)) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, hν'.constantTerm_translate, translate_apply,
      ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  simp only [constantTermInd]
  rw [e, constantTerm_smul, Pi.smul_apply, smul_eq_mul, translate_translate,
    hT.constantTerm_constantTerm _ m hf]

end Transitivity

end Langlands.HarishChandraSchwartz
