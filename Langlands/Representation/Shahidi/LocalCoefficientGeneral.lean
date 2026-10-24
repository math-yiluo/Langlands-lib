import Langlands.Representation.Shahidi.LocalCoefficientPadic
import Langlands.Group.GL.Nonarchimedean
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Shahidi's local coefficient over a general nonarchimedean local field

The relation (0.3) between the Jacquet functionals of the actual general-field
`I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)` and the intertwining operator `A(s, π, w_{m,n})`, for
the functional `λ₁ ⊗ λ₂` built from standard Whittaker functionals `λ₁` of `π₁` and `λ₂`
of `π₂`, over any nonarchimedean local field, including positive characteristic: the
relation that a rational function of `q^(-s)` is the local coefficient, for fixed
functionals and for all admissible choices, its uniqueness, rescaling, the passage from one
pair of functionals to all pairs under multiplicity one, and its literal reading through the
actual operator. The relations use the Borel structure `borel F` of `F`, as the
general-field analytic statements do. Compact open cofinality of the Levi is proved from the
local-field hypotheses.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shahidi

open GeneralLinear MeasureTheory HarmonicAnalysis Whittaker Topology

universe uF uV

/-! ## Compact open cofinality of the Levi -/

section Cofinal

private theorem localFieldInducedNonarchimedean {G H : Type*}
    [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : H →* G) (hf : IsInducing f) : NonarchimedeanGroup H where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
    exact ⟨OpenSubgroup.comap f hf.continuous L, fun x hx => hVU (hL hx)⟩

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem localFieldT2Space : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

private theorem localFieldGeneralLinearLocallyCompactSpace (r : ℕ) :
    LocallyCompactSpace (GeneralLinear r F) := by
  have := localFieldT2Space F
  have : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  exact inferInstance

/-- Over a nonarchimedean local field, every open subgroup of a block Levi
`∏ᵢ GL_{rᵢ}(F)` contains a compact open subgroup. The proof uses only the local-field
hypotheses: the actual `GL_r(F)` is nonarchimedean for the valuative topology
(`valuativeGeneralLinearNonarchimedean`) and locally compact, these properties pass to the
Levi through its block-diagonal image, and compact open subgroups then form an identity
neighborhood basis (`compactOpenSubgroupBasis`). -/
theorem generalLeviCompactOpenCofinal {r : ℕ} (B : BlockShape r) :
    CompactOpenCofinal (B.Levi F) := by
  have := Langlands.valuativeGeneralLinearNonarchimedean F r
  have := localFieldInducedNonarchimedean (B.leviSubgroup F).subtype .subtypeVal
  have := localFieldInducedNonarchimedean (B.leviEquivContinuous F).toMonoidHom
    (B.leviEquivContinuous F).toHomeomorph.isInducing
  have : ∀ i : Fin B.length, LocallyCompactSpace (GeneralLinear (B.size i) F) :=
    fun i => localFieldGeneralLinearLocallyCompactSpace F (B.size i)
  intro K
  obtain ⟨L, hL, hLK⟩ := Langlands.compactOpenSubgroupBasis (B.Levi F) K
    (K.isOpen.mem_nhds K.one_mem)
  exact ⟨L, hL, fun x hx => hLK hx⟩

end Cofinal

/-! ## The relation -/

section Relation

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (q : ℕ) (abv : AbsoluteValue F ℝ) (hopen : IsOpenNormOne abv)
variable {m n : ℕ}
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear (m + 1) F) V₁)
  (π₂ : Representation ℂ (GeneralLinear (n + 1) F) V₂)

/-- The functions `g ↦ f(g) ∈ V₁ ⊗ V₂`, for `f` in the actual general-field
`I(s, π₁ ⊗ π₂)` on `GL_{(m+1)+(n+1)}(F)`: the range of the published `sourceEval`. -/
def generalSourceFunctions (s : ℂ) :
    Set (GeneralLinear (m + 1 + (n + 1)) F → PiTensorProduct ℂ (pairCarrier V₁ V₂)) :=
  Set.range (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂)

/-- The same family, as the range of the published linear map `sourceFunction`. -/
theorem generalSourceFunctions_eq_range_sourceFunction (s : ℂ) :
    generalSourceFunctions abv hopen π₁ π₂ s =
      Set.range (sourceFunction abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) :=
  rfl

/-- `C` is Shahidi's local coefficient `C_χ(s, π₁ ⊗ π₂)` over the nonarchimedean local
field `F`, for the fixed standard Whittaker functionals `λ₁` of `π₁` and `λ₂` of `π₂`: the
generic `IsLocalCoefficient` for the actual general-field `I(s, π₁ ⊗ π₂)`, the functional
`λ₁ ⊗ λ₂` on both sides (the target functional `λ₂ ⊗ λ₁` of `I(-s, π₂ ⊗ π₁)` read through
`flip⁻¹`, see `satisfiesLocalCoefficientEquation_sourceEval_iff`), the measure `μ` of (0.1),
the measures `μJ`, `μJ'` of the two Jacquet integrals, all for the Borel structure of `F`,
and the variable `q^(-s)`. -/
def IsGeneralLocalCoefficientFor (ψ : UnitaryAdditiveCharacter F)
    (μ μJ : letI := borel F; Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (μJ' : letI := borel F; Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) (C : RatFunc ℂ) : Prop :=
  letI := borel F
  IsLocalCoefficient m n ψ (pairRepresentation (Nat.add_one_pos m) (Nat.add_one_pos n) π₁ π₂)
    (pairFunctional ℓ₁ ℓ₂) (pairFunctional ℓ₁ ℓ₂) μ μJ μJ' q
    (fun s => generalSourceFunctions abv hopen π₁ π₂ s) C

/-- `C` is Shahidi's local coefficient `C_χ(s, π₁ ⊗ π₂)` over `F`, quantified over the
admissible choices: `π₁` and `π₂` have nonzero standard Whittaker functionals, and `C` is
the local coefficient for every choice of nonzero standard Whittaker functionals `λ₁` of
`π₁` and `λ₂` of `π₂`. -/
def IsGeneralLocalCoefficient (ψ : UnitaryAdditiveCharacter F)
    (μ μJ : letI := borel F; Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (μJ' : letI := borel F; Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))
    (C : RatFunc ℂ) : Prop :=
  (∃ ℓ₁ ∈ glFunctionals ψ m π₁, ∃ ℓ₂ ∈ glFunctionals ψ n π₂, ℓ₁ ≠ 0 ∧ ℓ₂ ≠ 0) ∧
    ∀ ℓ₁ ∈ glFunctionals ψ m π₁, ∀ ℓ₂ ∈ glFunctionals ψ n π₂, ℓ₁ ≠ 0 → ℓ₂ ≠ 0 →
      IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C

variable {q abv hopen π₁ π₂}
variable {ψ : UnitaryAdditiveCharacter F}
  {μ μJ : letI := borel F; Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F)}
  {μJ' : letI := borel F; Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F)}

/-- For fixed functionals and smooth factors, the local coefficient is unique when
`1 < q`. -/
theorem IsGeneralLocalCoefficientFor.unique (hq : 1 < q) (hπ₁ : IsSmooth π₁)
    (hπ₂ : IsSmooth π₂) {ℓ₁ : V₁ →ₗ[ℂ] ℂ} {ℓ₂ : V₂ →ₗ[ℂ] ℂ} {C C' : RatFunc ℂ}
    (h : IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C)
    (h' : IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C') : C = C' :=
  letI := borel F
  IsLocalCoefficient.unique (generalLeviCompactOpenCofinal F _)
    (isSmooth_pairRepresentation _ _ hπ₁ hπ₂) hq h h'

/-- For smooth factors, the local coefficient is unique when `1 < q`. -/
theorem IsGeneralLocalCoefficient.unique (hq : 1 < q) (hπ₁ : IsSmooth π₁)
    (hπ₂ : IsSmooth π₂) {C C' : RatFunc ℂ}
    (h : IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C)
    (h' : IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C') : C = C' := by
  obtain ⟨⟨ℓ₁, hℓ₁, ℓ₂, hℓ₂, h₁, h₂⟩, hC⟩ := h
  exact IsGeneralLocalCoefficientFor.unique hq hπ₁ hπ₂ (hC ℓ₁ hℓ₁ ℓ₂ hℓ₂ h₁ h₂)
    (h'.2 ℓ₁ hℓ₁ ℓ₂ hℓ₂ h₁ h₂)

/-- Rescaling the functionals by nonzero scalars preserves the local coefficient. -/
theorem IsGeneralLocalCoefficientFor.smul {ℓ₁ : V₁ →ₗ[ℂ] ℂ} {ℓ₂ : V₂ →ₗ[ℂ] ℂ}
    {C : RatFunc ℂ} (h : IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' (a • ℓ₁) (b • ℓ₂) C := by
  let := borel F
  have := IsLocalCoefficient.smul h (mul_ne_zero hb ha)
  unfold IsGeneralLocalCoefficientFor
  simpa only [pairFunctional_smul_left, pairFunctional_smul_right, smul_smul] using this

/-- For nonzero scalars, the local coefficient for the rescaled functionals is the local
coefficient for the original ones. -/
theorem isGeneralLocalCoefficientFor_smul_iff {ℓ₁ : V₁ →ₗ[ℂ] ℂ} {ℓ₂ : V₂ →ₗ[ℂ] ℂ}
    {C : RatFunc ℂ} {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' (a • ℓ₁) (b • ℓ₂) C ↔
      IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C := by
  refine ⟨fun h => ?_, fun h => h.smul ha hb⟩
  simpa only [smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, one_smul] using
    h.smul (inv_ne_zero ha) (inv_ne_zero hb)

/-- Under multiplicity one of the standard Whittaker functionals, the local coefficient for
one choice of nonzero functionals is the local coefficient for all admissible choices. -/
theorem IsGeneralLocalCoefficientFor.isGeneralLocalCoefficient {ℓ₁ : V₁ →ₗ[ℂ] ℂ}
    {ℓ₂ : V₂ →ₗ[ℂ] ℂ} {C : RatFunc ℂ}
    (h : IsGeneralLocalCoefficientFor q abv hopen π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C)
    (hℓ₁ : ℓ₁ ∈ glFunctionals ψ m π₁) (hℓ₂ : ℓ₂ ∈ glFunctionals ψ n π₂)
    (h₁ : ℓ₁ ≠ 0) (h₂ : ℓ₂ ≠ 0)
    (hmult₁ : ∀ ℓ ∈ glFunctionals ψ m π₁, ∃ a : ℂ, ℓ = a • ℓ₁)
    (hmult₂ : ∀ ℓ ∈ glFunctionals ψ n π₂, ∃ b : ℂ, ℓ = b • ℓ₂) :
    IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C := by
  refine ⟨⟨ℓ₁, hℓ₁, ℓ₂, hℓ₂, h₁, h₂⟩, fun ℓ hℓ ℓ' hℓ' h₀ h₀' => ?_⟩
  obtain ⟨a, rfl⟩ := hmult₁ ℓ hℓ
  obtain ⟨b, rfl⟩ := hmult₂ ℓ' hℓ'
  have ha : a ≠ 0 := by
    rintro rfl
    exact h₀ (zero_smul ℂ ℓ₁)
  have hb : b ≠ 0 := by
    rintro rfl
    exact h₀' (zero_smul ℂ ℓ₂)
  exact h.smul ha hb

end Relation

/-! ## The literal reading of (0.3) -/

section Literal

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]
variable {abv : AbsoluteValue F ℝ} (hopen : IsOpenNormOne abv)
variable {m n : ℕ}
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable {π₁ : Representation ℂ (GeneralLinear (m + 1) F) V₁}
  {π₂ : Representation ℂ (GeneralLinear (n + 1) F) V₂}
variable (ψ : UnitaryAdditiveCharacter F)
  {μ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F)} [μ.IsAddLeftInvariant]
  (μJ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
  (μJ' : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F))

/-- Equation (0.3) for `f ∈ I(s, π₁ ⊗ π₂)` in the convergence domain, read literally: the
generic relation at `f` with the functional `λ₁ ⊗ λ₂` on both sides holds exactly when
`c ≠ 0`, the Jacquet integral of `f` for `λ₁ ⊗ λ₂` stabilizes to `z`, the swapped Jacquet
integral of `A f ∈ I(-s, π₂ ⊗ π₁)` for `λ₂ ⊗ λ₁` stabilizes to `z'`, and `z' = c⁻¹ z`. Here
`A` is the published `intertwiningInduced`, with the compact open cofinality of the Levi
supplied by `generalLeviCompactOpenCofinal`. -/
theorem satisfiesLocalCoefficientEquation_sourceEval_iff (s : ℂ)
    (hμ : IsModulusScaling (Nat.add_one_pos m) (Nat.add_one_pos n) abv μ)
    (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
    (f : sourceDomain abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ μ) (c : ℂ) :
    SatisfiesLocalCoefficientEquation m n ψ
        (pairRepresentation (Nat.add_one_pos m) (Nat.add_one_pos n) π₁ π₂)
        (pairFunctional ℓ₁ ℓ₂) (pairFunctional ℓ₁ ℓ₂) μ μJ μJ'
        (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) c ↔
      c ≠ 0 ∧ ∃ z z' : ℂ,
        HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μJ
          (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) z ∧
        HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μJ'
          (targetEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂
            (intertwiningInduced abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s
              (generalLeviCompactOpenCofinal F _) hπ₁ hπ₂ hμ f)) z' ∧
        z' = c⁻¹ * z := by
  have hA : HasIntertwiningIntegral (m + 1) (n + 1)
      (pairRepresentation (Nat.add_one_pos m) (Nat.add_one_pos n) π₁ π₂) μ
      (sourceEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val)
      (fun g => pairFlip.symm (targetEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s
        π₁ π₂ (intertwiningInduced abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s
          (generalLeviCompactOpenCofinal F _) hπ₁ hπ₂ hμ f) g)) :=
    fun g => hasIntegral_intertwiningInduced abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s
      (generalLeviCompactOpenCofinal F _) hπ₁ hπ₂ hμ f g
  have hswap := swappedJacquetIntegrand_pairFlip_symm m n ψ ℓ₁ ℓ₂
    (targetEval abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂
      (intertwiningInduced abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s
        (generalLeviCompactOpenCofinal F _) hπ₁ hπ₂ hμ f))
  constructor
  · rintro ⟨hc, A, z, z', hA', hz, hz', rfl⟩
    obtain rfl := hA'.unique (generalLeviCompactOpenCofinal F _)
      (isSmooth_pairRepresentation _ _ hπ₁ hπ₂) hA
    refine ⟨hc, z, c⁻¹ * z, hz, ?_, rfl⟩
    unfold HasSwappedJacquetIntegral at hz' ⊢
    rwa [hswap] at hz'
  · rintro ⟨hc, z, z', hz, hz', rfl⟩
    refine ⟨hc, _, z, c⁻¹ * z, hA, hz, ?_, rfl⟩
    unfold HasSwappedJacquetIntegral at hz' ⊢
    rwa [hswap]

end Literal

end Langlands.Shahidi
