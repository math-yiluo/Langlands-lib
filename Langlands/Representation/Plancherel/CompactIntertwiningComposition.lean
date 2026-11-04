import Langlands.Representation.Plancherel.CompactIntertwiningFamilies

/-! # Composition of rational families and actual compact intertwiners -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.Plancherel

universe uG uI uV uW uZ

namespace UnramifiedOperatorFamily

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {Ω : Set (unramifiedCharacters ν)}

/-- A finite sum of finite regular expansions still has a finite regular
expansion; no finite-dimensionality of the vector space is required. -/
theorem IsPolynomialOn.sum {ι : Type*} (s : Finset ι) {f : ι → Ω → V}
    (hf : ∀ i ∈ s, IsPolynomialOn Ω (f i)) :
    IsPolynomialOn Ω (fun χ => ∑ i ∈ s, f i χ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolynomialOn_const (ν := ν) (U := Ω) (0 : V)
  | @insert i s hi hs =>
      have htail := hs (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).add htail

/-- A varying polynomial operator sends a polynomial vector family to a
polynomial vector family. Only finitely many fixed-vector tests are needed
for each input expansion. -/
theorem IsPolynomialOperatorOn.apply {A : Ω → V →ₗ[ℂ] W}
    (hA : IsPolynomialOperatorOn Ω A) {f : Ω → V}
    (hf : IsPolynomialOn Ω f) :
    IsPolynomialOn Ω (fun χ => A χ (f χ)) := by
  obtain ⟨n, b, v, hf⟩ := hf
  have hsum := IsPolynomialOn.sum (Finset.univ : Finset (Fin n))
    (f := fun i χ => (b i).val χ.val • A χ (v i))
    (fun i _ => (hA (v i)).regular_smul (b i))
  convert hsum using 1
  funext χ
  rw [hf χ, map_sum]
  simp only [map_smul]

/-- Composition permits both operators to vary with the parameter. -/
theorem IsPolynomialOperatorOn.comp {A : Ω → V →ₗ[ℂ] W}
    {B : Ω → W →ₗ[ℂ] Z}
    (hB : IsPolynomialOperatorOn Ω B) (hA : IsPolynomialOperatorOn Ω A) :
    IsPolynomialOperatorOn Ω (fun χ => (B χ).comp (A χ)) :=
  fun v => hB.apply (hA v)

/-- The product of two denominators clears the composite family, uniformly
over every input vector. The carriers have independent universes. -/
theorem IsRationalOperatorOn.comp {A : Ω → V →ₗ[ℂ] W}
    {B : Ω → W →ₗ[ℂ] Z}
    (hB : IsRationalOperatorOn Ω B) (hA : IsRationalOperatorOn Ω A) :
    IsRationalOperatorOn Ω (fun χ => (B χ).comp (A χ)) := by
  obtain ⟨b, hb, hB⟩ := hB
  obtain ⟨a, ha, hA⟩ := hA
  refine ⟨b * a, fun χ => mul_ne_zero (hb χ) (ha χ), ?_⟩
  convert hB.comp hA using 1
  funext χ
  apply LinearMap.ext
  intro v
  simp only [Subalgebra.coe_mul, Pi.mul_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm]

end UnramifiedOperatorFamily

open Aubert.General Induction StandardIntertwining

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ P₂ M U₀ U₁ U₂ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (hδ₀ : IsUnimodularModulus U₀ hU₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (hδ₁ : IsUnimodularModulus U₁ hU₁)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP₀ : IsClosed (P₀ : Set G)) (hP₁ : IsClosed (P₁ : Set G))
  (hP₀K : ∀ g : G, ∃ p : P₀, ∃ k : K, g = (p : G) * (k : G))
  (hP₁K : ∀ g : G, ∃ p : P₁, ∃ k : K, g = (p : G) * (k : G))
  (hr₀ : Continuous h₀.projection) (hr₁ : Continuous h₁.projection)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (χ : unramifiedCharacters ν)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

omit χ in
/-- A parameter-dependent family of actual ambient intertwiners becomes a
family between fixed compact pictures, by the original restriction maps. -/
def compactIntertwiningOperatorFamily (Ω : Set (unramifiedCharacters ν))
    (J : ∀ χ : Ω,
      (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation) :
    Ω → CompactInductionPicture h₀ K A →ₗ[ℂ] CompactInductionPicture h₁ K A :=
  fun χ => compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
    h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ.val A (J χ)

/-- Compact conjugation retains the entire ambient intertwiner. In
particular, equality of compact operators loses no information. -/
theorem compactIntertwiningOperator_injective :
    Function.Injective
      (compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A) := by
  intro J L hJL
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply (unramifiedLeviInductionCompactEquiv
    h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁ χ A).injective
  have he := congrArg
    (fun T => T (unramifiedLeviInductionCompactEquiv
      h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ χ A f)) hJL
  simpa only [compactIntertwiningOperator, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using he

omit h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ in
/-- The identity ambient intertwiner is the identity on the fixed compact
picture. -/
theorem compactIntertwiningOperator_id :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ χ A
      (Representation.IntertwiningMap.id
        (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact (unramifiedLeviInductionCompactEquiv
    h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀ χ A).apply_symm_apply f

variable (h₂ : IsSemidirectDecomposition P₂ M U₂) (hU₂ : IsClosed (U₂ : Set G))
  (hδ₂ : IsUnimodularModulus U₂ hU₂) (hP₂ : IsClosed (P₂ : Set G))
  (hP₂K : ∀ g : G, ∃ p : P₂, ∃ k : K, g = (p : G) * (k : G))
  (hr₂ : Continuous h₂.projection)

/-- Conjugation by the actual restriction/extension equivalences respects
composition; the intermediate compact identification cancels exactly. -/
theorem compactIntertwiningOperator_comp
    (J₁₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (J₂₁ : (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂ ν χ A).representation) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ χ A (J₂₁.comp J₁₀) =
      (compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ χ A J₂₁).comp
      (compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A J₁₀) := by
  apply LinearMap.ext
  intro f
  simp only [compactIntertwiningOperator, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

/-- An actual ambient composition equation is equivalent to the compact
composition equation. This does not assert the integral factorization. -/
theorem compactIntertwiningOperator_comp_eq_iff
    (J₂₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂ ν χ A).representation)
    (J₁₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (J₂₁ : (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₂ hU₂ ν χ A).representation) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ χ A J₂₀ =
      (compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁
        h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ χ A J₂₁).comp
      (compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A J₁₀) ↔
      J₂₀ = J₂₁.comp J₁₀ := by
  rw [← compactIntertwiningOperator_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
    K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A
    h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ J₁₀ J₂₁]
  exact (compactIntertwiningOperator_injective h₀ hU₀ hδ₀ h₂ hU₂ hδ₂
    K hK hP₀ hP₂ hP₀K hP₂K hr₀ hr₂ ν hν χ A).eq_iff

omit χ in
/-- Family composition is the parameterwise composition of the actual
ambient maps, expressed on the fixed compact pictures. -/
theorem compactIntertwiningOperatorFamily_comp
    (Ω : Set (unramifiedCharacters ν))
    (J₁₀ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation)
    (J₂₁ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₂ hU₂ ν χ.val A).representation) :
    compactIntertwiningOperatorFamily h₀ hU₀ hδ₀ h₂ hU₂ hδ₂
        K hK hP₀ hP₂ hP₀K hP₂K hr₀ hr₂ ν hν A Ω
        (fun χ => (J₂₁ χ).comp (J₁₀ χ)) =
      fun χ =>
        (compactIntertwiningOperatorFamily h₁ hU₁ hδ₁ h₂ hU₂ hδ₂
          K hK hP₁ hP₂ hP₁K hP₂K hr₁ hr₂ ν hν A Ω J₂₁ χ).comp
        (compactIntertwiningOperatorFamily h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
          K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν A Ω J₁₀ χ) := by
  funext χ
  exact compactIntertwiningOperator_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
    K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ.val A
    h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ (J₁₀ χ) (J₂₁ χ)

omit χ in
/-- Rationality of actual compact intertwiner families is preserved by
composition, using the product of their whole-operator denominators. -/
theorem compactIntertwiningOperatorFamily_rational_comp
    (Ω : Set (unramifiedCharacters ν))
    (J₁₀ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation)
    (J₂₁ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₂ hU₂ ν χ.val A).representation)
    (hJ₁₀ : UnramifiedOperatorFamily.IsRationalOperatorOn Ω
      (compactIntertwiningOperatorFamily h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
        K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν A Ω J₁₀))
    (hJ₂₁ : UnramifiedOperatorFamily.IsRationalOperatorOn Ω
      (compactIntertwiningOperatorFamily h₁ hU₁ hδ₁ h₂ hU₂ hδ₂
        K hK hP₁ hP₂ hP₁K hP₂K hr₁ hr₂ ν hν A Ω J₂₁)) :
    UnramifiedOperatorFamily.IsRationalOperatorOn Ω
      (compactIntertwiningOperatorFamily h₀ hU₀ hδ₀ h₂ hU₂ hδ₂
        K hK hP₀ hP₂ hP₀K hP₂K hr₀ hr₂ ν hν A Ω
        (fun χ => (J₂₁ χ).comp (J₁₀ χ))) := by
  rw [compactIntertwiningOperatorFamily_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
    K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν A
    h₂ hU₂ hδ₂ hP₂ hP₂K hr₂ Ω J₁₀ J₂₁]
  exact hJ₂₁.comp hJ₁₀

end Langlands.Plancherel
