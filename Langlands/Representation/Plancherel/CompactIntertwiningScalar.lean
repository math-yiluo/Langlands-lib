import Langlands.Representation.Plancherel.CompactIntertwiningComposition
import Langlands.Representation.Plancherel.RationalUnramifiedScalarContinuation
import Langlands.Representation.Schur.RationalPoints

/-! # Extracting the scalar of an actual ambient intertwiner composite -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
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

/-- Restriction/extension conjugation respects the original scalar action on
ambient intertwining maps. -/
theorem compactIntertwiningOperator_smul
    (J : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation) (c : ℂ) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
      h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A (c • J) =
      c • compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A J := by
  apply LinearMap.ext
  intro f
  simp only [compactIntertwiningOperator, Representation.IntertwiningMap.toLinearMap_smul,
    LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

omit h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ in
/-- A scalar equation on the compact picture is exactly the same equation
for the original ambient intertwiner. -/
theorem compactIntertwiningOperator_scalar_iff
    (J : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation) (c : ℂ) :
    compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ χ A J = c • LinearMap.id ↔
      J = c • Representation.IntertwiningMap.id
        (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation := by
  rw [← compactIntertwiningOperator_id h₀ hU₀ hδ₀ K hK hP₀ hP₀K hr₀ ν hν χ A,
    ← compactIntertwiningOperator_smul h₀ hU₀ hδ₀ h₀ hU₀ hδ₀ K hK
      hP₀ hP₀ hP₀K hP₀K hr₀ hr₀ ν hν χ A]
  exact (compactIntertwiningOperator_injective h₀ hU₀ hδ₀ h₀ hU₀ hδ₀ K hK
    hP₀ hP₀ hP₀K hP₀K hr₀ hr₀ ν hν χ A).eq_iff

/-- The scalar of a pair of supplied ambient intertwiners is extracted
directly from their actual compact-picture composite. -/
def compactIntertwiningCompositionScalar
    (J₁₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (J₀₁ : (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation)
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) : ℂ :=
  endomorphismScalarCoefficient v ℓ
    ((compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ χ A J₀₁).comp
      (compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A J₁₀))

/-- The actual ambient composition and compact composition have identical
scalar equations, with no loss of the original maps or their normalization. -/
theorem compactIntertwiningComposition_scalar_iff
    (J₁₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (J₀₁ : (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation)
    (c : ℂ) :
    (compactIntertwiningOperator h₁ hU₁ hδ₁ K hP₁ hK hP₁K ν hν hr₁
      h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ χ A J₀₁).comp
      (compactIntertwiningOperator h₀ hU₀ hδ₀ K hP₀ hK hP₀K ν hν hr₀
        h₁ hU₁ hδ₁ hP₁ hP₁K hr₁ χ A J₁₀) = c • LinearMap.id ↔
      J₀₁.comp J₁₀ = c • Representation.IntertwiningMap.id
        (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation := by
  rw [← compactIntertwiningOperator_comp h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A
    h₀ hU₀ hδ₀ hP₀ hP₀K hr₀ J₁₀ J₀₁]
  exact compactIntertwiningOperator_scalar_iff h₀ hU₀ hδ₀ K hK hP₀ hP₀K hr₀
    ν hν χ A _ c

section Schur

variable [TopologicalSpace.SeparableSpace G]

/-- At an irreducible actual induced representation, published smooth Schur
identifies the ambient composite with its extracted scalar. Irreducibility
is a premise at this parameter, not a conclusion about all inductions. -/
theorem compactIntertwiningComposition_eq_extracted_scalar
    (hi : (UnramifiedLeviInduction h₀ hU₀ ν χ A).IsIrreducible)
    (J₁₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (J₀₁ : (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation)
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) :
    J₀₁.comp J₁₀ =
      compactIntertwiningCompositionScalar h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
        hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A J₁₀ J₀₁ v ℓ •
        Representation.IntertwiningMap.id
          (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation := by
  obtain ⟨c, hc, -⟩ := Langlands.Schur.separableSmooth_scalarEndomorphism
    (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation
    (UnramifiedLeviInduction h₀ hU₀ ν χ A).isSmooth hi (J₀₁.comp J₁₀)
  have he := (compactIntertwiningComposition_scalar_iff h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
    K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A J₁₀ J₀₁ c).mpr hc
  apply (compactIntertwiningComposition_scalar_iff h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
    K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A J₁₀ J₀₁ _).mp
  exact eq_scalarCoefficient_smul_id v ℓ hℓ _ ⟨c, he⟩

/-- The extracted scalar is independent of the normalized vector and
functional for these actual intertwiners at an irreducible parameter. -/
theorem compactIntertwiningCompositionScalar_independent
    (hi : (UnramifiedLeviInduction h₀ hU₀ ν χ A).IsIrreducible)
    (J₁₀ : (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation)
    (J₀₁ : (UnramifiedLeviInduction h₁ hU₁ ν χ A).representation.IntertwiningMap
      (UnramifiedLeviInduction h₀ hU₀ ν χ A).representation)
    (v w : CompactInductionPicture h₀ K A)
    (ℓ m : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ)
    (hℓ : ℓ v = 1) (hm : m w = 1) :
    compactIntertwiningCompositionScalar h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A J₁₀ J₀₁ v ℓ =
    compactIntertwiningCompositionScalar h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
      hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A J₁₀ J₀₁ w m := by
  have he := (compactIntertwiningComposition_scalar_iff h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
    K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A J₁₀ J₀₁ _).mpr
      (compactIntertwiningComposition_eq_extracted_scalar h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
        K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ A hi J₁₀ J₀₁ v ℓ hℓ)
  have hm' := congrArg (endomorphismScalarCoefficient w m) he
  exact (hm'.trans (endomorphismScalarCoefficient_smul_id w m hm _)).symm

end Schur

omit χ in
/-- Extract the pointwise scalar coefficient of a pair of parameter-dependent
ambient intertwiner families in the same fixed compact picture. -/
def compactIntertwiningCompositionScalarFamily
    (Ω : Set (unramifiedCharacters ν))
    (J₁₀ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation)
    (J₀₁ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation)
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) : Ω → ℂ :=
  fun χ => compactIntertwiningCompositionScalar h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν χ.val A (J₁₀ χ) (J₀₁ χ) v ℓ

omit χ in
/-- Rationality of the two actual compact intertwiner families supplies
a regular numerator and one denominator nonvanishing throughout the region
for their extracted composite coefficient. -/
theorem compactIntertwiningCompositionScalarFamily_numerator
    (Ω : Set (unramifiedCharacters ν))
    (J₁₀ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation)
    (J₀₁ : ∀ χ : Ω,
      (UnramifiedLeviInduction h₁ hU₁ ν χ.val A).representation.IntertwiningMap
        (UnramifiedLeviInduction h₀ hU₀ ν χ.val A).representation)
    (hJ₁₀ : IsRationalOperatorOn Ω
      (compactIntertwiningOperatorFamily h₀ hU₀ hδ₀ h₁ hU₁ hδ₁
        K hK hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν A Ω J₁₀))
    (hJ₀₁ : IsRationalOperatorOn Ω
      (compactIntertwiningOperatorFamily h₁ hU₁ hδ₁ h₀ hU₀ hδ₀
        K hK hP₁ hP₀ hP₁K hP₀K hr₁ hr₀ ν hν A Ω J₀₁))
    (v : CompactInductionPicture h₀ K A)
    (ℓ : CompactInductionPicture h₀ K A →ₗ[ℂ] ℂ) :
    ∃ a b : unramifiedRegularFunctions ν,
      (∀ χ : Ω, b.val χ.val ≠ 0) ∧
      ∀ χ : Ω, b.val χ.val *
        compactIntertwiningCompositionScalarFamily h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
          hP₀ hP₁ hP₀K hP₁K hr₀ hr₁ ν hν A Ω J₁₀ J₀₁ v ℓ χ =
        a.val χ.val :=
  scalarCoefficient_numerator v ℓ _ (hJ₀₁.comp hJ₁₀)

end Langlands.Plancherel
