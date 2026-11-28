import Langlands.Global.AdelicTruncatedEisensteinFamilyUniformAsymptoticsStatement
import Langlands.Global.ArthurTruncationL2Reduction
import Langlands.Global.ArthurTruncationIdempotenceProof

/-! # Truncated Eisenstein families: reduction to the asymptotic and square-integrability parts

`LocalTruncatedEisensteinFamilyUniformInnerProductStatement` asserts, for one maximal compact
subgroup `K` of `G(𝔸)`, three properties: Arthur's orthogonal projection property of the
truncation operators, Lapid's Proposition 1 for holomorphic families uniformly in the central
parameter, and the locally uniform square integrability of truncated families. The first holds
for every compact `K` with `P_0(𝔸)K = G(𝔸)`.

* `exists_isOrthogonalL2Extension_of_isIwasawaCompact`: for every compact `K` with
  `P_0(𝔸)K = G(𝔸)` and all reflection data, the norm-one and full-quotient truncations with
  respect to `K` extend to orthogonal projections on `L²` for sufficiently regular `T` (Arthur
  2005, Proposition 13.1 and the paragraph after its proof).
* `localTruncatedEisensteinFamilyUniformInnerProduct_of_asymptotics`:
  `LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement`, the second and third properties
  for one maximal compact `K`, implies `LocalTruncatedEisensteinFamilyUniformInnerProductStatement`.
  -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct CompactlySupported Classical

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- **Arthur 2005, Proposition 13.1 and the paragraph after its proof, for every compact Iwasawa
subgroup.** For every compact `K` with `P_0(𝔸)K = G(𝔸)`, all reflection data `D` and the
bijectivity `hρ`, there is `C` such that for every `T` with `β(T) > C` for all simple roots `β`
the norm-one truncation `Λ^T` on `G(F) \ G(𝔸)¹` and the full truncation on `G(F) \ G(𝔸)` extend
to orthogonal projections on `L²` that agree almost everywhere with pointwise truncation on
locally bounded measurable representatives. Idempotence is `iwasawaTruncationIdempotent`, the
pairing identity is `truncationSelfAdjoint`. -/
theorem exists_isOrthogonalL2Extension_of_isIwasawaCompact {F : Type u} [Field F]
    [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) :
    ∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
      IsOrthogonalL2Extension (normOneRationalQuotientHaarMeasure F G)
          (fun f q => normOneTruncation hG hi D hK hρ Tp
            (fun x => f (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x)) q.out) ∧
        IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
          (fun f q => truncation hG hi D hK hρ Tp
            (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out) := by
  obtain ⟨C₁, hC₁⟩ := iwasawaTruncationIdempotent F G T i ν hG hi hν D K hK hρ
  obtain ⟨C₂, hC₂⟩ := truncationSelfAdjoint F G T i ν hG hi hν D K hK hρ
  refine ⟨max C₁ C₂, fun Tp hTp => ?_⟩
  have h₁ : ∀ β ∈ simpleRelativeRoots i ν, C₁ < eval T β Tp :=
    fun β hβ => (le_max_left _ _).trans_lt (hTp β hβ)
  have h₂ : ∀ β ∈ simpleRelativeRoots i ν, C₂ < eval T β Tp :=
    fun β hβ => (le_max_right _ _).trans_lt (hTp β hβ)
  obtain ⟨hloc, hpair⟩ := hC₂ Tp h₂
  have hB : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      IsLocallyBoundedInvariant (rationalSubgroup F G) (truncation hG hi D hK hρ Tp φ) :=
    fun φ hφ => (hloc φ hφ).1
  have hI : ∀ φ, IsLocallyBoundedInvariant (rationalSubgroup F G) φ →
      truncation hG hi D hK hρ Tp (truncation hG hi D hK hρ Tp φ) =
        truncation hG hi D hK hρ Tp φ :=
    fun φ hφ => (hC₁ Tp h₁ φ hφ).2
  have hP : ∀ φ₁ φ₂ : AdelicGroupPoints F G → ℂ,
      IsLocallyBoundedInvariant (rationalSubgroup F G) φ₁ →
      Continuous φ₂ → (∀ g ∈ rationalSubgroup F G, ∀ x, φ₂ (g * x) = φ₂ x) →
      (∃ Cs : Set (AdelicGroupPoints F G), IsCompact Cs ∧
        ∀ x, φ₂ x ≠ 0 → ∃ g ∈ rationalSubgroup F G, g * x ∈ Cs) →
      Integrable (fun y : RationalQuotient F G =>
          φ₁ y.out * (starRingEnd ℂ) (truncation hG hi D hK hρ Tp φ₂ y.out))
        (rationalQuotientHaarMeasure F G) ∧
        ∫ y, truncation hG hi D hK hρ Tp φ₁ y.out * (starRingEnd ℂ) (φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) =
          ∫ y, φ₁ y.out * (starRingEnd ℂ) (truncation hG hi D hK hρ Tp φ₂ y.out)
            ∂(rationalQuotientHaarMeasure F G) := by
    intro φ₁ φ₂ hφ₁ hc hinv hcs
    obtain ⟨-, hint, heq⟩ := hpair φ₁ φ₂ hφ₁ hc hinv hcs
    exact ⟨hint, heq⟩
  exact ⟨isOrthogonalL2Extension_normOneTruncation hG hi D hK hρ Tp hν hB hI hP,
    isOrthogonalL2Extension_truncation hG hi D hK hρ Tp hB hI hP⟩

/-- **Reduction.** `LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement` implies
`LocalTruncatedEisensteinFamilyUniformInnerProductStatement`: the compact subgroup and the second
and third conjuncts are taken from the former, and the first conjunct holds for every compact
`K` with `P_0(𝔸)K = G(𝔸)` (`exists_isOrthogonalL2Extension_of_isIwasawaCompact`). -/
theorem localTruncatedEisensteinFamilyUniformInnerProduct_of_asymptotics
    (h : LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement) :
    LocalTruncatedEisensteinFamilyUniformInnerProductStatement := by
  intro F _ _ G _ _ T i _ ν hG hi hν
  obtain ⟨K, hKmax, hK₀, hK, hpos, hrest⟩ := h F G T i ν hG hi hν
  exact ⟨K, hKmax, hK₀, hK, hpos, fun D hρ hK₀' hK' =>
    ⟨exists_isOrthogonalL2Extension_of_isIwasawaCompact hG hi hν D hK₀' hρ, hrest D hρ hK₀' hK'⟩⟩

end Langlands.Global

