import Langlands.Global.RankinSelberg.RealAdjacentCanonicalChamber

/-! # Spanning the real canonical values by split Godement monomial coefficients -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapCanonicalSpan

open ArchimedeanLocal
open Langlands.Archimedean Langlands.Archimedean.GramFormula Langlands.Archimedean.PartialJacquet
open RealJacquet (realAdjacentGodementCoefficient realColumnProduct characterList_succ
  realStandardKFinite_characterList sectionValue_finset_sum columnGaussianMonomial leadingExponents
  gaussianMonomial_eq_realColumnProduct gaussianPolynomial_sum_monomials)
open RealGodement (canonicalJacquetMap canonicalJacquetMap_agrees realSpectralChamber
  isStrictlyDominant_characterList sectionValue gaussianSections realGodementGaussianSpanning
  gaussianSection_mem_kFinite realGodementSchwartzJoint additiveJacquetIntegral
  realGodementCanonicalModel)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "G" => Langlands.GeneralLinear (r + 2) ℝ

/-- The split Godement coefficients of monomial square Gaussian tests attached to the tail of an
inducing parameter: functions of the uniform model of the larger character list that are Godement
coefficients of a separated test whose square factor is a Gaussian monomial, over values of the
smaller canonical map. -/
def monomialSplitGenerators (D : RealQuotientMeasureData r) (a : ℝˣ) (P : Fin (r + 2) → Fin 2)
    (Z : Fin (r + 2) → ℂ) : Set (G → ℂ) :=
  {W | W ∈ realUniformWhittakerModel (r + 1) (RealGodementProfiles.characterList P Z) (-a) ∧
    ∃ (f : Automorphic.realStandardKFinite (r + 1)
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z)))
      (d : Coordinates (r + 1) (r + 1) →₀ ℕ) (c₀ : ℂ) (φ : 𝓢(Fin (r + 1) → ℝ, ℂ)),
      W = realAdjacentGodementCoefficient D a
        (realColumnProduct (gaussianPolynomial (MvPolynomial.monomial d c₀)) φ)
        (canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) f)
        (RealJacquetFrobenius.charData (P 0) (Z 0))}

/-- In the Godement convergence region of a strict chamber, every value of the larger canonical
map lies in the span of the split Godement monomial coefficients. -/
theorem canonicalJacquetMap_mem_span_monomialSplitGenerators (D : RealQuotientMeasureData r)
    (a : ℝˣ) (P : Fin (r + 2) → Fin 2) (Z : Fin (r + 2) → ℂ)
    (hZ : Z ∈ realSpectralChamber (r + 1))
    (hc : ∀ i : Fin (r + 1), ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z))) (r + 1) i ≤
      (RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re + (((r + 1 : ℕ) : ℝ) + 1) / 2)
    (F : Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z)) :
    canonicalJacquetMap a P Z F ∈ Submodule.span ℂ (monomialSplitGenerators D a P Z) := by
  classical
  let μ := D.groupHaar
  have : μ.IsHaarMeasure := D.groupHaar_isHaar
  let c := RealJacquetFrobenius.charData (P 0) (Z 0)
  let ds := RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z)
  have hlist := characterList_succ P Z
  let V := Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z)
  have hV : V = kFiniteFunctions (principalSeries ℝ (r + 2)
      (realPositionCharacter (RealBlock.character c :: ds))) (unitaryCompact ℝ (r + 2)) := by
    change Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z) = _
    rw [realStandardKFinite_characterList, hlist]
  have hspan := realGodementGaussianSpanning (r + 1) μ c ds hc
  have hZt : Fin.tail Z ∈ realSpectralChamber r := fun i => hZ i.succ
  have hDom : IsStrictlyDominant (realPositionExponent (RealBlock.character c :: ds)) (r + 1) := by
    have h := isStrictlyDominant_characterList P hZ
    rwa [hlist] at h
  let J := canonicalJacquetMap a P Z
  let S := Submodule.span ℂ (monomialSplitGenerators D a P Z)
  let T := (S.comap J).map V.subtype
  have hgen : gaussianSections μ c ds ⊆ T := by
    rintro _ ⟨Q, f, hf, rfl⟩
    have hfps : f ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds) := hf.1
    have hft : f ∈ Automorphic.realStandardKFinite (r + 1) ds := by
      rw [realStandardKFinite_characterList]
      exact hf
    let U := canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) ⟨f, hft⟩
    have hU : U = additiveJacquetIntegral a f :=
      canonicalJacquetMap_agrees a (Fin.tail P) hZt ⟨f, hft⟩
    let sect (u : Coordinates (r + 1) (r + 1 + 1) →₀ ℕ) : G → ℂ :=
      sectionValue μ c f (gaussianPolynomial (MvPolynomial.monomial u (Q.coeff u)))
    have hmem (u : Coordinates (r + 1) (r + 1 + 1) →₀ ℕ) : sect u ∈ V := by
      rw [hV]
      exact gaussianSection_mem_kFinite μ c ds hfps hc _
    have hQ : sectionValue μ c f (gaussianPolynomial Q) ∈ V := by
      rw [hV]
      exact gaussianSection_mem_kFinite μ c ds hfps hc _
    refine ⟨⟨_, hQ⟩, ?_, rfl⟩
    have hdecomp : (⟨_, hQ⟩ : V) = ∑ u ∈ Q.support, ⟨sect u, hmem u⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      rw [gaussianPolynomial_sum_monomials Q]
      exact sectionValue_finset_sum Q.support μ c ds hfps hc _
    change J ⟨_, hQ⟩ ∈ S
    rw [hdecomp, map_sum]
    refine S.sum_mem fun u _ => Submodule.subset_span ⟨Submodule.mem_iSup_of_mem J
      (Submodule.mem_iSup_of_mem (realGodementCanonicalModel (r + 1) a P Z) ⟨_, rfl⟩), ?_⟩
    refine ⟨⟨f, hft⟩, leadingExponents u, Q.coeff u,
      columnGaussianMonomial fun i => u (i, Fin.last (r + 1)), ?_⟩
    rw [← gaussianMonomial_eq_realColumnProduct]
    funext g
    change canonicalJacquetMap a P Z ⟨sect u, hmem u⟩ g = _
    rw [canonicalJacquetMap_agrees a P hZ]
    have hjoint := (realGodementSchwartzJoint r D a c ds f hfps hDom hc
      (gaussianPolynomial (MvPolynomial.monomial u (Q.coeff u))) g).2
    change additiveJacquetIntegral a (sectionValue μ c f _) g = _
    rw [hjoint]
    change _ = realAdjacentGodementCoefficient D a _ U c g
    rw [hU]
    rfl
  have hle : Submodule.span ℂ (gaussianSections μ c ds) ≤ T := Submodule.span_le.mpr hgen
  have hF : F.val ∈ T := hle (by rw [hspan, ← hV]; exact F.2)
  obtain ⟨v, hv, he⟩ := hF
  have hvF : v = F := Subtype.ext he
  rw [← hvF]
  exact hv

end Langlands.Global.RankinSelbergGlobal.RealGapCanonicalSpan
