import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicWavePacketCompletenessReduction

/-! # Reduction of the translation stability of the orthogonal of the wave packets

`WavePacketOrthogonalTranslationStatement` (the orthogonal complement in `L²([G])` of the wave
packets is stable under right translation by `G(𝔸)`) follows from three propositions:

* `WavePacketConvolutionStatement` (Arthur 2005 p.34, Mœglin–Waldspurger II.1.5, IV.1.7 (*) and
  the finiteness theorem of I.2.17, with Bernstein–Lapid Theorem 2.3 and Lapid 2011
  Proposition 6): wave
  packets are left `G(F)`-invariant, and the right convolution of a wave packet by a continuous,
  compactly supported, left `K_∞`-finite and left `G(𝔸_f)`-smooth function is again a wave
  packet;
* `RightTranslationTestFunctionSeparationStatement` (right invariance of the measure on `[G]`,
  strong continuity of the right regular representation, Fubini's theorem and the Peter–Weyl
  theorem for `K_∞`): an `L²` function orthogonal to every such convolution of a left
  `G(F)`-invariant `Θ ∈ L²([G])` has all its right translates orthogonal to `Θ`;
* `WavePacketRapidDecayStatement` (Delorme 2023, Proposition 5.4), used only for `Θ ∈ L²([G])`.

The theorem `wavePacketOrthogonalTranslation_of_reduction` derives
`WavePacketOrthogonalTranslationStatement` from the three. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Definitions

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Test functions for right convolution: `φ` on `G(𝔸)` is continuous and compactly supported,
its left translates by the subgroup `Kinf` of `G(F_∞)` span a finite-dimensional space, and it
is invariant under left translation by an open subgroup of `G(𝔸_f)`. -/
def IsLeftFiniteTestFunction (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  Continuous φ ∧ HasCompactSupport φ ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kinf =>
      fun h : AdelicGroupPoints F G => φ (AdelicGroupPoints.ofInfinite F G k * h))) ∧
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
      ∀ l ∈ L, ∀ h : AdelicGroupPoints F G, φ (AdelicGroupPoints.ofFinite F G l * h) = φ h

end Definitions

/-- Wave packets are left `G(F)`-invariant and stable under right convolution by test functions
(Arthur 2005, p.34, and Mœglin–Waldspurger II.1.5 and IV.1.7 (*): `R(φ) E(v, λ) = E(I(λ, φ) v, λ)`
where the series converge, with the `λ`-dependent induced action
`I(λ, φ) v = ∫ φ(h) v(· h) e^{⟨λ, H_P(· h) − H_P(·)⟩} dh`; the `I(λ, φ) v_j` lie in one
finite-dimensional subspace of `A^2_P` for all `λ`, by the finiteness theorem quoted in MW I.2.17
(compare MW IV.1.3), with coefficients entire in `λ`; the meromorphic continuation of the
Eisenstein series of a basis of that space, holomorphic on `i𝔞_P^*`, is Bernstein–Lapid,
Theorem 2.3, with Lapid 2011, Proposition 6). For every wave packet `Θ` of
`WavePacketCompletenessStatement`, `Θ(γ g) = Θ(g)` for `γ ∈ G(F)`, and for every continuous,
compactly supported, left `K_∞`-finite function `φ` invariant under left translation by an open
subgroup of `G(𝔸_f)`, the function `x ↦ ∫_{G(𝔸)} φ(h) Θ(x h) dh` is again a wave packet. -/
def WavePacketConvolutionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    ∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
      IsLeftInvariantUnder F G (rationalSubgroup F G) Θ ∧
      ∀ φ : AdelicGroupPoints F G → ℂ,
        IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ →
        IsWavePacket F G K rho hsmooth hcalc (AdelicGroupPoints.rightConvolution F G φ Θ)

/-- Separation of right translates by test functions (right invariance of the measure on
`[G] = G(F) \ G(𝔸)`, `G(𝔸)` being unimodular; strong continuity of the right regular
representation on `L²([G])`; Fubini's theorem; density of the `K_∞`-finite continuous functions,
by the Peter–Weyl theorem for `K_∞`). Let `f ∈ L²([G])` and let `Θ` on `G(𝔸)` be left
`G(F)`-invariant with `Θ ∈ L²([G])`. If `f` is orthogonal to `R(φ)Θ` for every continuous,
compactly supported, left `K_∞`-finite function `φ` invariant under left translation by an open
subgroup of `G(𝔸_f)`, then every right translate `y ↦ f(y g)` of `f` is orthogonal to `Θ`. -/
def RightTranslationTestFunctionSeparationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG →
    ∀ Θ : AdelicGroupPoints F G → ℂ, IsLeftInvariantUnder F G (rationalSubgroup F G) Θ →
      MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG →
      (∀ φ : AdelicGroupPoints F G → ℂ,
        IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ →
        ∫ y, f y * (starRingEnd ℂ) (AdelicGroupPoints.rightConvolution F G φ Θ y.out) ∂μG = 0) →
      ∀ g : AdelicGroupPoints F G,
        ∫ y, f (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g y) *
          (starRingEnd ℂ) (Θ y.out) ∂μG = 0

/-- Convolution stability of the wave packets, separation by test functions and the square
integrability of wave packets imply that the orthogonal complement of the wave packets is stable
under right translation. -/
theorem wavePacketOrthogonalTranslation_of_reduction (hA : WavePacketConvolutionStatement)
    (hB : RightTranslationTestFunctionSeparationStatement) (hS : WavePacketRapidDecayStatement) :
    WavePacketOrthogonalTranslationStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho hP₀ μG f hf horth g Θ hΘ
  obtain ⟨hleft, hconv⟩ := hA F G hred K rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ
  have hL2 : MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG := by
    simpa using hS F G hred K rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ 0
  exact hB F G hred K hKmax f hf Θ hleft hL2
    (fun φ hφ => horth (AdelicGroupPoints.rightConvolution F G φ Θ) (hconv φ hφ)) g

end Langlands.Global
