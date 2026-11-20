import Langlands.Global.AdelicWavePacketCompletenessStatement

/-! # Reduction of the completeness of wave packets to four ingredients

Delorme 2023, proof of Theorem 7.9, split into four propositions:

* `SpectralWitnessStatement` (Delorme, Lemma 7.10 with the preliminary remark before it, from
  Bernstein 1988 and Delorme Proposition 3.5): let `W` be a family of rapidly decreasing
  functions whose orthogonal complement in `L²([G])` is stable under right translation by
  `G(𝔸)`; then a nonzero `L²` function orthogonal to `W` produces a nonzero automorphic form,
  with a unitary `A_G`-character and in `L²([G], σ_{[G]}^{-2m})` for some `m`, orthogonal to `W`;
* `WavePacketRapidDecayStatement` (Delorme, Proposition 5.4 and (2.10)): every wave packet `Θ`
  satisfies `Θ σ_{[G]}^m ∈ L²([G])` for every `m`;
* `WavePacketOrthogonalTranslationStatement` (Delorme, Theorem 6.1 = Lapid 2011, Theorem 2, and
  Lemma 6.2, with the intertwining property of Langlands' Theorem 7.2 (b) in Arthur 2005): the
  orthogonal complement of the wave packets is stable under right translation by `G(𝔸)`;
* `TemperedWavePacketVanishingStatement` (Delorme §7: Theorem 7.1, Proposition 7.8, Lemma 7.11
  and the end of the proof of Theorem 7.9, with Proposition 3.5 and Lemma 3.10 (ii)): such an automorphic form orthogonal to every wave packet
  is zero.

The theorem `wavePacketCompleteness_of_reduction` derives `WavePacketCompletenessStatement`
from the four. -/

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

/-- Delorme's logarithmic height on `[G] = G(F) \ G(𝔸)` (Delorme 2023, §2, (2.6) and the
definition of `σ` after (2.7)): `σ_{[G]}(y) = inf_{γ ∈ G(F)} (1 + log ‖γ g‖)` for
`y = G(F) g`, for the norm `‖g‖ = max(1, ‖g‖_ρ)` on `G(𝔸)`. Here `‖g‖_ρ` is the
Mœglin–Waldspurger height (I.2.2) of the matrix embedding `rho`, the normalized product over
all places of the maximum of the absolute values of the entries of `rho(g)` and `rho(g)⁻¹`
(`RepresentationGrowth.adelicSourceNorm`); it can be smaller than `1`. Since `max 1` and `log`
are monotone and continuous, the infimum equals `1 + log max(1, inf_{γ ∈ G(F)} ‖γ g‖_ρ)`, the
expression below. When `IsClosedSubgroup rho` holds, `max(1, ‖·‖_ρ)` is a norm on `G(𝔸)` in
the sense of Beuzart-Plessis (arXiv 1602.06538v2, Appendix A.1), which is how Delorme fixes his
norm; if moreover `N = 0`, then `G` is trivial and `σ_{[G]} = 1`. -/
def rationalLogHeight {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (y : RationalQuotient F G) : ℝ :=
  1 + Real.log (max 1 (⨅ q : rationalSubgroup F G,
    RepresentationGrowth.adelicSourceNorm F G rho ((q : AdelicGroupPoints F G) * y.out)))

/-- `Θ` is a wave packet of Eisenstein series in the sense of `WavePacketCompletenessStatement`:
`Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`, where `P = MU` is a parabolic
of `G` with presentation `r` and `P(𝔸)K = G(𝔸)`, `e` are coordinates on `X^*(P) ⊗ ℝ`,
`v j ∈ A^2_P`, the `c j` are smooth and compactly supported, and the `E j` are meromorphic with
domain of holomorphy `D ⊇ i𝔞_P^*` and agree with the Eisenstein series `E(v j, λ)` for `Re λ`
sufficiently regular. The data and conditions are exactly those quantified in the hypothesis of
`WavePacketCompletenessStatement`. -/
def IsWavePacket (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (Θ : AdelicGroupPoints F G → ℂ) :
    Prop :=
  ∃ (P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (_ : IsAffine P.X.left) (_ : IsAffine M.X.left) (_ : LocallyOfFiniteType M.X.hom)
    (_ : IsAffine U.X.left)
    (p : P ⟶ G) (_ : IsClosedImmersion p.hom.hom.left) (iU : U ⟶ P) (l : M ⟶ P)
    (_ : IsClosedImmersion (iU ≫ p).hom.hom.left)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
    (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    LeviSubgroup.IsGeometricUnipotentRadical iU ∧
    ∃ (hK : IsIwasawaCompact p K) (n : ℕ)
      (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ HasCompactSupport (c j)) ∧
      Set.range (imaginaryParameter F P) ⊆ D ∧
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) ∧
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) ∧
      Θ = fun g => ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g
        ∂(spectralMeasure n)

/-- Automorphic forms of Delorme's Lemma 7.10, in the weighted-`L²` form of the preliminary
remark before it: `Φ` is an automorphic form on `G(F) \ G(𝔸)` (Mœglin–Waldspurger I.2.17, for
the archimedean part of `K` and the matrix embedding `rho`), it transforms under a unitary
character of the split component `A_G`, `Φ(a g) = a^{iν} Φ(g)` with `ν ∈ X^*(G) ⊗ ℝ`, and
`Φ / σ_{[G]}^m ∈ L²([G])` for some `m`, that is `Φ ∈ L²([G], σ_{[G]}^{-2m} dx)`. -/
def IsLogSquareIntegrableAutomorphicForm (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (Φ : AdelicGroupPoints F G → ℂ) :
    Prop :=
  IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho Φ ∧
    (∃ ν : RealCharacterParameter F G,
      ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ g : AdelicGroupPoints F G,
        Φ (a * g) = parameterPower F G (imaginaryParameter F G ν) a * Φ g) ∧
    ∃ m : ℕ, MemLp (fun y : RationalQuotient F G =>
        Φ y.out / (rationalLogHeight F G rho y : ℂ) ^ m) 2
      (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar)

end Definitions

/-- Delorme 2023, Lemma 7.10, in the abstract form in which its proof (after Carmona–Delorme
1998, Lemma 11, Delorme's reference [10]) uses the wave packets, together with the preliminary
remark before it (Bernstein 1988,
the theorem of §3.2 with Cond(w), end of §3.5, and the key lemma p.686; Delorme, Proposition 3.5
and (2.10)). Let `W` be a family of
functions on `G(𝔸)` such that every `Θ ∈ W` is rapidly decreasing on `[G]` in the weighted `L²`
sense, `Θ σ_{[G]}^m ∈ L²([G])` for every `m`, and such that the orthogonal complement of `W` in
`L²([G])` is stable under right translation by `G(𝔸)`. If a function `f ∈ L²([G])` orthogonal
to `W` is not zero almost everywhere, there is an automorphic form `Φ` with a unitary
`A_G`-character and `Φ / σ_{[G]}^m ∈ L²([G])` for some `m`, not identically zero, such that
`∫_{[G]} Φ · conj Θ = 0` for every `Θ ∈ W`. -/
def SpectralWitnessStatement : Prop :=
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
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ W : Set (AdelicGroupPoints F G → ℂ),
      (∀ Θ ∈ W, ∀ m : ℕ, MemLp (fun y : RationalQuotient F G =>
        Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG) →
      (∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG →
        (∀ Θ ∈ W, ∫ y, f y * (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
        ∀ g : AdelicGroupPoints F G, ∀ Θ ∈ W,
          ∫ y, f (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g y) *
            (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG →
      (∀ Θ ∈ W, ∫ y, f y * (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
      ¬ f =ᵐ[μG] 0 →
      ∃ Φ : AdelicGroupPoints F G → ℂ,
        IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ ∧
          (∃ g, Φ g ≠ 0) ∧
          ∀ Θ ∈ W, ∫ y, Φ y.out * (starRingEnd ℂ) (Θ y.out) ∂μG = 0

/-- Wave packets are rapidly decreasing (Delorme 2023, Proposition 5.4: `Θ` lies in the
Harish-Chandra Schwartz space `𝒞([G])`, so `|Θ| ≪_m σ_{[G]}^{-m} Ξ^{[G]}` for every `m`;
with (2.10), `∫_{[G]} (1 + σ_{[G]})^{-d_G} (Ξ^{[G]})² < ∞`): for every wave packet `Θ` of
`WavePacketCompletenessStatement` and every `m`, `Θ σ_{[G]}^m ∈ L²([G])`. Packets of parabolics
not containing the given minimal parabolic `P₀` are right translates by rational elements of
packets of parabolics containing `P₀`, for a conjugate compact subgroup `γ K γ⁻¹` (see the
Markdown). -/
def WavePacketRapidDecayStatement : Prop :=
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
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
      ∀ m : ℕ, MemLp (fun y : RationalQuotient F G =>
        Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG

/-- The orthogonal complement of the wave packets is stable under right translation (Delorme
2023, Theorem 6.1 = Lapid 2011, Theorem 2, and Lemma 6.2, with the intertwining property of
Langlands' Theorem 7.2 (b) in Arthur 2005: for each parabolic, the closed span of its wave
packets is the closure of the image of a bounded `G(𝔸)`-equivariant map, on which right
translation acts through the induced representations). If `f ∈ L²([G])` is orthogonal to every
wave packet of `WavePacketCompletenessStatement`, then so is its right translate `y ↦ f(y g)`
for every `g ∈ G(𝔸)`. -/
def WavePacketOrthogonalTranslationStatement : Prop :=
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
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG →
      (∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
        ∫ y, f y * (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
      ∀ (g : AdelicGroupPoints F G) (Θ : AdelicGroupPoints F G → ℂ),
        IsWavePacket F G K rho hsmooth hcalc Θ →
        ∫ y, f (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g y) *
          (starRingEnd ℂ) (Θ y.out) ∂μG = 0

/-- Vanishing of tempered automorphic forms orthogonal to the wave packets (Delorme 2023, §7:
Theorem 7.1, Proposition 7.8, Lemma 7.11 and the end of the proof of Theorem 7.9, with
Lemma 3.10 (ii); temperedness from Proposition 3.5). Let `Φ` be an automorphic form on
`G(F) \ G(𝔸)` with a unitary `A_G`-character and `Φ / σ_{[G]}^m ∈ L²([G])` for some `m`. If
`∫_{[G]} Φ · conj Θ = 0` for every wave packet `Θ` of `WavePacketCompletenessStatement`, then
`Φ = 0`. -/
def TemperedWavePacketVanishingStatement : Prop :=
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
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ Φ : AdelicGroupPoints F G → ℂ,
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
      (∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
        ∫ y, Φ y.out * (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
      ∀ g : AdelicGroupPoints F G, Φ g = 0

/-- The four ingredients imply the completeness of wave packets (Delorme 2023, proof of
Theorem 7.9). -/
theorem wavePacketCompleteness_of_reduction (hW : SpectralWitnessStatement)
    (hS : WavePacketRapidDecayStatement) (hG : WavePacketOrthogonalTranslationStatement)
    (hV : TemperedWavePacketVanishingStatement) : WavePacketCompletenessStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho hP₀ μG f hf horth
  have horth' : ∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
      ∫ y, f y * (starRingEnd ℂ) (Θ y.out) ∂μG = 0 := by
    rintro Θ ⟨P, M, U, A, _, _, _, _, p, _, iU, l, _, a, r, _, _, _, hA, hT, hU, hK, n, e, k,
      v, c, E, D, hv, hc, hD, hE, hreg, rfl⟩
    exact horth P M U A p iU l a r hA hT hU hK e k v c E D hv hc hD hE hreg
  by_contra hne
  obtain ⟨Φ, hΦ, ⟨g, hg⟩, hΦW⟩ :=
    hW F G hred K rho hsmooth hcalc hKmax hrho hP₀
      {Θ | IsWavePacket F G K rho hsmooth hcalc Θ}
      (fun Θ hΘ => hS F G hred K rho hsmooth hcalc hKmax hrho hP₀ Θ hΘ)
      (fun f' hf' h' g' Θ hΘ => hG F G hred K rho hsmooth hcalc hKmax hrho hP₀ f' hf' h' g' Θ hΘ)
      f hf horth' hne
  exact hg (hV F G hred K rho hsmooth hcalc hKmax hrho hP₀ Φ hΦ hΦW g)

end Langlands.Global
