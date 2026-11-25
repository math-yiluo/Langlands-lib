import Langlands.Global.AdelicWavePacketCompletenessReduction
import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport

/-! # Reduction of `TemperedWavePacketVanishingStatement` to three ingredients

Delorme 2023, end of the proof of Theorem 7.9 (after Lemma 7.10), split along the weak constant
terms of Definition 3.7:

* `MinimalParabolicStandardFamilyStatement` (structure theory): the given minimal parabolic is the
  minimal standard parabolic `P_∅` of a compatible family of standard parabolics;
* `WavePacketWeakConstantTermOrthogonalityStatement` (Delorme §§4–7: Theorem 7.1, Proposition 7.8,
  Lemma 7.11 and the Fourier analysis on `A_G` at the end of the proof of Theorem 7.9): if an
  automorphic form of Lemma 7.10 is orthogonal to every wave packet, then each of its weak constant
  terms `Φ_P^w` satisfies the defining condition of `𝒜^{temp,c}_P(G)`: its pairing with every
  `φ ∈ A^2_P` over `[G]_P^1` vanishes, translated by every point of `𝔄_P`;
* `TemperedWeakConstantTermVanishingStatement` (Delorme §3: Proposition 3.5, Proposition 3.6,
  Definition 3.7, Lemma 3.8 and Lemma 3.10 (ii)): such an automorphic form whose weak constant
  terms all satisfy that condition is zero.

The theorem `temperedWavePacketVanishing_of_reduction` derives
`TemperedWavePacketVanishingStatement` from the three. The first is proved here
(`minimalParabolicStandardFamily`), so `temperedWavePacketVanishing_of_weakConstantTerms` derives
the target from the other two. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- The index `J = ∅` of the minimal standard parabolic `P₀ = P_∅` of the family. -/
def bot : StandardIndex F G 𝓕.i 𝓕.ν := ⟨∅, Set.empty_subset _⟩

section WeakConstantTerm

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

/-- Delorme 2023, (3.2): a finite decomposition `ψ = ∑_{λ ∈ s} c λ` of a function on
`U(𝔸) M(F) \ G(𝔸)` into automorphic functions on `U(𝔸) M(F) \ G(𝔸)` with normalized generalized
exponents `λ ∈ 𝔞_{P,ℂ}^*`: `c λ (a g) = a^{λ + ρ_P} p_g(H_P(a))` for `a ∈ 𝔄_P`, with `p_g` a
polynomial of degree bounded independently of `g` (`HasExponent`). The exponents are distinct,
being the elements of a finite set. Unlike
`IsExponentDecomposition`, no cuspidality is required. -/
structure IsAutomorphicExponentDecomposition (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (ψ : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ) : Prop where
  sum_eq : ψ = ∑ lam ∈ s, c lam
  automorphic : ∀ lam ∈ s, 𝓕.IsAutomorphicOn hsmooth Kinf rho J (c lam)
  exponent : ∀ lam ∈ s, 𝓕.HasExponent J lam (c lam)

/-- The sum of the components of a decomposition whose normalized exponents are unitary,
`Re λ = 0`. -/
def unitaryExponentSum (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  open Classical in
  ∑ lam ∈ s.filter (fun lam => parameterRealPart F (𝓕.P J) lam = 0), c lam

/-- `ψ = φ_P^w` is the weak constant term of `φ` along the standard parabolic `P = P_J`
(Delorme 2023, Definition 3.7): the sum of the terms with unitary exponents in a decomposition
(3.2) of the constant term `φ_P`. -/
def IsWeakConstantTerm (J : StandardIndex F G 𝓕.i 𝓕.ν) (φ ψ : AdelicGroupPoints F G → ℂ) :
    Prop :=
  ∃ (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ),
    𝓕.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (𝓕.constantTerm J φ) s c ∧
      ψ = 𝓕.unitaryExponentSum J s c

end WeakConstantTerm

section Orthogonality

variable (K : Subgroup (AdelicGroupPoints F G))
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))

/-- The integrand `(k, m) ↦ φ(x m k) conj ψ(x m k)` on `K × M(F) \ M(𝔸)^1`, at the chosen
representative of `m`, of the pairing `(φ, ψ)^X_P` of Delorme 2023, (3.7), at `x = exp_P X ∈ 𝔄_P`,
without its nonzero factor `e^{-2ρ_P(X)}`. -/
def squareIntegrablePairingIntegrand (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (x : AdelicGroupPoints F (𝓕.P J)) (φ ψ : AdelicGroupPoints F G → ℂ) :
    K × NormOneRationalQuotient F (𝓕.M J) → ℂ :=
  fun z =>
    φ (map F (𝓕.P J) G (𝓕.p J) x *
        map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
          ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (z.1 : AdelicGroupPoints F G)) *
      starRingEnd ℂ (ψ (map F (𝓕.P J) G (𝓕.p J) x *
        map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
          ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (z.1 : AdelicGroupPoints F G)))

/-- The measure `dk dm` on `K × M(F) \ M(𝔸)^1`: the Haar probability measure of `K` times the
quotient Haar measure. -/
def squareIntegrablePairingMeasure (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    Measure (K × NormOneRationalQuotient F (𝓕.M J)) :=
  (compactHaarProbability F G K hKc).prod (normOneRationalQuotientHaarMeasure F (𝓕.M J))

/-- The condition defining `𝒜^{temp,c}_P(G)` in Delorme 2023, after (3.7): for every
`φ ∈ A^2_P` (for `K`, `rho`, `hsmooth`) and every `x ∈ 𝔄_P`, the integral
`∫_K ∫_{M(F) \ M(𝔸)^1} φ(x m k) conj ψ(x m k) dm dk` converges absolutely and vanishes. -/
def IsSquareIntegrableOrthogonal {d N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (ψ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ φ : AdelicGroupPoints F G → ℂ,
    IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ →
    ∀ x ∈ 𝓕.positiveSplitComponent J,
      Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ ψ)
          (𝓕.squareIntegrablePairingMeasure K hKc J) ∧
        ∫ z, 𝓕.squareIntegrablePairingIntegrand K J x φ ψ z
          ∂(𝓕.squareIntegrablePairingMeasure K hKc J) = 0

end Orthogonality

end StandardParabolicFamily

/-- Every minimal parabolic subgroup of a connected reductive group over a number field is the
minimal standard parabolic `P_∅` of a compatible family of standard parabolics (Borel–Tits). The
equality is of all-test images. In the Library, the parabolic of a generic cocharacter of a
maximal split torus is minimal (`GroupScheme.genericMinimalParabolic`), any two minimal
parabolics are conjugate by a rational point (`GroupScheme.minimalParabolicConjugacy`), and
`StandardParabolicFamily.ofMaximalSplitTorus` builds a family from a maximal split torus and a
generic cocharacter. -/
def MinimalParabolicStandardFamilyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
      (_ : IsClosedImmersion p₀.hom.hom.left),
      IsMinimalParabolicSubgroup p₀ →
      ∃ 𝓕 : StandardParabolicFamily F G,
        SubgroupFunctor.range (𝓕.p 𝓕.bot) = SubgroupFunctor.range p₀

/-- Delorme 2023, §§4–7: Theorem 7.1, the results 7.2–7.7, Proposition 7.8, Lemma 7.11 and the
end of the proof of Theorem 7.9 (the Fourier analysis on `A_G` and the conclusion
`Φ_{P,0,μ} ∈ 𝒜^{temp,c}_P(G)`). Let `Φ` be an automorphic form of Lemma 7.10 (a unitary
`A_G`-character and `Φ / σ_{[G]}^m ∈ L²([G])`) with `∫_{[G]} Φ · conj Θ = 0` for every wave
packet `Θ`. Then for every compatible family of standard parabolics whose minimal member `P_∅`
satisfies `P_∅(𝔸) K = G(𝔸)`, every weak constant term `ψ = Φ_P^w` of `Φ` along a standard
parabolic `P` satisfies the condition defining `𝒜^{temp,c}_P(G)`. -/
def WavePacketWeakConstantTermOrthogonalityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K),
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ Φ : AdelicGroupPoints F G → ℂ,
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
      (∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
        ∫ y, Φ y.out * (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
      ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
        𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
        𝓕.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ

/-- Delorme 2023, §3: Proposition 3.5 (with the preliminary remark after Theorem 7.9, the form is
tempered), Proposition 3.6 (the exponents of its constant terms are subunitary), Definition 3.7,
Lemma 3.8 (transitivity of weak constant terms) and Lemma 3.10 (ii). Let `Φ` be an automorphic
form of Lemma 7.10 and fix a compatible family of standard parabolics whose minimal member
`P_∅` satisfies `P_∅(𝔸) K = G(𝔸)`. If every weak constant term of `Φ` along every standard
parabolic `P` satisfies the condition defining `𝒜^{temp,c}_P(G)`, then `Φ = 0`. -/
def TemperedWeakConstantTermVanishingStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
      (∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
        𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
        𝓕.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc J ψ) →
      ∀ g : AdelicGroupPoints F G, Φ g = 0

/-- The three ingredients imply `TemperedWavePacketVanishingStatement` (Delorme 2023, end of the
proof of Theorem 7.9). -/
theorem temperedWavePacketVanishing_of_reduction
    (hS : MinimalParabolicStandardFamilyStatement)
    (hO : WavePacketWeakConstantTermOrthogonalityStatement)
    (hV : TemperedWeakConstantTermVanishingStatement) :
    TemperedWavePacketVanishingStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho hP₀ μG Φ hΦ horth g
  obtain ⟨P₀, hP₀aff, p₀, hp₀, hmin, hK₀⟩ := hP₀
  obtain ⟨𝓕, h𝓕⟩ := hS F G hred P₀ hP₀aff p₀ hp₀ hmin
  have hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K := hK₀.of_range_eq h𝓕.symm
  exact hV F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ
    (hO F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ horth) g

/-- `MinimalParabolicStandardFamilyStatement` holds. Take the maximal split torus `T`, the generic
cocharacter `ν` and the minimal standard parabolic `P_∅(T, ν)` of the published Siegel setup
(`siegelAlgebraicSetupExistence`), conjugate `P_∅(T, ν)` onto the given minimal parabolic by a
rational point `g` (`minimalParabolicConjugacy`), and build the standard family of the conjugated
torus `Int(g) ∘ T` with the same `ν` (`ofMaximalSplitTorus`). -/
theorem minimalParabolicStandardFamily : MinimalParabolicStandardFamilyStatement := by
  intro F _ _ G _ _ _ hG P₀ _ p₀ _ hmin
  obtain ⟨T, i, ν, T₀, j, hS⟩ := AdelicSiegelFactors.siegelAlgebraicSetupExistence.{0} F G hG
  have hi : IsMaximalSplitTorus i := hS.1
  have hν : IsGenericCocharacter i ν := hS.2.1
  have hstd : IsMinimalParabolicSubgroup (Standard.parabolicHom i ν ∅) := hS.2.2.1
  obtain ⟨g, e, he⟩ := minimalParabolicConjugacy.{0} F G hG _ _ _ p₀ hstd hmin
  let E := G.innerIso g
  let 𝓕 := StandardParabolicFamily.ofMaximalSplitTorus hG (i ≫ E.hom) (hi.comp_iso E) ν
    ((isGenericCocharacter_comp_ambientIso_iff i ν E).mpr hν)
  refine ⟨𝓕, ?_⟩
  rw [(𝓕.isCompatible 𝓕.bot).parabolic_eq]
  change standardParabolic (i ≫ E.hom) ν ∅ = _
  rw [standardParabolic_comp_ambientIso, ← (Standard.isRepresentedBy_parabolicHom i ν ∅).2,
    ← SubgroupFunctor.range_comp_iso, he, SubgroupFunctor.range_iso_comp]

/-- The two remaining ingredients imply `TemperedWavePacketVanishingStatement`. -/
theorem temperedWavePacketVanishing_of_weakConstantTerms
    (hO : WavePacketWeakConstantTermOrthogonalityStatement)
    (hV : TemperedWeakConstantTermVanishingStatement) :
    TemperedWavePacketVanishingStatement :=
  temperedWavePacketVanishing_of_reduction minimalParabolicStandardFamily hO hV

end Langlands.Global
