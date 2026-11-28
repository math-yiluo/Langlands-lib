import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement
import Langlands.Global.AdelicWavePacketStandardChamber
import Langlands.Global.AdelicWavePacketWeightedExpansions
import Langlands.Global.LocalWavePacketStandardLimitAuxiliary

/-! # Weighted intertwining expansions for standard wave packets -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Module
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme RealTorusSpace AdelicGroupPoints ArthurTruncation
  Langlands.Analysis.Meromorphic Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

local notation "I" => ArthurTruncation.StandardIndex hG hi ν
local notation "P[" S "]" => Standard.parabolicScheme i ν (ArthurTruncation.StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "L[" S "]" => Standard.leviScheme i ν (ArthurTruncation.StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "U[" S "]" => Standard.unipotentScheme i ν (ArthurTruncation.StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "p[" S "]" => Standard.parabolicHom i ν (ArthurTruncation.StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "l[" S "]" => Standard.leviToParabolic i ν (ArthurTruncation.StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "u[" S "]" => Standard.unipotentToParabolic i ν (ArthurTruncation.StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)

/-- Common meromorphic coefficients for the weighted intertwining expansions of a standard
packet into every standard parabolic. -/
def StandardWeightedIntertwiningExpansionsStatement : Prop :=
  IntertwiningSquareIntegrableExpansionStatement →
  ∀ (D : RelativeRootReflectionData i) (J : I)
    (A : I → CommGroupScheme (Spec (CommRingCat.of F))) (a : ∀ S : I, (A S).toGrp ⟶ L[S])
    (r : ∀ S : I, ParabolicRootPresentation p[S] l[S] (a S))
    [Mono (r J).data.i.hom.hom.left] [Fintype (relativeWeylGroup (r J).data.i)]
    [Mono (CommGroupScheme.groupHom (r J).data.f).hom.hom.left]
    (hA : IsSplitTorus (A J).toGrp) (hT : IsSplitTorus (r J).data.T.toGrp)
    (_hcompare : ∀ R : ℝ, ∃ R' : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R' lam →
      (r J).IsRegularParameter hA hT R lam)
    (_hU : ∀ S : I, LeviSubgroup.IsGeometricUnipotentRadical u[S])
    (_hmul : ∀ S : I, IsIso (subgroupMultiplication l[S] u[S]))
    (π : ∀ S : I, P[S] ⟶ L[S]) (_hπ : ∀ S, l[S] ≫ π S = 𝟙 L[S])
    {K : Subgroup (AdelicGroupPoints F G)} (hK : ∀ S : I, IsIwasawaCompact p[S] K)
    (_hKmax : IsMaximalCompactSubgroup F G K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (_hρ : IsClosedSubgroup rho)
    {k q : ℕ} (v : Fin k → Fin q → AdelicGroupPoints F G → ℂ)
    (b : Fin k → Fin q → ComplexCharacterParameter F P[J] → ℂ)
    (_hv : ∀ j l₀, IsSquareIntegrableInducedForm K (hK J).isCompact rho hsmooth hcalc p[J] u[J] l[J] (v j l₀))
    (_hb : ∀ j l₀, IsMeromorphicInCoordinatesOn (b j l₀) univ),
    ∃ (n : I → ℕ)
      (w : ∀ S : I, Fin (n S) → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : ∀ S : I, Fin (n S) → (L[S] ⟶ L[J])),
      (∀ S t, IsWeylConjugation p[J] l[J] p[S] l[S] (w S t) (cw S t)) ∧
      (∀ S, Function.Injective (fun t => weylParameter l[J] (cw S t) (π S))) ∧
      (∀ S, ∀ σ ∈ weylParameterSet p[J] l[J] p[S] l[S] (π S),
        ∃ t, weylParameter l[J] (cw S t) (π S) = σ) ∧
      ∃ (m : ℕ) (ψ : ∀ S : I, Fin (n S) → Fin k → Fin m → AdelicGroupPoints F G → ℂ)
        (coeff : ∀ S : I, Fin (n S) → Fin k → Fin m → ComplexCharacterParameter F P[J] → ℂ)
        (DM : Set (ComplexCharacterParameter F P[J])),
        (∀ S t j a₀, IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
          p[S] u[S] l[S] (ψ S t j a₀)) ∧
        range (imaginaryParameter F P[J]) ⊆ DM ∧
        (∀ S t j a₀, IsMeromorphicInCoordinatesOn (coeff S t j a₀) DM) ∧
        ∀ S t j, ∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
          ∑ l₀, b j l₀ lam * (hK J).intertwiningOperator (hK S) u[J] l[J] u[S]
            (cw S t) (π S) (w S t) (v j l₀) lam g =
          ∑ a₀, coeff S t j a₀ lam * ψ S t j a₀ g

set_option maxHeartbeats 1000000 in
/-- Apply the finite weighted expansion lemma to the actual Weyl representatives. -/
theorem exists_allStandardWeightedIntertwiningExpansions :
    StandardWeightedIntertwiningExpansionsStatement (ν := ν) hG hi := by
  intro hExp D J A a r _ _ _ hA hT hcompare hU hmul π hπ K hK hKmax N d
    rho hsmooth hcalc hρ k q v b hv hb
  classical
  choose n w cw hw hinj hsurj using
    fun S : I => exists_weylParameterEnumeration (p' := p[S]) (l' := l[S])
      (r J) (r S).isCompatible.levi (π := π J) (hπ J) (π' := π S) (hπ S)
  let X := ComplexCharacterParameter F P[J]
  let Y := AdelicGroupPoints F G
  let Q := Σ S : I, Fin (n S) × Fin k
  let Pr (p : Q) (φ : Y → ℂ) : Prop :=
    IsSquareIntegrableInducedForm K (hK p.1).isCompact rho hsmooth hcalc p[p.1] u[p.1] l[p.1] φ
  let Mv (p : Q) (l₀ : Fin q) : X → Y → ℂ :=
    (hK J).intertwiningOperator (hK p.1) u[J] l[J] u[p.1] (cw p.1 p.2.1)
      (π p.1) (w p.1 p.2.1) (v p.2.2 l₀)
  let reg : ℝ → X → Prop := IsStandardRegularParameter D J.roots
  let : FiniteDimensional ℂ X := finiteDimensional_complexCharacterParameter (r J) hG
  let : Fintype Q := inferInstanceAs (Fintype (Σ S : I, Fin (n S) × Fin k))
  have hSingle (p : Q) (l₀ : Fin q) :
      ∃ (m : ℕ) (ψ : Fin m → Y → ℂ) (coeff : Fin m → X → ℂ) (DM : Set X),
        (∀ j, Pr p (ψ j)) ∧ range (imaginaryParameter F P[J]) ⊆ DM ∧
        (∀ j, IsMeromorphicInCoordinatesOn (coeff j) DM) ∧
        ∃ R : ℝ, ∀ lam, reg R lam → ∀ g, Mv p l₀ lam g = ∑ j, coeff j lam * ψ j g := by
    obtain ⟨m, ψ, coeff, DM, hψ, hDM, hcoeff, R, hR⟩ :=
      hExp F G P[J] L[J] U[J] P[p.1] L[p.1] U[p.1] (A J) (A p.1)
        p[J] u[J] l[J] (a J) (r J) hA hT p[p.1] u[p.1] l[p.1] (a p.1) (r p.1) (π p.1)
        (w p.1 p.2.1) (cw p.1 p.2.1) hG (hU J) (hU p.1) (hmul p.1)
        (hπ p.1) (hw p.1 p.2.1) K (hK J) (hK p.1) rho hsmooth hcalc
        (v p.2.2 l₀) hKmax hρ (hv p.2.2 l₀)
    obtain ⟨R', hR'⟩ := hcompare R
    exact ⟨m, ψ, coeff, DM, hψ, hDM, hcoeff, R', fun lam hlam => hR lam (hR' lam hlam)⟩
  obtain ⟨m, ψ, coeff, DM, hψ, hDM, hcoeff, hEq⟩ := wavePacketWeightedExpansions
    (range (imaginaryParameter F P[J])) Pr reg (fun p => b p.2.2) Mv
    (fun p => zero_isSquareIntegrableInducedForm u[p.1] l[p.1] (hK p.1) rho hsmooth hcalc)
    (fun {_ _} h {_} hR α hα hαJ => h.trans_lt (hR α hα hαJ)) (fun p => hb p.2.2) hSingle
  exact ⟨n, w, cw, hw, hinj, hsurj, m, fun S t j => ψ ⟨S, t, j⟩,
    fun S t j => coeff ⟨S, t, j⟩, DM, fun S t j => hψ ⟨S, t, j⟩,
    hDM, fun S t j => hcoeff ⟨S, t, j⟩, fun S t j => hEq ⟨S, t, j⟩⟩

end Langlands.Global
