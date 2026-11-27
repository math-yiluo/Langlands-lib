import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet

/-! # Uniform moderate growth of Eisenstein series on compact sets of unitary parameters

Bernstein–Lapid 2024, the Corollary at the end of §8.6, with Lapid 2011, Proposition 6: for
`φ ∈ A^2_P` and `λ` in a compact subset of `i𝔞_P^*`, the continued Eisenstein series
`E_P(·, φ, λ)` are smooth functions on `G(F) \ G(𝔸)`, right invariant under one open subgroup
of `G(𝔸_f)`, all of whose derivatives are bounded by `M_u ‖g‖^R` with one exponent `R` and
constants `M_u` independent of `λ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- A family `f` of smooth left `G(F)`-invariant functions has **uniform moderate growth on
`S` with exponent `R` at level `L`**: every `f x` with `x ∈ S` is right invariant under `L`,
and for every element `u` of the enveloping algebra there is one constant `M` with
`|(u f x)(g)| ≤ M ‖g‖^R` for all `x ∈ S` and all `g ∈ G(𝔸)`, where `‖g‖` is the adelic norm
of `rho`. -/
def IsUniformGrowthFamily {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ) {Idx : Type}
    (f : Idx → FinitePlotSmoothRationalFunctions F G) (S : Set Idx) : Prop :=
  (∀ x ∈ S, IsFixedByFiniteSubgroup F G L (f x)) ∧
    ∀ u : AdelicEnvelopingAlgebra F G hsmooth, ∃ M : ℝ, ∀ x ∈ S, ∀ g : AdelicGroupPoints F G,
      ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc u (f x)).val g‖ ≤
        M * RepresentationGrowth.adelicSourceNorm F G rho g ^ R

/-- **Uniform moderate growth of Eisenstein series on compact sets of unitary parameters**
(Bernstein–Lapid 2024, Corollary in §8.6, with Lapid 2011, Proposition 6). The data and
hypotheses are those of `EisensteinUniformTemperednessStatement`: `φ ∈ A^2_P`, and `E` is
meromorphic in `λ` at each point `g` with one domain of holomorphy `D` containing the imaginary
parameters, and equal to the Eisenstein series `E(φ, λ)` for `Re λ` sufficiently regular. Let
`e : ℝⁿ ≃ X^*(P) ⊗ ℝ` be real linear coordinates and `C ⊆ ℝⁿ` compact. Then there are an open
subgroup `L ≤ G(𝔸_f)`, an exponent `R` and smooth left `G(F)`-invariant functions `f x` with
`f x = E(i e(x))` for `x ∈ C`, such that the family has uniform moderate growth on `C` with
exponent `R` at level `L` (`IsUniformGrowthFamily`). -/
def EisensteinUnitaryUniformGrowthStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        Set.range (imaginaryParameter F P) ⊆ D →
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          E lam = hK.eisensteinSeries φ lam) →
        ∀ (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (C : Set (Fin n → ℝ)),
          IsCompact C →
          ∃ (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ)
            (f : (Fin n → ℝ) → FinitePlotSmoothRationalFunctions F G),
            IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
            (∀ x ∈ C, evaluate F G (f x).val = E (imaginaryParameter F P (e x))) ∧
            IsUniformGrowthFamily rho hsmooth hcalc L R f C

end Langlands.Global
