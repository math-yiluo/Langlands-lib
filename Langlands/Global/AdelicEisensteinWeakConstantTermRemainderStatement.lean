import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.SimpleRootBoxCompact
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # The remainder of the weak constant term of Eisenstein series: exponents on cones

Delorme 2023, §4.1, (4.3) and (4.4), with the bounds used in the proofs of Lemmas 5.1 and 5.3:
the constant term `E_Q` of the Eisenstein series of `φ ∈ A^2_P` along a proper standard
parabolic `Q` is the sum of its weak constant term `E^w_Q`, a finite sum of smooth multiples of
functions transforming under the imaginary parameters of `Q`, and of a remainder
`E^-_Q = E_Q − E^w_Q`. The remainder has a unitary central character, satisfies the polynomial
bound (5.1) on Siegel sets, and its exponents along the split component `𝔄_Q` have strictly
negative real parts on every cone `α(Y) ≥ δ‖Y‖` (`α ∈ Δ \ J`) of `𝔞_Q`, with multiplicities
bounded uniformly for `λ` in a compact subset of `i𝔞_P^*` (Lapid 2011, (13), Lemma 6 and
Corollary 2). The exponents are expressed by difference equations along single translations
(`HasConeShiftEquations`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic PositiveRealTorus

section Cone

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- `f` satisfies **cone shift equations of order `m` and rate `ε`** along the set `J` of simple
roots, on the cone of aperture `δ`. Let `a` be a positive point of `A_{T₀}` at which every
`β ∈ J` has idele norm `1` and every simple root `α ∉ J` has idele norm at least `1`, with
`δ log |α'(a)| ≤ log |α(a)|` for all simple roots `α, α' ∉ J`. Then there are
`w_0, …, w_{m-1} ∈ ℂ` with `|w_k| ≤ δ(a)^{1/2} |α(a)|^{-ε}` for every simple root `α ∉ J`, such
that left translation by the image of `a` in `G(𝔸)` satisfies `∏_k (L_a − w_k) f = 0`, that is
`∑_k c_k f(a^k g) = 0` for every `g`, where `∏_k (X − w_k) = ∑_k c_k X^k`
(`IsTranslationPolynomialSolution`). Here `δ(a) = siegelModulus a`.

If `f = ∑_μ f_μ` is a finite sum of functions with normalized exponents `μ` along `𝔄_Q`, `Q` the
standard parabolic of `J`, whose polynomial parts have degrees `d_μ` with `∑_μ (d_μ + 1) ≤ m`,
and `Re μ(Y) ≤ −ε log |α(a)|` at `Y = H_Q(a)` for the points `a` above, then `f` satisfies these
equations: the roots are `a^{μ + ρ_Q}`, each repeated `d_μ + 1` times, and
`|a^{μ + ρ_Q}| = e^{Re μ(H_Q(a))} δ_Q(a)^{1/2}` with `δ_Q(a) = δ(a)` on `𝔄_Q`. -/
def HasConeShiftEquations (J : Set (characterLattice T)) (δ ε : ℝ) (m : ℕ)
    (f : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ a : PositiveRealTorus.intrinsicSubgroup F T₀,
    (∀ β ∈ J, logNormHom F T₀ a.val (j ≫ β) = 0) →
    (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → 0 ≤ logNormHom F T₀ a.val (j ≫ α)) →
    (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → ∀ α' ∈ simpleRelativeRoots i ν, α' ∉ J →
      δ * logNormHom F T₀ a.val (j ≫ α') ≤ logNormHom F T₀ a.val (j ≫ α)) →
    ∃ w : Fin m → ℂ,
      (∀ k, ∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
        ‖w k‖ ≤ Real.sqrt (siegelModulus F G T i ν T₀ j a) *
          Real.exp (-(ε * logNormHom F T₀ a.val (j ≫ α)))) ∧
      IsTranslationPolynomialSolution (positiveMap F G T i T₀ j a)
        (∏ k, (Polynomial.X - Polynomial.C (w k))) f

end Cone

/-- **The remainder of the weak constant term of Eisenstein series** (Delorme 2023, (4.3), (4.4)
and the bounds in the proofs of Lemmas 5.1 and 5.3; Lapid 2011, (13), Lemma 6 and Corollary 2).
The data are those of `EisensteinConstantTermWeakApproximationStatement`.

Then there are `ε > 0`, `m : ℕ`, `B` and finitely many triples `(c_q, L_q, Φ_q)` with items 1–6
of `EisensteinConstantTermWeakApproximationStatement` (`ε > 0`, smooth `c_q`, surjective
`L_q : V_q → X^*(Q) ⊗ ℝ`, the shift law `Φ_q(x + v, g) = m_Q(g)^{i L_q(v)} Φ_q(x, g)`,
continuity of `x ↦ Φ_q(x, g)` and `‖Φ_q(x, z b ω)‖ ≤ B δ(b)^{1/2} σ(z b ω)^m`), such that for
every `x ∈ C` the remainder
`r_x = E(i e(x))_Q − ∑_q c_q(x) Φ_q(x, ·)` of the constant term
`E(i e(x))_Q = subgroupConstantTerm F (Standard.unipotentHom i ν J) (E (i e(x)))` satisfies
* `‖r_x(z g)‖ = ‖r_x(g)‖` for `z ∈ A_G` and `g ∈ G(𝔸)`;
* `‖r_x(b ω)‖ ≤ B δ(b)^{1/2} σ(b ω)^m` for `b` in the weak simple-root chamber `|β(b)| ≥ t` of
  `A_{T₀}` and `ω ∈ Ω`;
* cone shift equations of order `m` and rate `ε` along `J` on the cone of aperture `δ`
  (`HasConeShiftEquations`).

Here `δ = siegelModulus` and `σ = adelicLogHeight`. In Delorme's setting the weak constant term
(4.3) supplies the triples, and `r_x` is `E^-_Q = E_Q − E^w_Q` at `λ = i e(x)`. -/
def EisensteinWeakConstantTermRemainderStatement : Prop :=
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
          ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
            (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
            (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
            IsIwasawaCompact (Standard.parabolicHom i ν ∅) K →
            ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
              (∃ α ∈ simpleRelativeRoots i ν, α ∉ J) →
              haveI : IsClosedImmersion (Standard.parabolicHom i ν J).hom.hom.left :=
                Standard.isClosedSubgroup_parabolicHom i ν J
              haveI : IsAffineHom (Standard.parabolicScheme i ν J).X.hom :=
                (Standard.isClosedSubgroup_parabolicHom i ν J).isAffineHom
              haveI : IsAffine (Standard.parabolicScheme i ν J).X.left :=
                isAffine_of_isAffineHom (Standard.parabolicScheme i ν J).X.hom
              haveI : IsClosedImmersion (Standard.unipotentHom i ν J).hom.hom.left :=
                Standard.isClosedSubgroup_unipotentHom i ν J
              haveI : IsAffineHom (Standard.unipotentScheme i ν J).X.hom :=
                (Standard.isClosedSubgroup_unipotentHom i ν J).isAffineHom
              haveI : IsAffine (Standard.unipotentScheme i ν J).X.left :=
                isAffine_of_isAffineHom (Standard.unipotentScheme i ν J).X.hom
              ∀ (hKQ : IsIwasawaCompact (Standard.parabolicHom i ν J) K) (δ : ℝ), 0 < δ →
              ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
              ∃ (ε : ℝ) (m : ℕ) (B : ℝ) (k : ℕ) (c : Fin k → (Fin n → ℝ) → ℂ)
                (V : Fin k → Submodule ℝ (Fin n → ℝ))
                (L : ∀ q, V q →ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J))
                (Φ : Fin k → (Fin n → ℝ) → AdelicGroupPoints F G → ℂ),
                0 < ε ∧
                (∀ q, ContDiff ℝ (⊤ : ℕ∞) (c q)) ∧
                (∀ q, Function.Surjective (L q)) ∧
                (∀ q (v : V q) (x : Fin n → ℝ) (g : AdelicGroupPoints F G),
                  Φ q (x + v) g =
                    hKQ.heightPower
                      (imaginaryParameter F (Standard.parabolicScheme i ν J) (L q v)) g *
                      Φ q x g) ∧
                (∀ q (g : AdelicGroupPoints F G), Continuous fun x => Φ q x g) ∧
                (∀ q, ∀ x ∈ C, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
                  ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                    ‖Φ q x (z * positiveMap F G T i T₀ j b * ω)‖ ≤
                      B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
                        adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ^ m) ∧
                (∀ x ∈ C, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
                  ∀ g : AdelicGroupPoints F G,
                    ‖subgroupConstantTerm F (Standard.unipotentHom i ν J)
                          (E (imaginaryParameter F P (e x))) (z * g) -
                        ∑ q, c q x * Φ q x (z * g)‖ =
                      ‖subgroupConstantTerm F (Standard.unipotentHom i ν J)
                          (E (imaginaryParameter F P (e x))) g -
                        ∑ q, c q x * Φ q x g‖) ∧
                (∀ x ∈ C,
                  ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                    ‖subgroupConstantTerm F (Standard.unipotentHom i ν J)
                          (E (imaginaryParameter F P (e x)))
                          (positiveMap F G T i T₀ j b * ω) -
                        ∑ q, c q x * Φ q x (positiveMap F G T i T₀ j b * ω)‖ ≤
                      B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
                        adelicLogHeight F G rho (positiveMap F G T i T₀ j b * ω) ^ m) ∧
                (∀ x ∈ C, HasConeShiftEquations F G T i ν T₀ j J δ ε m
                  (fun g => subgroupConstantTerm F (Standard.unipotentHom i ν J)
                      (E (imaginaryParameter F P (e x))) g -
                    ∑ q, c q x * Φ q x g))

end Langlands.Global
