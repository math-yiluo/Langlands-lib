import Langlands.Global.AdelicSpectralWitnessReduction
import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Generalized eigenfunctions from invariant distribution vectors

`CyclicSpectralEigenfunctionStatement` follows from two propositions about a unitary
representation `ρ` of `G(𝔸)` on a complex Hilbert space `V` and a linear form `ξ` on `V`.
A vector of `V` is called smooth here when it is a smooth vector of the restriction of `ρ` to
`G(F_∞)` (for the manifold structure `InfiniteAdelicGroupPoints.smoothChartedSpace`) and is
fixed by an open subgroup of `G(𝔸_f)`. The form `ξ` is a distribution vector when, on the
smooth vectors fixed by any open subgroup `L` of `G(𝔸_f)`, it is bounded by finitely many of the
seminorms `v ↦ ‖dρ(X₁ ⋯ Xₖ) v‖`. Its matrix coefficients are the functions
`Φ_v(g) = ξ(ρ(g) v)` for smooth `v`.

* `CyclicIrreducibleDistributionVectorStatement` (Delorme 2023, proof of Lemma 7.10, with
  Bernstein 1988, §1.4 and §§3.1–3.4): every nonzero `f ∈ L²([G])` gives a topologically
  irreducible unitary `ρ` and a nonzero `G(F)`-invariant distribution vector `ξ` whose matrix
  coefficients lie in `L²([G], σ_{[G]}^{-2m})` and in the weighted closure of the complex linear
  span of the right translates of `f`;
* `IrreducibleDistributionVectorAutomorphyStatement` (Delorme 2023, proof of Lemma 7.10;
  Harish-Chandra 1953, §11, with Segal's theorem that `𝔷` acts by scalars on irreducible
  unitary representations; Schur's lemma for `A_G`): a nonzero distribution vector of a
  topologically irreducible unitary representation has a matrix coefficient that is a nonzero
  smooth, `K_∞`-finite, `𝔷`-finite function with a unitary `A_G`-character.

The theorem `cyclicSpectralEigenfunction_of_distributionVectors` derives
`CyclicSpectralEigenfunctionStatement` from the two. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Archimedean

/-- Irreducible pieces of a cyclic subspace with tempered invariant distribution vectors
(Delorme 2023, proof of Lemma 7.10; Bernstein 1988, §1.4 and §§3.1–3.4, with the summable weight
`σ_{[G]}^{2m}` of Delorme's (2.10) and Remark 3.4). Let `f ∈ L²([G])` be not zero almost
everywhere. There are a complex Hilbert space `V`, a jointly continuous, unitary, topologically
irreducible representation `ρ` of `G(𝔸)` on `V`, a linear form `ξ` on `V` and `m : ℕ` such that:

* on the smooth vectors fixed by an open subgroup `L` of `G(𝔸_f)`, `‖ξ v‖` is bounded by a
  constant times a finite sum of the norms `‖dρ(X₁ ⋯ Xₖ) v‖` of iterated derivatives along
  `G(F_∞)`;
* `ξ(ρ(γ g) v) = ξ(ρ(g) v)` for `γ ∈ G(F)`, `g ∈ G(𝔸)` and smooth `v`;
* `ξ v ≠ 0` for some smooth `v`;
* for smooth `v`, `y ↦ ξ(ρ(y.out) v) / σ_{[G]}(y)^m` is in `L²([G])`, and
  `∫ y, ξ(ρ(y.out) v) · conj Θ(y.out) = 0` for every `Θ` with `Θ σ_{[G]}^m ∈ L²([G])` that is
  orthogonal to all right translates of `f`.

A vector is smooth when it is a smooth vector of the restriction of `ρ` to `G(F_∞)` and is fixed
by an open subgroup of `G(𝔸_f)`. Only the restriction of `ξ` to smooth vectors matters. -/
def CyclicIrreducibleDistributionVectorStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG → ¬ f =ᵐ[μG] 0 →
      ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
        (ρ : AdelicGroupPoints F G →* (V →L[ℂ] V)) (ξ : V →ₗ[ℂ] ℂ) (m : ℕ),
        let ρinf := ρ.comp (ofInfinite F G).toMonoidHom
        let Vsm := Langlands.Archimedean.smoothVectors
          𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ρinf
        let IsSmooth : V → Prop := fun v => v ∈ Vsm ∧
          ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
            IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧ ∀ l ∈ L, ρ (ofFinite F G l) v = v
        (∀ g, ρ g ∈ unitary (V →L[ℂ] V)) ∧
        IsContinuousRepresentation ρ ∧ IsTopologicallyIrreducible ρ ∧
        (∀ L : Subgroup (FiniteAdelicGroupPoints F G),
          IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
          ∃ (S : Finset (List (InfiniteAdelicGroupPoints.smoothModel F d))) (C : ℝ),
            ∀ v ∈ Vsm, (∀ l ∈ L, ρ (ofFinite F G l) v = v) →
              ‖ξ v‖ ≤ C * ∑ Xs ∈ S,
                ‖Langlands.Archimedean.iteratedLieDerivative
                  𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ρinf Xs v‖) ∧
        (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, ∀ v, IsSmooth v →
          ξ (ρ (q * g) v) = ξ (ρ g v)) ∧
        (∃ v, IsSmooth v ∧ ξ v ≠ 0) ∧
        ∀ v, IsSmooth v →
          MemLp (fun y : RationalQuotient F G =>
            ξ (ρ y.out v) / (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG ∧
          ∀ Θ : AdelicGroupPoints F G → ℂ,
            MemLp (fun y : RationalQuotient F G =>
              Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG →
            (∀ g : AdelicGroupPoints F G,
              ∫ y, f (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g y) *
                (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
            ∫ y, ξ (ρ y.out v) * (starRingEnd ℂ) (Θ y.out) ∂μG = 0

/-- Matrix coefficients of distribution vectors of irreducible unitary representations are
generalized eigenfunctions (Delorme 2023, proof of Lemma 7.10; Harish-Chandra 1953, §11, after
Segal: `𝔷` acts by scalars on an irreducible unitary representation; Schur's lemma for `A_G`).
Let `ρ` be a jointly continuous, unitary, topologically irreducible representation of `G(𝔸)` on
a complex Hilbert space `V`, and `ξ` a linear form on `V` which, on the smooth vectors fixed by
any open subgroup `L` of `G(𝔸_f)`, is bounded by a constant times a finite sum of the norms
`‖dρ(X₁ ⋯ Xₖ) v‖`, and which does not vanish on all smooth vectors. Then some smooth vector `v`
has a matrix coefficient `Φ(g) = ξ(ρ(g) v)` that is smooth, `K_∞`-finite and `𝔷`-finite,
satisfies `Φ(a g) = a^{iν} Φ(g)` for some `ν ∈ X^*(G) ⊗ ℝ` and all `a ∈ A_G`, and is not
identically zero. A vector is smooth when it is a smooth vector of the restriction of `ρ` to
`G(F_∞)` and is fixed by an open subgroup of `G(𝔸_f)`. -/
def IrreducibleDistributionVectorAutomorphyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {d : ℕ}
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K →
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (ρ : AdelicGroupPoints F G →* (V →L[ℂ] V)) (ξ : V →ₗ[ℂ] ℂ),
      let ρinf := ρ.comp (ofInfinite F G).toMonoidHom
      let Vsm := Langlands.Archimedean.smoothVectors
        𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ρinf
      let IsSmooth : V → Prop := fun v => v ∈ Vsm ∧
        ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
          IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧ ∀ l ∈ L, ρ (ofFinite F G l) v = v
      (∀ g, ρ g ∈ unitary (V →L[ℂ] V)) →
      IsContinuousRepresentation ρ → IsTopologicallyIrreducible ρ →
      (∀ L : Subgroup (FiniteAdelicGroupPoints F G),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
        ∃ (S : Finset (List (InfiniteAdelicGroupPoints.smoothModel F d))) (C : ℝ),
          ∀ v ∈ Vsm, (∀ l ∈ L, ρ (ofFinite F G l) v = v) →
            ‖ξ v‖ ≤ C * ∑ Xs ∈ S,
              ‖Langlands.Archimedean.iteratedLieDerivative
                𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ρinf Xs v‖) →
      (∃ v, IsSmooth v ∧ ξ v ≠ 0) →
      ∃ v, IsSmooth v ∧
        IsAdelicSmoothFunction F G (fun g => ξ (ρ g v)) ∧
        IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
          (fun g => ξ (ρ g v)) ∧
        IsCenterFiniteFunction F G hsmooth hcalc (fun g => ξ (ρ g v)) ∧
        (∃ ν : RealCharacterParameter F G,
          ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ g : AdelicGroupPoints F G,
            ξ (ρ (a * g) v) = parameterPower F G (imaginaryParameter F G ν) a * ξ (ρ g v)) ∧
        ∃ g, ξ (ρ g v) ≠ 0

/-- The two propositions imply the cyclic generalized eigenfunction statement. -/
theorem cyclicSpectralEigenfunction_of_distributionVectors
    (hA : CyclicIrreducibleDistributionVectorStatement)
    (hB : IrreducibleDistributionVectorAutomorphyStatement) :
    CyclicSpectralEigenfunctionStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho hP₀ μG f hf hne
  obtain ⟨V, _, _, _, ρ, ξ, m, hunit, hcont, hirr, hξ, hΓ, hne', hv⟩ :=
    hA F G hred K rho hsmooth hKmax hrho hP₀ f hf hne
  obtain ⟨v, hvs, hsm, hKfin, hZfin, hν, hnz⟩ :=
    hB F G hred K hsmooth hcalc hKmax V ρ ξ hunit hcont hirr hξ hne'
  obtain ⟨hL2, hdual⟩ := hv v hvs
  exact ⟨m, fun g => ξ (ρ g v), fun x hx g => hΓ x hx g v hvs, hsm, hKfin, hZfin, hν, hL2, hnz,
    hdual⟩

end Langlands.Global
