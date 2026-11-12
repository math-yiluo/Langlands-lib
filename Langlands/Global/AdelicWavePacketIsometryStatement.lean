import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # The wave packet isometry

Lapid 2011, Theorem 2 (p.314), and Getz–Hahn §10.5, (10.22)–(10.24): for a finite family of
parabolics `P` and Weyl-compatible wave packet data `F_P`, the map
`(F_P)_P ↦ ∑_P n_P⁻¹ Θ_{P, F_P}` is an isometry for the norm `∑_P n_P⁻¹ ‖F_P‖²_*`, where
`n_P = ∑_{P'} |Ω(P, P')|`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- The wave packet isometry (Lapid 2011, Theorem 2, on the dense subspace of smooth compactly
supported families; Getz–Hahn (10.22)–(10.24)). Let `(P i)_{i ∈ I}` be a finite family of
parabolics `P i = M i U i` with presentations `r i` and Levi projections `π i`, `K` a maximal
compact subgroup with `P i(𝔸)K = G(𝔸)` for all `i`, `μ_{M i}` compatible Haar measures,
coordinates `e i` and weights `β i` with integral `1` defining `dλ` and `(·,·)_{P i}`. For each
pair `(i, i')` let `(w i i' t, cw i i' t)` enumerate `Ω(P i, P i')` once, with coordinate changes
`x ↦ (e i')⁻¹ (w (e i x))` preserving Lebesgue measure, and let
`M(w i i' t, λ) (v i j) = ∑ q, coeff i i' t j q λ • ψ i i' t j q` for `Re λ` sufficiently regular,
with coefficients holomorphic near `i𝔞_{P i}^*`. Let `F i (x) = ∑ j, c i j x • v i j` with
`v i j ∈ A^2_{P i}`, `c i j` smooth and compactly supported, and Eisenstein continuations `E i j`
holomorphic near `i𝔞_{P i}^*`, and suppose the Weyl compatibility
`F i' (w λ) = M(w, λ) F i (λ)` for all `w ∈ Ω(P i, P i')` and imaginary `λ`. Let
`n i = ∑ i', |Ω(P i, P i')|` and `Φ = ∑ i, (n i)⁻¹ Θ i`, with `Θ i` the wave packet of `F i`.
Then `Φ ∈ L²(G(F) \ G(𝔸))` and `‖Φ‖² = ∑ i, (n i)⁻¹ ∫ (F i (x), F i (x))_{P i} dλ`. -/
def WavePacketIsometryStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (I : Type) [Fintype I]
    (P M U : I → GroupScheme (Spec (CommRingCat.of F)))
    (A : I → CommGroupScheme (Spec (CommRingCat.of F)))
    [∀ i, IsAffine (P i).X.left] [∀ i, IsAffine (M i).X.left]
    [∀ i, LocallyOfFiniteType (M i).X.hom] [∀ i, IsAffine (U i).X.left]
    (p : ∀ i, P i ⟶ G) [∀ i, IsClosedImmersion (p i).hom.hom.left] (iU : ∀ i, U i ⟶ P i)
    (l : ∀ i, M i ⟶ P i) [∀ i, IsClosedImmersion (iU i ≫ p i).hom.hom.left]
    (a : ∀ i, (A i).toGrp ⟶ M i) (r : ∀ i, ParabolicRootPresentation (p i) (l i) (a i))
    [∀ i, Mono (r i).data.i.hom.hom.left] [∀ i, Fintype (relativeWeylGroup (r i).data.i)]
    [∀ i, Mono (CommGroupScheme.groupHom (r i).data.f).hom.hom.left]
    (hA : ∀ i, IsSplitTorus (A i).toGrp) (hT : ∀ i, IsSplitTorus (r i).data.T.toGrp)
    (π : ∀ i, P i ⟶ M i),
    haveI : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
      IsClosedSubgroup.locallyOfFiniteType (j := p i)
        (inferInstance : IsClosedImmersion (p i).hom.hom.left)
    IsConnectedReductive G → (∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i)) →
    (∀ i, l i ≫ π i = 𝟙 (M i)) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) [∀ i, (μM i).IsHaarMeasure],
      (∀ i, IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i)) →
    ∀ (n : I → ℕ) (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
      (β : ∀ i, (Fin (n i) → ℝ) → ℝ),
      (∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ ∫ y, β i y = 1) →
    ∀ (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
      (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
      (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D : ∀ i, Set (ComplexCharacterParameter F (P i))),
      (∀ i j,
        IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
          (v i j)) →
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j) ∧ HasCompactSupport (c i j)) →
      (∀ i, Set.range (imaginaryParameter F (P i)) ⊆ D i) →
      (∀ i j g, IsMeromorphicInCoordinatesOn (fun lam => E i j lam g) (D i)) →
      (∀ i j, ∃ R : ℝ, ∀ lam, (r i).IsRegularParameter (hA i) (hT i) R lam →
        E i j lam = (hK i).eisensteinSeries (v i j) lam) →
    ∀ (T : I → I → Type) [∀ i i', Fintype (T i i')]
      (w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : ∀ i i', T i i' → (M i' ⟶ M i)),
      (∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t)) →
      (∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i'))) →
      (∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
        ∃ t, weylParameter (l i) (cw i i' t) (π i') = s) →
      (∀ i i' t, MeasurePreserving
        (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
        volume volume) →
    ∀ (m : ℕ) (ψ : ∀ i i', T i i' → Fin (k i) → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : ∀ i i', T i i' → Fin (k i) → Fin m → ComplexCharacterParameter F (P i) → ℂ)
      (DM : ∀ i, Set (ComplexCharacterParameter F (P i))),
      (∀ i i' t j q,
        IsSquareIntegrableInducedForm K (hK i').isCompact rho hsmooth hcalc (p i') (iU i')
          (l i') (ψ i i' t j q)) →
      (∀ i, Set.range (imaginaryParameter F (P i)) ⊆ DM i) →
      (∀ i i' t j q, IsMeromorphicInCoordinatesOn (coeff i i' t j q) (DM i)) →
      (∀ i i' t j, ∃ R : ℝ, ∀ lam, (r i).IsRegularParameter (hA i) (hT i) R lam → ∀ g,
        (hK i).intertwiningOperator (hK i') (iU i) (l i) (iU i') (cw i i' t) (π i')
            (w i i' t) (v i j) lam g =
          ∑ q, coeff i i' t j q lam * ψ i i' t j q g) →
      (∀ i i' t x g,
        ∑ j', c i' j' ((e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x))) *
            v i' j' g =
          ∑ j, c i j x *
            ∑ q, coeff i i' t j q (imaginaryParameter F (P i) (e i x)) * ψ i i' t j q g) →
    let Θ : I → AdelicGroupPoints F G → ℂ := fun i g =>
      ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) g ∂(spectralMeasure (n i))
    let nP : I → ℕ := fun i => ∑ i', Fintype.card (T i i')
    let Φ : AdelicGroupPoints F G → ℂ := fun g => ∑ i, ((nP i : ℂ))⁻¹ * Θ i g
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    MemLp (fun y : RationalQuotient F G => Φ y.out) 2 μG ∧
      ∫ y, ‖Φ y.out‖ ^ 2 ∂μG =
        ∑ i, ((nP i : ℝ))⁻¹ *
          ∫ x, (inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i)
              (fun g => ∑ j, c i j x * v i j g) (fun g => ∑ j, c i j x * v i j g)).re
            ∂(spectralMeasure (n i))

end Langlands.Global
