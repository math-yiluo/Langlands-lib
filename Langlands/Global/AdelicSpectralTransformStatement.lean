import Langlands.Global.AdelicSpectralTransformSpaces
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # The unitary spectral transform

Arthur 2005, Theorem 7.2(b), and Getz–Hahn (10.22)–(10.24): the operators `M(w, λ)` on the
imaginary axis exist, and the map `(F_P)_P ↦ ∑_P n_P⁻¹ ∫ E(F_P(λ), λ) dλ` on smooth compactly
supported families extends to a linear isometry from Arthur's space `L̂` of families with
`F_{P'}(wλ) = M(w, λ) F_P(λ)` into `L²(G(F) \ G(𝔸))`, whose image is closed and invariant under
right translations by `G(𝔸)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

set_option synthInstance.maxHeartbeats 400000 in
/-- The unitary spectral transform (Arthur 2005, Theorem 7.2(b); Getz–Hahn (10.22)–(10.24)).
Let `(P i)_{i ∈ I}` be a finite family of parabolics `P i = M i ⋉ U i` with presentations `r i`
and Levi projections `π i`, `K` a maximal compact subgroup with `P i(𝔸)K = G(𝔸)`, `μ_{M i}`
compatible Haar measures, coordinates `e i` on `X^*(P i) ⊗ ℝ` and weights `β i ≥ 0` with
integral `1`, and `(w i i' t, cw i i' t)` an enumeration of each `Ω(P i, P i')` whose coordinate
changes `x ↦ (e i')⁻¹ (w (e i x))` preserve Lebesgue measure. Let `n_i = ∑ i', |Ω(P i, P i')|`.
Then:
* there are operators `Mop i i' t x = M(w i i' t, i e_i(x)) : H_{P i} → H_{P i'}`
  (`IsImaginaryIntertwiningOperator`);
* for every such choice, there is a linear isometry `Ē : L̂ → L²(G(F) \ G(𝔸))` on Arthur's
  space `L̂` of families with `F_{i'}(wλ) = M(w, λ) F_i(λ)` and norm
  `∑ i, n_i⁻¹ ∫ ‖F_i(λ)‖² dλ`, such that the smooth compactly supported families of `L̂` are
  dense, `Ē` sends each of them, `F_i(λ) = ∑ j, c i j λ • v i j`, to
  `∑ i, n_i⁻¹ ∫ ∑ j, c i j λ • E(v i j, λ) dλ` for all Eisenstein continuations `E` holomorphic
  near `i𝔞_{P i}^*`, and the range of `Ē` is closed and invariant under right translation by
  `G(𝔸)`. -/
def SpectralTransformStatement : Prop :=
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
    (∀ i, IsIso (subgroupMultiplication (l i) (iU i))) → (∀ i, l i ≫ π i = 𝟙 (M i)) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) [∀ i, (μM i).IsHaarMeasure],
      (∀ i, IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i)) →
    ∀ (n : I → ℕ) (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
      (β : ∀ i, (Fin (n i) → ℝ) → ℝ),
      (∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ (∀ y, 0 ≤ β i y) ∧
        ∫ y, β i y = 1) →
    ∀ (T : I → I → Type) [∀ i i', Fintype (T i i')]
      (w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : ∀ i i', T i i' → (M i' ⟶ M i)),
      (∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t)) →
      (∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i'))) →
      (∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
        ∃ t, weylParameter (l i) (cw i i' t) (π i') = s) →
    ∀ (hw : ∀ i i' t, MeasurePreserving
        (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
        volume volume),
    let nP : I → ℕ := fun i => ∑ i', Fintype.card (T i i')
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    (∃ Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
        inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
            (e i) (β i) →L[ℂ]
          inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
            (μM i') (e i') (β i'),
      ∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
        (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
        (e i) (e i') (β i) (β i') (Mop i i' t)) ∧
    ∀ (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
        inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
            (e i) (β i) →L[ℂ]
          inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
            (μM i') (e i') (β i')),
      (∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
        (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
        (e i) (e i') (β i) (β i') (Mop i i' t)) →
    ∃ Ebar : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop →ₗᵢ[ℂ]
        Lp ℂ 2 μG,
      (Submodule.span ℂ {Φ : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π
          hw Mop | ∃ k v c, IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c
            Φ.1}).topologicalClosure = ⊤ ∧
      (∀ (Φ : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
          (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
          (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ),
        IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1 →
        ∀ (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
          (D : ∀ i, Set (ComplexCharacterParameter F (P i))),
          (∀ i, Set.range (imaginaryParameter F (P i)) ⊆ D i) →
          (∀ i j g, IsMeromorphicInCoordinatesOn (fun lam => E i j lam g) (D i)) →
          (∀ i j, ∃ R : ℝ, ∀ lam, (r i).IsRegularParameter (hA i) (hT i) R lam →
            E i j lam = (hK i).eisensteinSeries (v i j) lam) →
          ⇑(Ebar Φ) =ᵐ[μG] fun y => ∑ i, ((nP i : ℂ))⁻¹ *
            ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) y.out
              ∂(spectralMeasure (n i))) ∧
      IsClosed (LinearMap.range Ebar.toLinearMap : Set (Lp ℂ 2 μG)) ∧
      ∀ f ∈ LinearMap.range Ebar.toLinearMap, ∀ y : AdelicGroupPoints F G,
        ∃ f' ∈ LinearMap.range Ebar.toLinearMap,
          f' =ᵐ[μG] fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) (x.out * y))

end Langlands.Global
