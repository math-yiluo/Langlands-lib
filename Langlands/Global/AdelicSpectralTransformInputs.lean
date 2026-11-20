import Langlands.Global.AdelicSpectralTransformStatement

/-! # Inputs of the unitary spectral transform

Five propositions from which `SpectralTransformStatement` (Arthur 2005, Theorem 7.2(b);
Getz–Hahn (10.22)–(10.24)) follows by Hilbert space arguments
(`SpectralTransformReductionStatement`):

* `ImaginaryIntertwiningExistenceStatement`: the operators `M(w, λ) : H_P → H_{P'}` exist on the
  imaginary axis (Arthur 2005, Theorem 7.2(a); Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i));
* `SymmetricFamilyDensityStatement`: the smooth compactly supported families are dense in
  Arthur's space `L̂` (Arthur 2005, §7; Delorme, Lemma 6.2);
* `EisensteinImaginaryContinuationStatement`: finitely many `φ ∈ A^2_P` have Eisenstein series
  continuations with one domain of holomorphy containing `i𝔞_P^*` (Bernstein–Lapid, Theorem
  2.3(1); Lapid 2011, Proposition 6);
* `SymmetricFamilyGramStatement`: the wave packets of smooth compactly supported families of
  `L̂` are square integrable with inner products those of `L̂` (Lapid 2011, Theorem 2, polarized);
* `WavePacketTranslationStatement`: the right translates of such wave packets are `L²`-limits
  of such wave packets (Arthur 2005, §7: `R(y)` acts on `H_P` through `I_P(λ, y)`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Helpers

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {K : Subgroup (AdelicGroupPoints F G)}

/-- `E` is a family of continuations of the Eisenstein series `E(v j, λ)` with one domain of
holomorphy `D` containing `i(X^*(P) ⊗ ℝ)`: each `λ ↦ E j λ g` is meromorphic in coordinates
with domain `D`, and `E j λ = E(v j, λ)` for `Re λ` sufficiently regular. These are the
conditions that `SpectralTransformStatement` imposes on its continuations `E i j`. -/
def IsEisensteinContinuation (hK : IsIwasawaCompact p K) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) {k : ℕ}
    (v : Fin k → AdelicGroupPoints F G → ℂ)
    (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F P)) : Prop :=
  Set.range (imaginaryParameter F P) ⊆ D ∧
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) ∧
    ∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E j lam = hK.eisensteinSeries (v j) lam

end Helpers

/-- The wave packet sum `y ↦ ∑ i, (nP i)⁻¹ ∫ ∑ j, c i j x • E i j (i e_i(x)) y dλ` on
`G(F) \ G(𝔸)`, evaluated at the chosen representative `y.out` of each coset; it is the function
of the formula of `SpectralTransformStatement`. -/
def wavePacketSum {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    {I : Type} [Fintype I] {P : I → GroupScheme (Spec (CommRingCat.of F))} {n : I → ℕ}
    (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i)) (nP : I → ℕ)
    {k : I → ℕ} (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
    (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ) :
    RationalQuotient F G → ℂ :=
  fun y => ∑ i, ((nP i : ℂ))⁻¹ *
    ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) y.out
      ∂(spectralMeasure (n i))

/-- Existence of the operators `M(w, λ) : H_P → H_{P'}` on the imaginary axis (Arthur 2005,
Theorem 7.2(a); Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i)). For two presented parabolics
`P = MU` and `P' = M'U'` with Levi projections, `K` maximal compact with
`P(𝔸)K = P'(𝔸)K = G(𝔸)`, compatible Haar measures `μ_M`, `μ_{M'}`, coordinates `e`, `e'` and
weights `β`, `β'` with integral `1`, and an element `(w, cw)` of `W(P, P')` whose coordinate change
`x ↦ e'⁻¹(w(e x))` preserves Lebesgue measure, there is a family of continuous linear operators
`Mop x : H_P → H_{P'}` with `IsImaginaryIntertwiningOperator`. -/
def ImaginaryIntertwiningExistenceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : P' ⟶ M'),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iU' → IsIso (subgroupMultiplication l iU) →
    IsIso (subgroupMultiplication l' iU') → l ≫ π = 𝟙 M → l' ≫ π' = 𝟙 M' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
      (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P')
      (β : (Fin n → ℝ) → ℝ) (β' : (Fin n' → ℝ) → ℝ),
      (Continuous β ∧ HasCompactSupport β ∧ (∀ y, 0 ≤ β y) ∧ ∫ y, β y = 1) →
      (Continuous β' ∧ HasCompactSupport β' ∧ (∀ y, 0 ≤ β' y) ∧ ∫ y, β' y = 1) →
    ∀ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M),
      IsWeylConjugation p l p' l' w cw →
      MeasurePreserving (fun x => e'.symm (realWeylParameter l cw π' (e x))) volume volume →
    ∃ Mop : (Fin n → ℝ) →
        inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β →L[ℂ]
          inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β',
      IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT iU' l' π' w cw
        μM μM' e e' β β' Mop

set_option synthInstance.maxHeartbeats 400000 in
/-- Density of the smooth compactly supported families in Arthur's space `L̂` (Arthur 2005, §7,
p.34; Delorme, Lemma 6.2: the symmetrization over the `Ω(P i, P i')` is the orthogonal
projection onto `L̂` and preserves smooth compactly supported families). In the data of
`SpectralTransformStatement`, for every family `Mop` of operators `M(w, λ)` with
`IsImaginaryIntertwiningOperator`, the span of the smooth compactly supported families of `L̂`
is dense in `L̂`. -/
def SymmetricFamilyDensityStatement : Prop :=
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
    ∀ (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
        inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
            (e i) (β i) →L[ℂ]
          inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
            (μM i') (e i') (β i')),
      (∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
        (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
        (e i) (e i') (β i) (β i') (Mop i i' t)) →
      (Submodule.span ℂ {Φ : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π
          hw Mop | ∃ k v c, IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c
            Φ.1}).topologicalClosure = ⊤

/-- Eisenstein series continuations near the imaginary axis (Bernstein–Lapid, Theorem 2.3(1):
meromorphic continuation; Lapid 2011, Proposition 6: holomorphy on `i𝔞_P^*`). For a presented
parabolic `P = MU`, `K` maximal compact with `P(𝔸)K = G(𝔸)` and finitely many `v j ∈ A^2_P`,
there are continuations `E j` of the Eisenstein series `E(v j, λ)` with one domain of holomorphy
`D` containing `i(X^*(P) ⊗ ℝ)` (`IsEisensteinContinuation`). -/
def EisensteinImaginaryContinuationStatement : Prop :=
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
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
    ∃ (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)), IsEisensteinContinuation hK r hA hT v E D

set_option synthInstance.maxHeartbeats 400000 in
/-- The Gram identity for wave packets of `L̂` (Lapid 2011, Theorem 2, polarized; Getz–Hahn
(10.22)–(10.24)). In the data of `SpectralTransformStatement`, for every family `Mop` of
operators `M(w, λ)` with `IsImaginaryIntertwiningOperator`, and smooth compactly supported
families `Φ`, `Φ'` of `L̂` with representations `F_i(λ) = ∑ j, c i j λ • v i j`,
`F'_i(λ) = ∑ j, c' i j λ • v' i j` and Eisenstein continuations `E`, `E'`
(`IsEisensteinContinuation`), the wave packet sum `W` of `(c, E)` is square integrable on
`G(F) \ G(𝔸)` and `∫ conj(W y) W'(y) dy = ⟨Φ, Φ'⟩_{L̂}`, where `W'` is the wave packet sum of
`(c', E')`. -/
def SymmetricFamilyGramStatement : Prop :=
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
    ∀ (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
        inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
            (e i) (β i) →L[ℂ]
          inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
            (μM i') (e i') (β i')),
      (∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
        (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
        (e i) (e i') (β i) (β i') (Mop i i' t)) →
    ∀ (Φ Φ' : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
      (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
      (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
      (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D : ∀ i, Set (ComplexCharacterParameter F (P i)))
      (k' : I → ℕ) (v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ)
      (c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ)
      (E' : ∀ i, Fin (k' i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D' : ∀ i, Set (ComplexCharacterParameter F (P i))),
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1 →
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i)) →
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Φ'.1 →
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v' i) (E' i) (D' i)) →
      MemLp (wavePacketSum e nP c E) 2 μG ∧
        ∫ y, (starRingEnd ℂ) (wavePacketSum e nP c E y) * wavePacketSum e nP c' E' y ∂μG =
          inner ℂ Φ.1 Φ'.1

set_option synthInstance.maxHeartbeats 400000 in
/-- Right translation of wave packets (Arthur 2005, §7, p.35: `R(y)` acts on `H_P` through the
induced representation `I_P(λ, y)`, which the operators `M(w, λ)` intertwine). In the data of
`SpectralTransformStatement`, for every family `Mop` of operators `M(w, λ)` with
`IsImaginaryIntertwiningOperator`, every smooth compactly supported family of `L̂` with a
representation `(v, c)` and Eisenstein continuations `E`, every `y ∈ G(𝔸)` and every `ε > 0`,
there is a smooth compactly supported family of `L̂` with a representation `(v', c')` and
continuations `E'` whose wave packet sum is within `ε` in `L²(G(F) \ G(𝔸))` of the right
translate by `y` of the wave packet sum of `(c, E)`. -/
def WavePacketTranslationStatement : Prop :=
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
    ∀ (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
        inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
            (e i) (β i) →L[ℂ]
          inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
            (μM i') (e i') (β i')),
      (∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
        (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
        (e i) (e i') (β i) (β i') (Mop i i' t)) →
    ∀ (Φ : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
      (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
      (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
      (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D : ∀ i, Set (ComplexCharacterParameter F (P i))),
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1 →
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i)) →
    ∀ (y : AdelicGroupPoints F G) (ε : ℝ), 0 < ε →
    ∃ (Φ' : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
      (k' : I → ℕ) (v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ)
      (c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ)
      (E' : ∀ i, Fin (k' i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D' : ∀ i, Set (ComplexCharacterParameter F (P i))),
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Φ'.1 ∧
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v' i) (E' i) (D' i)) ∧
      eLpNorm (fun z => wavePacketSum e nP c E
          (LeftCosetSpace.mk (rationalSubgroup F G) (z.out * y)) - wavePacketSum e nP c' E' z)
        2 μG < ENNReal.ofReal ε

end Langlands.Global
