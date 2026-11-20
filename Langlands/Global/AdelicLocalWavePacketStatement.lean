import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicWavePacketInnerProductStatement
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Smooth wave packets, the inner product on `A^2_P`, and Levi data

Premises of the reduction of Lapid 2011, Lemma 10 (`BoundedWavePacketStatement`) to statements
about smooth wave packets:

* `LocalWavePacketInnerProductStatement`: Lapid's Proposition 2 (p.314) for `φ ∈ W_P`, i.e. for
  smooth coefficients supported in a compact set on which the Eisenstein series are regular;
* `LocalWavePacketNormBoundStatement`: the bound (19) of Lemma 10 for `φ ∈ W_P`;
* `InducedInnerProductSesquilinearStatement`: `(·,·)_P` is sesquilinear on finite linear
  combinations of elements of `A^2_P` (absolute convergence of the defining integral);
* `LeviProjectionExistenceStatement`: a Levi projection `π : P → M` with `l ≫ π = 𝟙` exists
  (Getz–Hahn, Theorem 1.5.8);
* `WavePacketIwasawaCompatibleMeasureExistenceStatement`: a Haar measure on `M(𝔸)` compatible with the
  Iwasawa decomposition exists (Getz–Hahn, Exercise 3.5). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Lapid 2011, Proposition 2 (p.314), for wave packets in Lapid's space `W_P`: the data of
`BoundedWavePacketInnerProductStatement`, with smooth coefficients `c j` (`c' j`) vanishing
outside a compact set `S` (`S'`) of coordinates, on whose image `{i e(x) | x ∈ S}` the
continuations `E j` and the coefficients `coeff t j i` are holomorphic (domains `D`, `DM`), and
similarly for `P'`. The conclusion is that of Proposition 2: `Θ` and `Θ'` are square integrable
on `G(F) \ G(𝔸)` and `(Θ, Θ') = ∫ ∑ t, (M(w t, λ)φ(λ), φ'(w_t λ))_{P'} dλ`, written out in the
data. -/
def LocalWavePacketInnerProductStatement : Prop :=
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
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
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
    LeviSubgroup.IsGeometricUnipotentRadical iU' → l' ≫ π' = 𝟙 M' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n' → ℝ) → ℝ),
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
      (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      IsCompact S →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) →
    ∀ (k' : ℕ) (v' : Fin k' → AdelicGroupPoints F G → ℂ) (c' : Fin k' → (Fin n' → ℝ) → ℂ)
      (S' : Set (Fin n' → ℝ))
      (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ j, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j)) →
      IsCompact S' →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ S', c' j x = 0) →
      (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ D' →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D') →
      (∀ j, ∃ R : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R lam →
        E' j lam = hK'.eisensteinSeries (v' j) lam) →
    ∀ (T : Type) [Fintype T] (w : T → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : T → (M' ⟶ M)),
      (∀ t, IsWeylConjugation p l p' l' (w t) (cw t)) →
      Function.Injective (fun t => weylParameter l (cw t) π') →
      (∀ s ∈ weylParameterSet p l p' l' π', ∃ t, weylParameter l (cw t) π' = s) →
    ∀ (m : ℕ) (ψ : T → Fin k → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : T → Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM : Set (ComplexCharacterParameter F P)),
      (∀ t j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ t j i)) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ DM →
      (∀ t j i, IsMeromorphicInCoordinatesOn (coeff t j i) DM) →
      (∀ t j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t) (v j) lam g =
          ∑ i, coeff t j i lam * ψ t j i g) →
    let Θ : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
    let Θ' : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c' j x * E' j (imaginaryParameter F P' (e' x)) g ∂(spectralMeasure n')
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG ∧
      MemLp (fun y : RationalQuotient F G => Θ' y.out) 2 μG ∧
      ∫ y, Θ y.out * (starRingEnd ℂ) (Θ' y.out) ∂μG =
        ∫ x, ∑ t, ∑ j, ∑ i, ∑ j',
            c j x * coeff t j i (imaginaryParameter F P (e x)) *
              (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
              inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j')
          ∂(spectralMeasure n)

/-- `LocalWavePacketInnerProductStatement` implies the published Proposition 2
(`WavePacketInnerProductStatement`), whose continuations are holomorphic on all of `i𝔞_P^*`:
take `S` the union of the supports of the `c j`. -/
theorem wavePacketInnerProduct_of_local (h : LocalWavePacketInnerProductStatement) :
    WavePacketInnerProductStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    a' r' _ _ _ hA' hT' π' hG hU hU' hlπ' K hK hK' Nr dr rho hsmooth hcalc hKmax hrho μM' _ hμM'
    n n' e e' β' hβc' hβs' hβ1' k v c E D hv hc hD hE hEis k' v' c' E' D' hv' hc' hD' hE' hEis'
    T _ w cw hw hinj hsurj mi ψ coeff DM hψ hDM hcoeff hexp
  have key : ∀ {q : ℕ} {r : ℕ} (b : Fin r → (Fin q → ℝ) → ℂ), (∀ j, HasCompactSupport (b j)) →
      IsCompact (⋃ j, tsupport (b j)) ∧ ∀ j, ∀ x ∉ ⋃ j, tsupport (b j), b j x = 0 := by
    intro q r b hb
    refine ⟨isCompact_iUnion fun j => hb j, fun j x hx => ?_⟩
    exact image_eq_zero_of_notMem_tsupport fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩)
  obtain ⟨hS, hcS⟩ := key c fun j => (hc j).2
  obtain ⟨hS', hcS'⟩ := key c' fun j => (hc' j).2
  exact h F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' hG hU hU' hlπ' K hK
    hK' rho hsmooth hcalc hKmax hrho μM' hμM' e e' β' hβc' hβs' hβ1' k v c _ E D hv hS
    (fun j => ⟨(hc j).1, hcS j⟩) (fun _ ⟨x, _, hx⟩ => hx ▸ hD ⟨e x, rfl⟩) hE hEis k' v' c' _ E'
    D' hv' hS' (fun j => ⟨(hc' j).1, hcS' j⟩) (fun _ ⟨x, _, hx⟩ => hx ▸ hD' ⟨e' x, rfl⟩) hE'
    hEis' T w cw hw hinj hsurj mi ψ coeff DM hψ (fun _ ⟨x, _, hx⟩ => hx ▸ hDM ⟨e x, rfl⟩)
    hcoeff hexp

/-- The bound (19) of Lapid 2011, Lemma 10 (p.329), for wave packets in Lapid's space `W_P`:
the data of `BoundedWavePacketNormBoundStatement`, with smooth coefficients `c j` vanishing
outside a compact set `S` of coordinates on whose image `{i e(x) | x ∈ S}` the continuations
`E j` are holomorphic. Conclusion: `Ω(P, P)` is finite, `Θ` is square integrable on
`G(F) \ G(𝔸)`, and `∫ |Θ|² ≤ |Ω(P, P)| · ∫ (φ(x), φ(x))_P dx`. -/
def LocalWavePacketNormBoundStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
      (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      IsCompact S →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) →
    let Θ : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
    let φ : (Fin n → ℝ) → AdelicGroupPoints F G → ℂ := fun x g => ∑ j, c j x * v j g
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    (weylParameterSet p l p l π).Finite ∧
      MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG ∧
      ∫ y, ‖Θ y.out‖ ^ 2 ∂μG ≤
        Nat.card (weylParameterSet p l p l π) *
          ∫ x, (inducedInnerProduct K hK.isCompact p l μM e β (φ x) (φ x)).re
            ∂(spectralMeasure n)

/-- The inner product `(·,·)_P` (`inducedInnerProduct`, Lapid §2, p.311) is sesquilinear on
finite linear combinations of elements `v j` of `A^2_P`: for a parabolic `P = MU` with
presentation `r` and a Levi projection `π` (`l ≫ π = 𝟙`), a maximal compact `K` with
`P(𝔸)K = G(𝔸)`, an Iwasawa-compatible Haar
measure `μ_M`, coordinates `e` and a continuous compactly supported weight `β` with `∫ β = 1`,
`(∑ j, z j v j, ∑ j, z' j v j)_P = ∑ j, ∑ j', z j · conj (z' j') · (v j, v j')_P`. This holds
because the integral defining `(φ, ψ)_P` converges absolutely for `φ, ψ ∈ A^2_P`. -/
def InducedInnerProductSesquilinearStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
    ∀ z z' : Fin k → ℂ,
      inducedInnerProduct K hK.isCompact p l μM e β (fun g => ∑ j, z j * v j g)
          (fun g => ∑ j, z' j * v j g) =
        ∑ j, ∑ j', z j * (starRingEnd ℂ) (z' j') *
          inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j')

/-- Levi decomposition (Getz–Hahn, Theorem 1.5.8 and Definition 1.5.9, p.16): for a parabolic
`P = MU` of a connected reductive `G` over a number field, with unipotent radical `U` and
rational Levi subgroup `l : M → P` (presented by `r`), `P` is the semidirect product of `M` and
`U`, so there is a Levi projection `π : P → M`, a homomorphism with `l ≫ π = 𝟙 M` (the
quotient map `P → P/U ≅ M`). -/
def LeviProjectionExistenceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∃ π : P ⟶ M, l ≫ π = 𝟙 M

/-- Iwasawa integration formula (Getz–Hahn, Exercise 3.5, p.99): for a parabolic `P = MU` of
a connected reductive `G` and a maximal compact subgroup `K` of `G(𝔸)` with `P(𝔸)K = G(𝔸)`,
Haar measures can be normalized so that `dg = d_l p dk`; with `d_l(um) = δ_P(m)⁻¹ du dm` this
gives a Haar measure `μ_M` on `M(𝔸)` with
`∫_G f = ∫_K ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dμ_M(m) dk` (`IsIwasawaCompatibleMeasure`), for
Mathlib's Haar measure on `G(𝔸)`, `vol(U(F) \ U(𝔸)) = 1` and `vol(K) = 1`. -/
def WavePacketIwasawaCompatibleMeasureExistenceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K),
      IsMaximalCompactSubgroup F G K →
    ∃ μM : Measure (AdelicGroupPoints F M), μM.IsHaarMeasure ∧
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM

end Langlands.Global
