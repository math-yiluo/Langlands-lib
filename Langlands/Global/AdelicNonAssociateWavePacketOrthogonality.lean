import Langlands.Global.AdelicWavePacketInnerProductStatement
import Langlands.Global.AdelicIwasawaCompatibleMeasureProof
import Langlands.GroupScheme.Rational.LeviRetraction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Orthogonality of wave packets of non-associate parabolics on `G(F) \ G(𝔸)`

Lapid 2011, Proposition 2, in the case `Ω(P, P') = ∅`: if no rational point of `G` conjugates
the Levi subgroup of `P` to that of `P'`, a wave packet of `P` and a wave packet of `P'` are
square integrable on `G(F) \ G(𝔸)` and orthogonal there.

* `IsParabolicWavePacket`: `Θ` is a wave packet of one presented parabolic `P` over all of
  `i𝔞_P^*`, with the data of `WavePacketInnerProductStatement`.
* `NonAssociateWavePacketOrthogonalityStatement`: the orthogonality statement.
* `nonAssociateWavePacketOrthogonality_of_innerProduct`: it follows from the published
  `WavePacketInnerProductStatement` (Lapid's Proposition 2), applied with an empty enumeration
  of `Ω(P, P')`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate

set_option autoImplicit false

universe u

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Predicate

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- `Θ` is a wave packet of Eisenstein series of the presented parabolic `P` over all of
`i𝔞_P^*` (Lapid 2011, §3, p.314, `Θ_{P,φ}` for `φ ∈ W_P`):
`Θ(g) = ∫ ∑ j, c j x · E j (i e(x))(g) dx`, where `e` are coordinates on `X^*(P) ⊗ ℝ`,
`v j ∈ A^2_P`, the `c j` are smooth and compactly supported, and `E j` is a meromorphic
continuation of the Eisenstein series `E(v j, λ)` with one domain of holomorphy `D ⊇ i𝔞_P^*`.
These are the conditions that `WavePacketInnerProductStatement` imposes on each of its two
wave packets. It differs from `IsRelativeWavePacket` only in that the coordinates `e` range
over all of `X^*(P) ⊗ ℝ` instead of `relativeParameterSpace p`. -/
def IsParabolicWavePacket (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : U ⟶ P) (l : M ⟶ P)
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (Θ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (k : ℕ)
    (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
    (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F P)),
    (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) ∧
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ HasCompactSupport (c j)) ∧
    Set.range (imaginaryParameter F P) ⊆ D ∧
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) ∧
    (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      E j lam = hK.eisensteinSeries (v j) lam) ∧
    Θ = fun g => ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)

end Predicate

section Statement

/-- **Orthogonality of wave packets of non-associate parabolics on `G(F) \ G(𝔸)`** (Lapid 2011,
Proposition 2, (4), when `Ω(P, P') = ∅`; Arthur 2005, Theorem 7.2(b)). Let `G` be connected
reductive over a number field, `K` a maximal compact subgroup of `G(𝔸)`, `rho` a closed matrix
embedding, and `P = MU`, `P' = M'U'` presented parabolics with geometric unipotent radicals
and `P(𝔸)K = P'(𝔸)K = G(𝔸)`. If no rational point `w` of `G` and no `c : M' → M` satisfy
`IsWeylConjugation p l p' l' w c`, then every wave packet `Θ` of `P` and every wave packet `Θ'`
of `P'` (`IsParabolicWavePacket`) are square integrable on `G(F) \ G(𝔸)`, for the quotient
`μG` of Mathlib's Haar measure on `G(𝔸)` by counting measure on `G(F)`, and
`∫ Θ(y.out) · conj Θ'(y.out) dμG = 0`. -/
def NonAssociateWavePacketOrthogonalityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iU' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (¬ ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
        IsWeylConjugation p l p' l' w c) →
      ∀ Θ Θ' : AdelicGroupPoints F G → ℂ,
        IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
        IsParabolicWavePacket hK' rho hsmooth hcalc iU' l' r' hA' hT' Θ' →
        let μG : Measure (RationalQuotient F G) :=
          LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
            (isDiscrete_rationalSubgroup F G) Measure.haar
        MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG ∧
          MemLp (fun y : RationalQuotient F G => Θ' y.out) 2 μG ∧
          ∫ y, Θ y.out * conj (Θ' y.out) ∂μG = 0

end Statement

section Proof

/-- If no pair `(w, c)` satisfies `IsWeylConjugation p l q l' w c`, the Weyl set
`Ω(P, Q) = weylParameterSet p l q l' π'` is empty. -/
theorem weylParameterSet_eq_empty_of_not_weylConjugation {F : Type u} [Field F] [NumberField F]
    {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G}
    {l' : M' ⟶ Q} (π' : Q ⟶ M')
    (h : ¬ ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
      IsWeylConjugation p l q l' w c) :
    weylParameterSet p l q l' π' = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun s hs => ?_
  obtain ⟨w, c, hwc, -⟩ := hs
  exact h ⟨w, c, hwc⟩

/-- **Lapid's Proposition 2 gives the orthogonality of non-associate wave packets.** Apply
`WavePacketInnerProductStatement` with a Levi projection of `P'`
(`IsRationalLeviSubgroup.exists_unipotentRadical_retraction`), an Iwasawa-compatible Haar
measure on `M'(𝔸)` (`iwasawaCompatibleMeasureExistence`), a normalized bump weight, and the
empty enumeration of `Ω(P, P')`, which is empty by
`weylParameterSet_eq_empty_of_not_weylConjugation`. The right side of (4) is then the integral
of an empty sum. -/
theorem nonAssociateWavePacketOrthogonality_of_innerProduct
    (hWP : WavePacketInnerProductStatement) : NonAssociateWavePacketOrthogonalityStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT p' _ iU' l' a'
    r' _ _ _ hA' hT' hG hU hU' K hK hK' N d rho hsmooth hcalc hKmax hrho hn Θ Θ' hΘ hΘ' μG
  obtain ⟨n, e, k, v, c, E, D, hv, hc, hD, hE, hreg, rfl⟩ := hΘ
  obtain ⟨n', e', k', v', c', E', D', hv', hc', hD', hE', hreg', rfl⟩ := hΘ'
  have : IsClosedImmersion (iU ≫ p).hom.hom.left :=
    IsClosedSubgroup.comp (i := iU) (j := p) hU.1.isClosedSubgroup
      ‹IsClosedImmersion p.hom.hom.left›
  have : IsClosedImmersion (iU' ≫ p').hom.hom.left :=
    IsClosedSubgroup.comp (i := iU') (j := p') hU'.1.isClosedSubgroup
      ‹IsClosedImmersion p'.hom.hom.left›
  -- a Levi projection of `P'`, a compatible Haar measure on `M'(𝔸)` and a weight on `ℝ^{n'}`
  obtain ⟨-, -, π', -, -, hπ', -⟩ := r'.isCompatible.levi.exists_unipotentRadical_retraction
  obtain ⟨μM', hμM'Haar, hμM'⟩ :=
    iwasawaCompatibleMeasureExistence F G P' M' U' A' p' iU' l' a' r' hG hU' K hK' hKmax
  have := hμM'Haar
  let bump : ContDiffBump (0 : Fin n' → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  -- Lapid's Proposition 2 with the empty enumeration of `Ω(P, P')`
  have hempty := weylParameterSet_eq_empty_of_not_weylConjugation (p := p) (l := l) π' hn
  obtain ⟨h1, h2, h3⟩ := hWP F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT'
    π' hG hU hU' hπ' K hK hK' rho hsmooth hcalc hKmax hrho μM' hμM' e e'
    (bump.normed volume) bump.continuous_normed bump.hasCompactSupport_normed
    bump.integral_normed k v c E D hv hc hD hE hreg k' v' c' E' D' hv' hc' hD' hE' hreg'
    Empty Empty.elim Empty.elim (fun t => t.elim) (fun t => t.elim)
    (fun s hs => by rw [hempty] at hs; exact hs.elim) 0 Empty.elim Empty.elim Set.univ
    (fun t => t.elim) (Set.subset_univ _) (fun t => t.elim) (fun t => t.elim)
  refine ⟨h1, h2, h3.trans ?_⟩
  simp

end Proof

end Langlands.Global
