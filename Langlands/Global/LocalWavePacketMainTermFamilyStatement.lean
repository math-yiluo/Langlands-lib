import Langlands.Global.LocalWavePacketSomeCompactReduction
import Langlands.Global.AdelicTruncatedEisensteinFamilyAsymptoticsStatement

/-! # The `(G, M)`-family of the main terms in Lapid's §8

Lapid 2011, §8, p.328, after Arthur 1982, §§1–2: on the imaginary axis the inner products
`(M(t, λ)φ(λ), M(t', λ')φ'(λ'))_S` that make up the main term of formula (2) are the values of a
`(G, M)`-family, and the value of this family at the origin is the inner product in the right
side of formula (4).

* `WavePacketMainTermFamilyStatement`: for standard parabolic subgroups `P = P_J`, `P' = P_{J'}`
  and expansions of the intertwined families in `A^2_S` for every standard `S`, (i) the inner
  products for two pairs of Weyl elements related by an elementary symmetry `s` that fixes the
  wall `⟨μ, α^∨⟩ = 0` agree on that wall, when the measures on `𝔞_S` and `𝔞_{S'}` correspond under
  `s`; (ii) at `λ' = wλ` the inner product for `S = P` and the trivial Weyl element is
  `(M(w, λ)φ(λ), φ'(wλ))_{P'}`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology Classical

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- **Lapid 2011, §8, p.328 (after Arthur 1982, §§1–2): the inner products of the main term
form a `(G, M)`-family.** The setting is that of `WavePacketMainTermLimitStatement`: a number
field `F`, a connected reductive `G`, a maximal split torus `i : T → G`, a generic cocharacter
`ν`, a maximal compact `K` with `Q(𝔸)K = G(𝔸)` for every standard `Q`, reflection data `D`, Levi
projections `π S` and Iwasawa-compatible Haar measures `μM S` for every standard `S`, two standard
parabolic subgroups `P = P_J`, `P' = P_{J'}` with families `φ_j(λ) = ∑_l b_{j,l}(λ) v_{j,l}` and
`φ'_{j'}(λ') = ∑_{l'} b'_{j',l'}(λ') v'_{j',l'}` of vectors of `A^2_P` and `A^2_{P'}`, the
expansions `M(w, λ)φ_j(λ) = ∑_a coeff_{w,j,a}(λ) ψ_{w,j,a}` in `A^2_{P'}` for representatives
`w` of `Ω(P, P')`, and for every standard `S` the expansions
`M(t, λ)φ_j(λ) = ∑_a coeffS_{S,t,j,a}(λ) ψS_{S,t,j,a}` in `A^2_S` for representatives `t` of
`Ω(P, S)` and `M(t', λ')φ'_{j'}(λ') = ∑_{a'} coeffS'_{S,t',j',a'}(λ') ψS'_{S,t',j',a'}` for
representatives `t'` of `Ω(P', S)`, all for `Re λ` sufficiently regular, with coefficients
meromorphic and holomorphic on the open sets `DM`, `DMS`, `DMS'`.

For coordinates `e` of `𝔞_S^*` and a weight `β` put
`F^{e,β}_{S,t,t'}(λ, λ') = ∑_{a,a'} coeffS_{S,t,j,a}(λ) conj(coeffS'_{S,t',j',a'}(λ'))
(ψS_{S,t,j,a}, ψS'_{S,t',j',a'})_S`, the inner product `(·,·)_S` being
`inducedInnerProduct` for `μM S`, `e` and `β`. On the imaginary axis this is
`(M(t, λ)φ_j(λ), M(t', λ')φ'_{j'}(λ'))_S`. The statement asserts, for imaginary `λ ∈ DMS` and
`λ' ∈ DMS'`:

1. (`(G, M)`-family.) Let `(ws, cs)` present an element `s ∈ Ω(S, S₂)` that fixes the
   hyperplane `⟨μ, α^∨⟩ = 0` of `𝔞_S^*` pointwise (as a subspace of `𝔞_0^*`), for a simple root
   `α ∉ S`, and let `t₂`, `t₂'` be representatives with `t₂ = s t` and `t₂' = s t'` on
   parameters. If `⟨tλ + t'λ̄', α^∨⟩ = 0`, then `F^{e,β}_{S,t,t'}(λ, λ') =
   F^{s e,β}_{S₂,t₂,t₂'}(λ, λ')` for all coordinates `e` and weights `β` with `∫ β = 1`.
   This is the rank-one property of `M(s, ·)` together with its unitarity and the functional
   equations.
2. (Value at the origin.) Let `t₀` represent the identity of `Ω(P, P)`, `w` represent an element
   of `Ω(P, P')` and `t'` its inverse in `Ω(P', P)`, and let `λ ∈ DM` with `wλ ∈ DMS'`. Then
   `F^{e,β}_{P,t₀,t'}(λ, wλ) = ∑_a ∑_{l'} coeff_{w,j,a}(λ) conj(b'_{j',l'}(wλ))
   (ψ_{w,j,a}, v'_{j',l'})_{P'}`, the inner product on `P'` taken for `μM'`, the coordinates
   `w e` and `β`; this is the adjunction `(φ(λ), M(t', wλ)φ'(wλ))_P =
   (M(w, λ)φ(λ), φ'(wλ))_{P'}`. -/
def WavePacketMainTermFamilyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
  ∀ (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
  ∀ (hK : ∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K)
    (D : RelativeRootReflectionData i),
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
  ∀ (π : ∀ S : StandardIndex hG hi ν,
      Standard.parabolicScheme i ν S.roots ⟶ Standard.leviScheme i ν S.roots),
    (∀ S : StandardIndex hG hi ν,
      Standard.leviToParabolic i ν S.roots ≫ π S = 𝟙 (Standard.leviScheme i ν S.roots)) →
  ∀ (μM : ∀ S : StandardIndex hG hi ν,
      Measure (AdelicGroupPoints F (Standard.leviScheme i ν S.roots))),
    (∀ S : StandardIndex hG hi ν, (μM S).IsHaarMeasure ∧
      IsIwasawaCompatibleMeasure K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
        (Standard.unipotentToParabolic i ν S.roots) (Standard.leviToParabolic i ν S.roots)
        (μM S)) →
  ∀ (J J' : StandardIndex hG hi ν)
    (π' : Standard.parabolicScheme i ν J'.roots ⟶ Standard.leviScheme i ν J'.roots),
    Standard.leviToParabolic i ν J'.roots ≫ π' = 𝟙 (Standard.leviScheme i ν J'.roots) →
  ∀ (μM' : Measure (AdelicGroupPoints F (Standard.leviScheme i ν J'.roots)))
    [μM'.IsHaarMeasure],
    IsIwasawaCompatibleMeasure K (hK J').isCompact (Standard.parabolicHom i ν J'.roots)
      (Standard.unipotentToParabolic i ν J'.roots) (Standard.leviToParabolic i ν J'.roots) μM' →
  ∀ (k q : ℕ) (v : Fin k → Fin q → AdelicGroupPoints F G → ℂ)
    (b : Fin k → Fin q → ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ),
    (∀ j l, IsSquareIntegrableInducedForm K (hK J).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J.roots) (Standard.unipotentToParabolic i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (v j l)) →
    (∀ j l, IsMeromorphicInCoordinatesOn (b j l) Set.univ) →
  ∀ (k' q' : ℕ) (v' : Fin k' → Fin q' → AdelicGroupPoints F G → ℂ)
    (b' : Fin k' → Fin q' → ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) →
      ℂ),
    (∀ j l, IsSquareIntegrableInducedForm K (hK J').isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J'.roots) (Standard.unipotentToParabolic i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (v' j l)) →
    (∀ j l, IsMeromorphicInCoordinatesOn (b' j l) Set.univ) →
  ∀ (Ω : Type) [Fintype Ω] (w : Ω → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cw : Ω → (Standard.leviScheme i ν J'.roots ⟶ Standard.leviScheme i ν J.roots)),
    (∀ t, IsWeylConjugation (Standard.parabolicHom i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (w t) (cw t)) →
  ∀ (mψ : ℕ) (ψ : Ω → Fin k → Fin mψ → AdelicGroupPoints F G → ℂ)
    (coeff : Ω → Fin k → Fin mψ →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (DM : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ t j a, IsSquareIntegrableInducedForm K (hK J').isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J'.roots) (Standard.unipotentToParabolic i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (ψ t j a)) →
    (∀ t j a, IsMeromorphicInCoordinatesOn (coeff t j a) DM) →
    (∀ t j, ∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      ∑ l, b j l lam * (hK J).intertwiningOperator (hK J')
          (Standard.unipotentToParabolic i ν J.roots) (Standard.leviToParabolic i ν J.roots)
          (Standard.unipotentToParabolic i ν J'.roots) (cw t) π' (w t) (v j l) lam g =
        ∑ a, coeff t j a lam * ψ t j a g) →
  ∀ (ΩS : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (ΩS S)]
    (wS : ∀ S : StandardIndex hG hi ν, ΩS S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cwS : ∀ S : StandardIndex hG hi ν, ΩS S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (wS S t) (cwS S t)) →
  ∀ (mS : ℕ) (ψS : ∀ S : StandardIndex hG hi ν, ΩS S → Fin k → Fin mS →
      AdelicGroupPoints F G → ℂ)
    (coeffS : ∀ S : StandardIndex hG hi ν, ΩS S → Fin k → Fin mS →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (DMS : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ (S : StandardIndex hG hi ν) t j a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψS S t j a)) →
    (∀ (S : StandardIndex hG hi ν) t j a, IsMeromorphicInCoordinatesOn (coeffS S t j a) DMS) →
    (∀ (S : StandardIndex hG hi ν) t j, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      ∑ l, b j l lam * (hK J).intertwiningOperator (hK S)
          (Standard.unipotentToParabolic i ν J.roots)
          (Standard.leviToParabolic i ν J.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cwS S t) (π S) (wS S t) (v j l) lam g =
        ∑ a, coeffS S t j a lam * ψS S t j a g) →
  ∀ (ΩS' : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (ΩS' S)]
    (wS' : ∀ S : StandardIndex hG hi ν, ΩS' S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cwS' : ∀ S : StandardIndex hG hi ν, ΩS' S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J'.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (wS' S t) (cwS' S t)) →
  ∀ (mS' : ℕ) (ψS' : ∀ S : StandardIndex hG hi ν, ΩS' S → Fin k' → Fin mS' →
      AdelicGroupPoints F G → ℂ)
    (coeffS' : ∀ S : StandardIndex hG hi ν, ΩS' S → Fin k' → Fin mS' →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) → ℂ)
    (DMS' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    (∀ (S : StandardIndex hG hi ν) t j a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψS' S t j a)) →
    (∀ (S : StandardIndex hG hi ν) t j a, IsMeromorphicInCoordinatesOn (coeffS' S t j a) DMS') →
    (∀ (S : StandardIndex hG hi ν) t j, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J'.roots R lam → ∀ g,
      ∑ l, b' j l lam * (hK J').intertwiningOperator (hK S)
          (Standard.unipotentToParabolic i ν J'.roots)
          (Standard.leviToParabolic i ν J'.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cwS' S t) (π S) (wS' S t) (v' j l) lam g =
        ∑ a, coeffS' S t j a lam * ψS' S t j a g) →
  let innerS (S : StandardIndex hG hi ν) (t : ΩS S) (t' : ΩS' S) (j : Fin k) (j' : Fin k') (n : ℕ)
      (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
      (β : (Fin n → ℝ) → ℝ)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∑ a, ∑ a', coeffS S t j a lam * (starRingEnd ℂ) (coeffS' S t' j' a' lam') *
      inducedInnerProduct K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (μM S) e β (ψS S t j a) (ψS' S t' j' a')
  (∀ (S S₂ : StandardIndex hG hi ν) (t : ΩS S) (t₂ : ΩS S₂) (t' : ΩS' S) (t₂' : ΩS' S₂)
      (ws : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
      (cs : Standard.leviScheme i ν S₂.roots ⟶ Standard.leviScheme i ν S.roots),
      IsWeylConjugation (Standard.parabolicHom i ν S.roots) (Standard.leviToParabolic i ν S.roots)
        (Standard.parabolicHom i ν S₂.roots) (Standard.leviToParabolic i ν S₂.roots) ws cs →
    ∀ α ∈ simpleFinset ν hG hi \ S.1,
      (∀ mu : RealCharacterParameter F (Standard.parabolicScheme i ν S.roots),
        pair T (restrictToTorus F i ν S.roots mu) (corootVector D α) = 0 →
          restrictToTorus F i ν S₂.roots
              (realWeylParameter (Standard.leviToParabolic i ν S.roots) cs (π S₂) mu) =
            restrictToTorus F i ν S.roots mu) →
      weylParameter (Standard.leviToParabolic i ν J.roots) (cwS S₂ t₂) (π S₂) =
        weylParameter (Standard.leviToParabolic i ν S.roots) cs (π S₂) ∘ₗ
          weylParameter (Standard.leviToParabolic i ν J.roots) (cwS S t) (π S) →
      weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' S₂ t₂') (π S₂) =
        weylParameter (Standard.leviToParabolic i ν S.roots) cs (π S₂) ∘ₗ
          weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' S t') (π S) →
    ∀ (x : RealCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (x' : RealCharacterParameter F (Standard.parabolicScheme i ν J'.roots)),
      imaginaryParameter F _ x ∈ DMS → imaginaryParameter F _ x' ∈ DMS' →
      complexParameterPairing F _
          (weylParameter (Standard.leviToParabolic i ν J.roots) (cwS S t) (π S)
              (imaginaryParameter F _ x) +
            weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' S t') (π S)
              (parameterConj F _ (imaginaryParameter F _ x')))
          (toCharacterDual F i ν S.roots (corootVector D α)) = 0 →
    ∀ (j : Fin k) (j' : Fin k') {n : ℕ}
      (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
      (e₂ : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν S₂.roots)),
      (∀ y, e₂ y = realWeylParameter (Standard.leviToParabolic i ν S.roots) cs (π S₂) (e y)) →
    ∀ β : (Fin n → ℝ) → ℝ, Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
      innerS S t t' j j' n e β (imaginaryParameter F _ x) (imaginaryParameter F _ x') =
        innerS S₂ t₂ t₂' j j' n e₂ β (imaginaryParameter F _ x) (imaginaryParameter F _ x')) ∧
  (∀ (t₀ : ΩS J) (tw : Ω) (t' : ΩS' J),
      weylParameter (Standard.leviToParabolic i ν J.roots) (cwS J t₀) (π J) = LinearMap.id →
      weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' J t') (π J) ∘ₗ
          weylParameter (Standard.leviToParabolic i ν J.roots) (cw tw) π' = LinearMap.id →
    ∀ x : RealCharacterParameter F (Standard.parabolicScheme i ν J.roots),
      imaginaryParameter F _ x ∈ DM → imaginaryParameter F _ x ∈ DMS →
      weylParameter (Standard.leviToParabolic i ν J.roots) (cw tw) π'
          (imaginaryParameter F _ x) ∈ DMS' →
    ∀ (j : Fin k) (j' : Fin k') {n : ℕ}
      (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (e₂ : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J'.roots)),
      (∀ y, e₂ y = realWeylParameter (Standard.leviToParabolic i ν J.roots) (cw tw) π' (e y)) →
    ∀ β : (Fin n → ℝ) → ℝ, Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
      innerS J t₀ t' j j' n e β (imaginaryParameter F _ x)
          (weylParameter (Standard.leviToParabolic i ν J.roots) (cw tw) π'
            (imaginaryParameter F _ x)) =
        ∑ a, ∑ l', coeff tw j a (imaginaryParameter F _ x) *
          (starRingEnd ℂ) (b' j' l' (weylParameter (Standard.leviToParabolic i ν J.roots)
            (cw tw) π' (imaginaryParameter F _ x))) *
          inducedInnerProduct K (hK J').isCompact (Standard.parabolicHom i ν J'.roots)
            (Standard.leviToParabolic i ν J'.roots) μM' e₂ β (ψ tw j a) (v' j' l'))

end Langlands.Global
