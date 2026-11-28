import Langlands.Global.LocalWavePacketStandardReduction

/-! # The truncated limit of Lapid §8 for one pair of parabolic subgroups -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- The conclusion of Lapid's §8 limit for two functions `Θ`, `Θ'` on `G(𝔸)`, a truncation
operator `Λ` indexed by `j : ℕ` and a limit value `rhs`: the functions `y ↦ Θ(y.out)`,
`y ↦ Θ'(y.out)` on `G(F) \ G(𝔸)` are measurable and bounded on compact sets, their truncations
are eventually square integrable with bounded norms, and the truncated inner products tend to
`rhs`. -/
def TruncatedWavePacketLimitConclusion {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (Λ : ℕ → (RationalQuotient F G → ℂ) → RationalQuotient F G → ℂ)
    (Θ Θ' : AdelicGroupPoints F G → ℂ) (rhs : ℂ) : Prop :=
  let μG : Measure (RationalQuotient F G) :=
    LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
      (isDiscrete_rationalSubgroup F G) Measure.haar
  let f : RationalQuotient F G → ℂ := fun y => Θ y.out
  let f' : RationalQuotient F G → ℂ := fun y => Θ' y.out
  Measurable f ∧ Measurable f' ∧
    (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f x‖ ≤ B) ∧
    (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f' x‖ ≤ B) ∧
    (∀ᶠ j : ℕ in atTop, MemLp (Λ j f) 2 μG) ∧
    (∀ᶠ j : ℕ in atTop, MemLp (Λ j f') 2 μG) ∧
    (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
      (∫ y, Λ j f y * (starRingEnd ℂ) (Λ j f y) ∂μG).re ≤ B) ∧
    (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
      (∫ y, Λ j f' y * (starRingEnd ℂ) (Λ j f' y) ∂μG).re ≤ B) ∧
    Tendsto (fun j : ℕ => ∫ y, Λ j f y * (starRingEnd ℂ) (Λ j f' y) ∂μG) atTop (𝓝 rhs)

/-- The limit of truncated inner products of wave packets for one pair of parabolic subgroups,
one compact subgroup `K`, a truncation operator `Λ` (indexed by `j : ℕ`), and regularity
predicates `Reg`, `Reg'` on the parameters of the two parabolic subgroups. The data and the
conclusion are those of `TruncatedWavePacketSectionSomeCompactLimitStatement`, with
`trunc j f = Λ j f`. -/
def TruncatedWavePacketPairLimit {F : Type} [Field F] [NumberField F]
    {G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
    [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [LocallyOfFiniteType P'.X.hom] [IsAffine M'.X.left]
    [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
    (K : Subgroup (AdelicGroupPoints F G))
    (Λ : ℕ → (RationalQuotient F G → ℂ) → RationalQuotient F G → ℂ)
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (hK : IsIwasawaCompact p K) (Reg : ℝ → ComplexCharacterParameter F P → Prop)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left] (π' : P' ⟶ M')
    (hK' : IsIwasawaCompact p' K) (Reg' : ℝ → ComplexCharacterParameter F P' → Prop) : Prop :=
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
  ∀ (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
    IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
  ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n' → ℝ) → ℝ),
    Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
  ∀ (k q : ℕ) (v : Fin k → Fin q → AdelicGroupPoints F G → ℂ)
    (b : Fin k → Fin q → ComplexCharacterParameter F P → ℂ)
    (c : Fin k → (Fin n → ℝ) → ℂ) (S : Set (Fin n → ℝ))
    (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F P)),
    (∀ j i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j i)) →
    (∀ j i, IsMeromorphicInCoordinatesOn (b j i) Set.univ) →
    IsCompact S →
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
    (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
    (∀ j, ∃ R : ℝ, ∀ lam, Reg R lam → ∀ g,
      E j lam g = ∑ i, b j i lam * hK.eisensteinSeries (v j i) lam g) →
  ∀ (k' q' : ℕ) (v' : Fin k' → Fin q' → AdelicGroupPoints F G → ℂ)
    (b' : Fin k' → Fin q' → ComplexCharacterParameter F P' → ℂ)
    (c' : Fin k' → (Fin n' → ℝ) → ℂ) (S' : Set (Fin n' → ℝ))
    (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
    (D' : Set (ComplexCharacterParameter F P')),
    (∀ j i,
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j i)) →
    (∀ j i, IsMeromorphicInCoordinatesOn (b' j i) Set.univ) →
    IsCompact S' →
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ S', c' j x = 0) →
    (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ D' →
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D') →
    (∀ j, ∃ R : ℝ, ∀ lam, Reg' R lam → ∀ g,
      E' j lam g = ∑ i, b' j i lam * hK'.eisensteinSeries (v' j i) lam g) →
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
    (∀ t j, ∃ R : ℝ, ∀ lam, Reg R lam → ∀ g,
      ∑ i, b j i lam * hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t) (v j i) lam g =
        ∑ i, coeff t j i lam * ψ t j i g) →
  TruncatedWavePacketLimitConclusion Λ
    (fun g => ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n))
    (fun g => ∫ x, ∑ j, c' j x * E' j (imaginaryParameter F P' (e' x)) g ∂(spectralMeasure n'))
    (∫ x, ∑ t, ∑ j, ∑ i, ∑ j', ∑ i',
          c j x * coeff t j i (imaginaryParameter F P (e x)) *
            (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
            (starRingEnd ℂ)
              (b' j' i' (weylParameter l (cw t) π' (imaginaryParameter F P (e x)))) *
            inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j' i')
        ∂(spectralMeasure n))

section Monotone

variable {F : Type} [Field F] [NumberField F]
  {G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P'.X.left] [LocallyOfFiniteType P'.X.hom] [IsAffine M'.X.left]
  [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  {Λ : ℕ → (RationalQuotient F G → ℂ) → RationalQuotient F G → ℂ}
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {hK : IsIwasawaCompact p K}
  {p' : P' ⟶ G} [IsClosedImmersion p'.hom.hom.left] {iU' : U' ⟶ P'} {l' : M' ⟶ P'}
  [IsClosedImmersion (iU' ≫ p').hom.hom.left] {π' : P' ⟶ M'}
  {hK' : IsIwasawaCompact p' K}

/-- The limit for the regularity predicates `Reg`, `Reg'` gives the limit for `Reg₁`, `Reg'₁`
when, for every bound, sufficiently `Reg`-regular parameters are `Reg₁`-regular, and likewise
for the second parabolic subgroup: every region `{λ : Reg₁ R₁ λ}` on which an identity is
assumed then contains a region `{λ : Reg R λ}`. -/
theorem TruncatedWavePacketPairLimit.mono_reg
    {Reg Reg₁ : ℝ → ComplexCharacterParameter F P → Prop}
    {Reg' Reg'₁ : ℝ → ComplexCharacterParameter F P' → Prop}
    (h : ∀ R₁ : ℝ, ∃ R : ℝ, ∀ lam, Reg R lam → Reg₁ R₁ lam)
    (h' : ∀ R₁ : ℝ, ∃ R : ℝ, ∀ lam, Reg' R lam → Reg'₁ R₁ lam)
    (hlim : TruncatedWavePacketPairLimit K Λ p iU l hK Reg p' iU' l' π' hK' Reg') :
    TruncatedWavePacketPairLimit K Λ p iU l hK Reg₁ p' iU' l' π' hK' Reg'₁ := by
  intro N d rho hsmooth hcalc hrho μM' _ hμM' n n' e e' β' hβc hβs hβ1 k q v b c S E D hv hb hS
    hc hD hE hEis k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' hEis' T _ w cw hw hinj hsurj
    m ψ coeff DM hψ hDM hcoeff hexp
  refine hlim rho hsmooth hcalc hrho μM' hμM' e e' β' hβc hβs hβ1 k q v b c S E D hv hb hS hc hD
    hE (fun j => ?_) k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' (fun j => ?_) T w cw hw hinj
    hsurj m ψ coeff DM hψ hDM hcoeff (fun t j => ?_)
  · obtain ⟨R₁, hR₁⟩ := hEis j
    obtain ⟨R, hR⟩ := h R₁
    exact ⟨R, fun lam hlam => hR₁ lam (hR lam hlam)⟩
  · obtain ⟨R₁, hR₁⟩ := hEis' j
    obtain ⟨R, hR⟩ := h' R₁
    exact ⟨R, fun lam hlam => hR₁ lam (hR lam hlam)⟩
  · obtain ⟨R₁, hR₁⟩ := hexp t j
    obtain ⟨R, hR⟩ := h R₁
    exact ⟨R, fun lam hlam => hR₁ lam (hR lam hlam)⟩

end Monotone

end Langlands.Global
