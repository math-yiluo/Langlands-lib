import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.ArthurTruncationL2Statement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Asymptotics of truncated inner products of Eisenstein series

Lapid 2011, Proposition 1 (p.313, formula (2)), for the adelic Eisenstein series, intertwining
operators and norm-one truncation of the Library, under local regularity: the parameters range
over a compact set on which the meromorphic continuations are holomorphic.

* `parameterConj`: complex conjugation `λ ↦ λ̄` on `X^*(P) ⊗ ℂ`.
* `corootVector`: the real coroot `α^∨ ∈ 𝔞_0` of a relative root.
* `IsStandardRegularParameter`: `Re λ` is `R`-regular in the positive chamber of a standard
  parabolic subgroup, `R < ⟨Re λ, α^∨⟩` for `α ∈ Δ_0 ∖ Δ_0^P`.
* `corootCovolume`: `vol(𝔞_Q^G / L_Q)` for the lattice `L_Q` spanned by the coroots of `Δ_Q`
  (Arthur 1980, p.115), for the measure on `𝔞_Q^G` defined by a Lebesgue measure on `𝔞_Q`
  and one on `𝔞_G`.
* `LocalTruncatedEisensteinInnerProductStatement`: the proposition. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct CompactlySupported Classical

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

section Conjugation

variable (F : Type) [Field F] (P : GroupScheme (Spec (CommRingCat.of F)))

/-- Complex conjugation `λ ↦ λ̄` on `X^*(P) ⊗ ℂ`, applied to the scalar factor. It is real
linear. -/
def parameterConj : ComplexCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
  AlgebraTensorModule.map Complex.conjAe.toLinearMap LinearMap.id

theorem parameterConj_tmul (s : ℂ) (χ : GroupScheme.rationalCharacters P) :
    parameterConj F P (s ⊗ₜ[ℤ] χ) = (starRingEnd ℂ) s ⊗ₜ[ℤ] χ :=
  rfl

/-- On imaginary parameters `λ = i m`, `m ∈ X^*(P) ⊗ ℝ`, conjugation is `λ̄ = −λ`. -/
theorem parameterConj_imaginaryParameter [NumberField F] (m : RealCharacterParameter F P) :
    parameterConj F P (imaginaryParameter F P m) = -imaginaryParameter F P m := by
  induction m using TensorProduct.inductionOn with
  | tmul t χ =>
    change (starRingEnd ℂ) (t • Complex.I) ⊗ₜ[ℤ] χ = -((t • Complex.I) ⊗ₜ[ℤ] χ)
    rw [← TensorProduct.neg_tmul]
    congr 1
    apply Complex.ext <;> simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]

end Conjugation

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces

section Instances

variable {F : Type} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (S : Set (characterLattice T))

scoped instance instLocallyOfFiniteTypeStandardParabolic [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (Standard.parabolicScheme i ν S).X.hom :=
  (Standard.isClosedSubgroup_parabolicHom i ν S).locallyOfFiniteType

scoped instance instAffineHomStandardLevi : IsAffineHom (Standard.leviScheme i ν S).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν S).isAffineHom

scoped instance instAffineStandardLevi : IsAffine (Standard.leviScheme i ν S).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν S).X.hom

scoped instance instLocallyOfFiniteTypeStandardLevi [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (Standard.leviScheme i ν S).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν S).locallyOfFiniteType

scoped instance instClosedStandardUnipotentComp :
    IsClosedImmersion
      (Standard.unipotentToParabolic i ν S ≫ Standard.parabolicHom i ν S).hom.hom.left := by
  rw [Standard.unipotentToParabolic_comp]
  exact Standard.isClosedSubgroup_unipotentHom i ν S

end Instances

section Combinatorics

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- The real coroot `α^∨ ∈ 𝔞_0 = V T` of a relative root `α`, given by the reflection data `D`
(`RelativeRootReflectionData.realCoroot`); `0` for a character that is not a relative root. -/
def corootVector (D : RelativeRootReflectionData i) (α : characterLattice T) : V T :=
  if h : α ∈ relativeRoots i then D.realCoroot ⟨α, h⟩ else 0

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)

/-- The standard parabolic subgroups `Q ⊇ P_0`, indexed by `Δ_0^Q ⊆ Δ_0`. -/
abbrev StandardIndex : Type := ↥(simpleFinset ν hG hi).powerset

/-- The set `Δ_0^Q` of simple roots of the Levi component of the standard parabolic subgroup `Q`
indexed by `S`. -/
abbrev StandardIndex.roots {hG : IsConnectedReductive G} {hi : IsMaximalSplitTorus i}
    {ν : cocharacterLattice T} (S : StandardIndex hG hi ν) : Set (characterLattice T) :=
  ((S : Finset (characterLattice T)) : Set (characterLattice T))

variable {ν} in
/-- A complex parameter `λ ∈ 𝔞_{P,ℂ}^* = X^*(P) ⊗ ℂ` of the standard parabolic subgroup `P` with
`Δ_0^P = J` is `R`-regular when `R < ⟨Re λ, α^∨⟩` for every `α ∈ Δ_0 ∖ J`, with `Re λ ∈ 𝔞_P^*`
read in `𝔞_0^*` by restriction to the maximal split torus (`restrictToTorus`). For large `R` these
parameters are those whose real part is sufficiently regular in the positive chamber of
`𝔞_P^*` (Lapid 2011, §2, pp.311–312). -/
def IsStandardRegularParameter (D : RelativeRootReflectionData i) (J : Set (characterLattice T))
    (R : ℝ) (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J)) : Prop :=
  ∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
    R < pair T (restrictToTorus F i ν J (parameterRealPart F _ lam)) (corootVector D α)

/-- `vol(𝔞_Q^G / L_Q)` for the standard parabolic subgroup `Q` indexed by `S`, where `L_Q` is the
lattice of `𝔞_Q^G` spanned by the coroots `α^∨`, `α ∈ Δ_Q` (Arthur 1980, p.115). The coroot of
`α ∈ Δ_Q`, the restriction of `α_0 ∈ Δ_0 ∖ Δ_0^Q`, is the image of `α_0^∨` in
`𝔞_Q = Hom(X^*(Q), ℝ)` (`toCharacterDual`). The measure on `𝔞_Q` is Lebesgue measure in the
coordinates `parameterCoordinates F Q e` dual to `e`; the measure on `𝔞_G` is Lebesgue measure in
the basis `c` of `𝔞_G ⊆ 𝔞_0` (`relativeCentralDirections`); the measure on `𝔞_Q^G` is the one
with `d𝔞_Q = d𝔞_Q^G · d𝔞_G`. With these measures the volume is that of the parallelepiped in
`𝔞_Q` spanned by the coroots `α^∨`, `α ∈ Δ_Q`, and the images of the `c k`. -/
def corootCovolume (D : RelativeRootReflectionData i) (S : StandardIndex hG hi ν) {n m : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
    (c : Fin m → V T) : ℝ :=
  (volume (parallelepiped fun b : ↥(simpleFinset ν hG hi \ S.1) ⊕ Fin m =>
    parameterCoordinates F _ e
      (toCharacterDual F i ν S.roots (Sum.elim (fun α => corootVector D α.1) c b)))).toReal

end Combinatorics

end Langlands.Global.ArthurTruncation

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- **Lapid 2011, Proposition 1 (p.313, formula (2)), under local regularity, for a chosen
compact subgroup.**

Setting (Lapid §2, p.311): a connected reductive `G` over a number field `F`, a maximal split
torus `i : T → G` and a generic cocharacter `ν` (the minimal parabolic `P_0`). Lapid fixes a
maximal compact `K` in good position with respect to `M_0`; as in
`TruncationProjectionStatement`, the proposition asserts that there is a maximal compact subgroup
`K` of `G(𝔸)` with `Q(𝔸)K = G(𝔸)` for every standard parabolic `Q` and with `P_0(𝔸) ∩ K`
commuting with the positive torus of every Siegel setup, for which the conclusion holds for all
reflection data `D` (the coroots), the comparison `hρ` used by the truncation operator, and all
the data below. Standard parabolic subgroups are indexed by `S : StandardIndex hG hi ν`
(`Δ_0^Q = S.roots`), with the Library's closed representatives of `Q`, `M_Q`, `N_Q`, and Levi
projections `π S`.

Normalizations: Haar measures `μM S` on `M_Q(𝔸)` compatible with Mathlib's Haar measure on
`G(𝔸)` for the Iwasawa decomposition; Lebesgue measure on `𝔞_Q` in the coordinates dual to
`e S`, with weights `β S` of integral `1` (so `inducedInnerProduct` is `(·,·)_Q`); Lebesgue
measure on `𝔞_G` in a basis `c` of `𝔞_G ⊆ 𝔞_0`; a Haar measure `μ₁` on `G(𝔸)¹` with
`dg = dμ₁ · d𝔞_G`, expressed through a section `s` of `H_G` over `𝔞_G`; the quotient measure
on `G(F) \ G(𝔸)¹` induced by `μ₁`; and `corootCovolume` for `vol(𝔞_Q^G / L_Q)`.

Data: `v ∈ A^2_P` and `v' ∈ A^2_{P'}` for standard `P`, `P'` (indexed by `J`, `J'`);
continuations `E`, `E'` of the Eisenstein series, meromorphic in coordinates with domains of
holomorphy `DE`, `DE'`; for every standard `Q`, the set `Ω(P, Q)` enumerated without repetition
by Weyl conjugation data `(w S t, cw S t)`, `t : Ω S`, and finite expansions
`M(w, λ)v = ∑ a, coeff S t a λ • ψ S t a` of the normalized intertwining operators
(`intertwiningOperator`) with `ψ S t a ∈ A^2_Q` and coefficients meromorphic with domain of
holomorphy `DM`, for sufficiently regular `λ`; the same for `P'`.

Conclusion: for every cone generated by finitely many vectors `gen j` of the open positive
chamber of `𝔞_0`, and every compact set `C` of coordinate pairs `(x, x')` with
`λ = i e_P(x) ∈ i(𝔞_P^G)^*` in `DE ∩ DM` and `λ' = i e_{P'}(x') ∈ i(𝔞_{P'}^G)^*` in `DE' ∩ DM'`,
there are `δ > 0`, a constant and a threshold such that for `T = ∑ τ_j gen_j` (`τ_j ≥ 0`) with
`∑ τ_j` beyond the threshold, the truncations `Λ^T E(λ)`, `Λ^T E'(λ')` are square integrable on
`G(F) \ G(𝔸)¹` and, for `(λ, λ')` off the hyperplanes `⟨wλ + w'λ̄', α^∨⟩ = 0`,
`|(Λ^T E(λ), Λ^T E'(λ'))_{G(F)\G(𝔸)¹} − M(T; λ, λ')| ≤ const · e^{−δ ∑ τ_j}`, where
`M(T; λ, λ') = ∑_Q ∑_{w, w'} vol(𝔞_Q^G / L_Q) e^{⟨wλ + w'λ̄', T⟩}
(M(w, λ)v, M(w', λ')v')_Q / ∏_{α ∈ Δ_Q} ⟨wλ + w'λ̄', α^∨⟩` and `λ̄' = parameterConj λ'`. -/
def LocalTruncatedEisensteinInnerProductStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
  ∃ K : Subgroup (AdelicGroupPoints F G),
    IsMaximalCompactSubgroup F G K ∧
    IsIwasawaCompact (Standard.parabolicHom i ν ∅) K ∧
    (∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K) ∧
    (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
      AdelicSiegelFactors.IsSiegelAlgebraicSetup F G T i ν T₀ j →
        AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K) ∧
  ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (hK₀ : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hK : ∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K),
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
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
  ∀ (n : StandardIndex hG hi ν → ℕ)
    (e : ∀ S : StandardIndex hG hi ν, (Fin (n S) → ℝ) ≃ₗ[ℝ]
      RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
    (β : ∀ S : StandardIndex hG hi ν, (Fin (n S) → ℝ) → ℝ),
    (∀ S : StandardIndex hG hi ν, Continuous (β S) ∧ HasCompactSupport (β S) ∧ ∫ y, β S y = 1) →
  ∀ (m : ℕ) (c : Fin m → V T), LinearIndependent ℝ c →
    Submodule.span ℝ (Set.range c) = relativeCentralDirections i →
  ∀ (μ₁ : Measure (normOneSubgroup F G)), μ₁.IsHaarMeasure →
  ∀ (s : (Fin m → ℝ) → AdelicGroupPoints F G),
    (∀ (y : Fin m → ℝ) (χ : rationalCharacters G),
      characterLog F G (s y) χ =
        pair T (rationalCharacterRestrictReal i ((1 : ℝ) ⊗ₜ[ℤ] χ)) (∑ k, y k • c k)) →
    (∀ f : C_c(AdelicGroupPoints F G, ℂ),
      ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        ∫ y, ∫ x, f ((x : AdelicGroupPoints F G) * s y) ∂μ₁ ∂(volume : Measure (Fin m → ℝ))) →
  ∀ (J : StandardIndex hG hi ν) (v : AdelicGroupPoints F G → ℂ)
    (E : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) →
      AdelicGroupPoints F G → ℂ)
    (DE : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    IsSquareIntegrableInducedForm K (hK J).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J.roots) (Standard.unipotentToParabolic i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) v →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
    (∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R lam →
      E lam = (hK J).eisensteinSeries v lam) →
  ∀ (Ω : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (Ω S)]
    (w : ∀ S : StandardIndex hG hi ν, Ω S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cw : ∀ S : StandardIndex hG hi ν, Ω S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (w S t) (cw S t)) →
    (∀ S : StandardIndex hG hi ν, Function.Injective
      (fun t => weylParameter (Standard.leviToParabolic i ν J.roots) (cw S t) (π S))) →
    (∀ S : StandardIndex hG hi ν, ∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J.roots)
        (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (π S),
      ∃ t, weylParameter (Standard.leviToParabolic i ν J.roots) (cw S t) (π S) = σ) →
  ∀ (k : ℕ) (ψ : ∀ S : StandardIndex hG hi ν, Ω S → Fin k → AdelicGroupPoints F G → ℂ)
    (coeff : ∀ S : StandardIndex hG hi ν, Ω S → Fin k →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (DM : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ (S : StandardIndex hG hi ν) t a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψ S t a)) →
    (∀ (S : StandardIndex hG hi ν) t a, IsMeromorphicInCoordinatesOn (coeff S t a) DM) →
    (∀ (S : StandardIndex hG hi ν) t, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      (hK J).intertwiningOperator (hK S) (Standard.unipotentToParabolic i ν J.roots)
          (Standard.leviToParabolic i ν J.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cw S t) (π S) (w S t) v lam g =
        ∑ a, coeff S t a lam * ψ S t a g) →
  ∀ (J' : StandardIndex hG hi ν) (v' : AdelicGroupPoints F G → ℂ)
    (E' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) →
      AdelicGroupPoints F G → ℂ)
    (DE' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    IsSquareIntegrableInducedForm K (hK J').isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J'.roots) (Standard.unipotentToParabolic i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) v' →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) DE') →
    (∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J'.roots R lam →
      E' lam = (hK J').eisensteinSeries v' lam) →
  ∀ (Ω' : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (Ω' S)]
    (w' : ∀ S : StandardIndex hG hi ν, Ω' S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cw' : ∀ S : StandardIndex hG hi ν, Ω' S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J'.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (w' S t) (cw' S t)) →
    (∀ S : StandardIndex hG hi ν, Function.Injective
      (fun t => weylParameter (Standard.leviToParabolic i ν J'.roots) (cw' S t) (π S))) →
    (∀ S : StandardIndex hG hi ν, ∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J'.roots)
        (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (π S),
      ∃ t, weylParameter (Standard.leviToParabolic i ν J'.roots) (cw' S t) (π S) = σ) →
  ∀ (k' : ℕ) (ψ' : ∀ S : StandardIndex hG hi ν, Ω' S → Fin k' → AdelicGroupPoints F G → ℂ)
    (coeff' : ∀ S : StandardIndex hG hi ν, Ω' S → Fin k' →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) → ℂ)
    (DM' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    (∀ (S : StandardIndex hG hi ν) t a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψ' S t a)) →
    (∀ (S : StandardIndex hG hi ν) t a, IsMeromorphicInCoordinatesOn (coeff' S t a) DM') →
    (∀ (S : StandardIndex hG hi ν) t, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J'.roots R lam → ∀ g,
      (hK J').intertwiningOperator (hK S) (Standard.unipotentToParabolic i ν J'.roots)
          (Standard.leviToParabolic i ν J'.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cw' S t) (π S) (w' S t) v' lam g =
        ∑ a, coeff' S t a lam * ψ' S t a g) →
  ∀ (r : ℕ) (gen : Fin r → V T), (∀ j, ∀ α ∈ simpleRelativeRoots i ν, 0 < eval T α (gen j)) →
  ∀ (C : Set ((Fin (n J) → ℝ) × (Fin (n J') → ℝ))), IsCompact C →
    (∀ x ∈ C,
      restrictToTorus F i ν J.roots (e J x.1) ∈ relativeRootSpanReal i ∧
      restrictToTorus F i ν J'.roots (e J' x.2) ∈ relativeRootSpanReal i ∧
      imaginaryParameter F _ (e J x.1) ∈ DE ∩ DM ∧
      imaginaryParameter F _ (e J' x.2) ∈ DE' ∩ DM') →
  let μQ : Measure (NormOneRationalQuotient F G) :=
    LeftCosetSpace.discreteQuotientMeasure (rationalNormOneSubgroup F G)
      (isDiscrete_rationalNormOneSubgroup F G) μ₁
  let ΛE (Tp : V T) (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (q : NormOneRationalQuotient F G) : ℂ :=
    normOneTruncation hG hi D hK₀ hρ Tp (fun x => E lam x) q.out
  let ΛE' (Tp : V T) (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))
      (q : NormOneRationalQuotient F G) : ℂ :=
    normOneTruncation hG hi D hK₀ hρ Tp (fun x => E' lam' x) q.out
  let Λ (S : StandardIndex hG hi ν) (t : Ω S) (t' : Ω' S)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) :
      ComplexCharacterParameter F (Standard.parabolicScheme i ν S.roots) :=
    weylParameter (Standard.leviToParabolic i ν J.roots) (cw S t) (π S) lam +
      weylParameter (Standard.leviToParabolic i ν J'.roots) (cw' S t') (π S)
        (parameterConj F _ lam')
  let denom (S : StandardIndex hG hi ν) (t : Ω S) (t' : Ω' S)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∏ α ∈ simpleFinset ν hG hi \ S.1,
      complexParameterPairing F _ (Λ S t t' lam lam')
        (toCharacterDual F i ν S.roots (corootVector D α))
  let mainTerm (Tp : V T)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∑ S : StandardIndex hG hi ν, ∑ t : Ω S, ∑ t' : Ω' S,
      (corootCovolume hG hi ν D S (e S) c : ℂ) *
        Complex.exp (complexParameterPairing F _ (Λ S t t' lam lam')
          (toCharacterDual F i ν S.roots Tp)) *
        (∑ a, ∑ b, coeff S t a lam * (starRingEnd ℂ) (coeff' S t' b lam') *
          inducedInnerProduct K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
            (Standard.leviToParabolic i ν S.roots) (μM S) (e S) (β S) (ψ S t a) (ψ' S t' b)) /
        denom S t t' lam lam'
  ∃ δ : ℝ, 0 < δ ∧ ∃ B t₀ : ℝ, ∀ τ : Fin r → ℝ, (∀ j, 0 ≤ τ j) → t₀ ≤ ∑ j, τ j →
    ∀ x ∈ C,
      MemLp (ΛE (∑ j, τ j • gen j) (imaginaryParameter F _ (e J x.1))) 2 μQ ∧
      MemLp (ΛE' (∑ j, τ j • gen j) (imaginaryParameter F _ (e J' x.2))) 2 μQ ∧
      ((∀ (S : StandardIndex hG hi ν) t t', denom S t t' (imaginaryParameter F _ (e J x.1))
          (imaginaryParameter F _ (e J' x.2)) ≠ 0) →
        ‖(∫ q, ΛE (∑ j, τ j • gen j) (imaginaryParameter F _ (e J x.1)) q *
              (starRingEnd ℂ) (ΛE' (∑ j, τ j • gen j) (imaginaryParameter F _ (e J' x.2)) q)
            ∂μQ) -
          mainTerm (∑ j, τ j • gen j) (imaginaryParameter F _ (e J x.1))
            (imaginaryParameter F _ (e J' x.2))‖ ≤
        B * Real.exp (-(δ * ∑ j, τ j)))

end Langlands.Global
