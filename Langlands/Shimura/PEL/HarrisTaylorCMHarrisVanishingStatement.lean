import Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower
import Langlands.JacquetLanglands.HarrisTransfer
import Langlands.Representation.Classification.Supercuspidal

/-! # Harris (1999), (5.1): the `JL(π_f)`-isotypic part of `H^j(S_U, W)_λ` vanishes for
`j ≠ n - 1`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39
(1999), §5, formula (5.1), printed p. 312, stated for the Library's CM Shimura varieties of
Harris's signature, the Library's `λ`-adic cohomology with coefficients in an algebraic
representation `ρ` (`HarrisTaylorCMLambdaTower`), and the published transfer relation
`JL(π_f)` (`JacquetLanglands.IsHarrisJacquetLanglandsTransfer`), under Harris's hypothesis (R)
of [H1] (Harris 1997, printed p. 79).
See `HarrisTaylorCMHarrisVanishingStatement.md`.
-/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Global AdelicFunctoriality

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)
  (U : SmallCMLevel D)

/-! Harris's inner form `GJ` (algebra `D'`) and the data of the transfer `JL` at the place `w₀`
of `F` above the split place `𝔭` of `L` over `p` (`JacquetLanglands.HarrisTransfer`). -/

variable {D' : Type} [Ring D'] [Algebra F D'] [Algebra E D'] [Algebra ℚ D']
  [IsScalarTower ℚ E D'] [IsScalarTower ℚ F D'] [Module.Finite ℚ D']
  (σJ : SecondKindInvolution E F D')
  (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (𝔭 : FinitePlacesAbove L v.1)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1))
  (w₀ : letI := (algebraMap L F).toAlgebra; FinitePlacesAbove F 𝔭.1)
  (s : w₀.1.adicCompletion F ⊗[F] D' ≃ₐ[w₀.1.adicCompletion F]
    Matrix (Fin n) (Fin n) (w₀.1.adicCompletion F))
  (Δ : Type) [DivisionRing Δ] [Algebra (w₀.1.adicCompletion F) Δ]
  [FiniteDimensional (w₀.1.adicCompletion F) Δ] [Algebra.IsCentral (w₀.1.adicCompletion F) Δ]
  [TopologicalSpace Δ] [IsModuleTopology (w₀.1.adicCompletion F) Δ]
  (t : w₀.1.adicCompletion F ⊗[F] A ≃ₐ[w₀.1.adicCompletion F] Δ)
  (f : ∀ w : {w : (letI := (algebraMap L F).toAlgebra; FinitePlacesAbove F 𝔭.1) // w ≠ w₀},
    w.1.1.adicCompletion F ⊗[F] D' ≃ₐ[w.1.1.adicCompletion F] w.1.1.adicCompletion F ⊗[F] A)
  (e : PrimeToFiniteAdeles p ⊗[ℚ] D' ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] A)
  (he : ∀ x, e (σJ.rationalInvolution.baseChange _ x) =
    D.rationalInvolution.baseChange _ (e x))

set_option hygiene false in
/-- The derived-category instances of the Library's `λ`-adic cohomology for the coefficient
prime `ℓ`. -/
local notation "derivedInstances" ℓ =>
  ∀ U' : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U')
        (HarrisCoefficientIntegers K ℓ))

set_option hygiene false in
/-- Harris's splitting of `GJ(A_f)` at `w₀`. -/
local notation "splitJ" => JacquetLanglands.harrisAwaySplitGL σJ (algebraMap L F) p hp v 𝔭 h𝔭 w₀ s

/-- **Harris (1999), (5.1)**, printed p. 312: `H^j(S_K(N), W)[π] = 0` for `j ≠ n - 1`.

Hypotheses: Harris's condition (R) of [H1] (1997, printed p. 79): at every finite place `w` of
`F`, the algebra `F_w ⊗_F A` is split (isomorphic to `M_n(F_w)`) or a division algebra (every
nonzero element is a unit); `ρ' = JL(π_f)` (`IsHarrisJacquetLanglandsTransfer`) for a
representation `π_f` of `GJ(A_f)` whose component at `w₀` is supercuspidal; `τ` is a model of
`ρ'` over a field `M` extending `K_λ`, through a field isomorphism `j : M ≃+* ℂ`.

Conclusion: for every degree `d ≠ n - 1`, the vectors fixed by the level of `U` in the
`τ`-isotypic part of `H^d(S, W)_λ ⊗_{K_λ} M` (the Library's `H^d(S_U, W)[τ]`,
`cmHarrisLambdaTowerIsotypicFixedVectors`) are zero.
See `HarrisTaylorCMHarrisVanishingStatement.md`. -/
def CMHarrisVanishingStatement : Prop :=
  (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    Nonempty (w.adicCompletion F ⊗[F] A ≃ₐ[w.adicCompletion F]
        Matrix (Fin n) (Fin n) (w.adicCompletion F)) ∨
      ∀ x : w.adicCompletion F ⊗[F] A, x ≠ 0 → IsUnit x) →
  ∀ {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (πf : Representation ℂ σJ.rationalInvolution.FiniteAdelicPoints V)
    (ρ' : Representation ℂ D.rationalInvolution.FiniteAdelicPoints V'),
    JacquetLanglands.IsHarrisJacquetLanglandsTransfer σJ D.toSecondKindInvolution
      (algebraMap L F) p hp v 𝔭 h𝔭 w₀ n s Δ t f e he πf ρ' →
    (∃ (X Y : ModuleCat.{0} ℂ) (πv : Representation ℂ (GeneralLinear n (w₀.1.adicCompletion F)) X)
        (πaway : Representation ℂ
          (JacquetLanglands.HarrisAwayComplement σJ (algebraMap L F) p v 𝔭 w₀) Y),
      GeneralLinear.IsSupercuspidal πv ∧
        Nonempty (πf.Equiv (JacquetLanglands.splitTensor (splitJ) πv πaway))) →
    ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances ℓ]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ)
      (M : Type) [Field M] [Algebra (FiniteCompletion K lam.1) M]
      (j : M ≃+* ℂ)
      {V'' : Type} [AddCommGroup V''] [Module M V'']
      (τ : Representation M D.rationalInvolution.FiniteAdelicPoints V'') (eτ : V' ≃+ V''),
      (∀ (z : ℂ) (x : V'), eτ (z • x) = j.symm z • eτ x) →
      (∀ g (x : V'), eτ (ρ' g x) = τ g (eτ x)) →
    ∀ d : ℕ, d ≠ n - 1 →
      Subsingleton (cmHarrisLambdaTowerIsotypicFixedVectors D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
        hRigid lam d M τ U).V

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
