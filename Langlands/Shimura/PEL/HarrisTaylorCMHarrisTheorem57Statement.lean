import Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower
import Langlands.Shimura.Unitary.KottwitzBaseChange
import Langlands.JacquetLanglands.HarrisTransfer
import Langlands.Galois.HarrisTwistingCharacter
import Langlands.Galois.UnitaryNormalization
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorEquiv
import Langlands.Shimura.Unitary.HarrisCMTypePlaces

/-! # Harris (1999), Theorem 5.7(i)–(ii), for the Library's `λ`-adic cohomology

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39
(1999), Theorem 5.7(i)–(ii), printed p. 313, stated for the Library's CM Shimura varieties of
Harris's signature, the Library's `λ`-adic cohomology with coefficients in an algebraic
representation `ρ`, and the published transfer relation `JL(π_f)`.
See `HarrisTaylorCMHarrisTheorem57Statement.md`.
-/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Global AdelicFunctoriality
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.RestrictedLevelColimit
open Langlands.Shimura.SmallLevelGaloisTower
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.ContinuousIsotypicGaloisRepresentation
open Langlands.GaloisRepresentation (Objects HasEulerPolynomialAt LambdaAdicCharacter
  unitaryEulerPolynomial)
open Langlands.Shimura.KottwitzUnramified (UnramifiedChart LocalPoints)

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

/-- **Harris (1999), Theorem 5.7(i)–(ii)**, printed p. 313.

Hypotheses: `A` is a division algebra; `ρ' = JL(π_f)` for `π_f` with supercuspidal component at
`w₀` on which the factor `ℚ_p^×` of (4.2) acts trivially; `ξ₀` is the central character of `ρ'`
on the ideles of `L`; `τ` is the model of `ρ'` over `M` through `j : M ≃+* ℂ`; `JL(π_f)` occurs
in `H^{n-1}(S_U, W)_λ` (the isotypic part `Hπ` is nonzero); `ψ` realizes `ν̄(π)` at a place
`lamν` above the same prime `ℓ`, and the continuous embedding `κ` carries it into `M`.

Conclusion: (i) the characteristic polynomials of `[Hπ ⊗ ν̄(π)]^*` are the `a`-th powers of those
of an `n`-dimensional `ρπ`; (ii) outside a finite set of primes, at every place `w` above a
prime where `ρ'` is unramified, `ρπ` is unramified and its normalized Euler polynomial (5.6)
is that of the base change `BC(π)_w`. See `HarrisTaylorCMHarrisTheorem57Statement.md`. -/
def CMHarrisTheorem57Statement : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (πf : Representation ℂ σJ.rationalInvolution.FiniteAdelicPoints V)
    (ρ' : Representation ℂ D.rationalInvolution.FiniteAdelicPoints V'),
    JacquetLanglands.IsHarrisJacquetLanglandsTransfer σJ D.toSecondKindInvolution
      (algebraMap L F) p hp v 𝔭 h𝔭 w₀ n s Δ t f e he πf ρ' →
    (∃ (X Y : ModuleCat.{0} ℂ) (πv : Representation ℂ (GeneralLinear n (w₀.1.adicCompletion F)) X)
        (πaway : Representation ℂ
          (JacquetLanglands.HarrisAwayComplement σJ (algebraMap L F) p v 𝔭 w₀) Y),
      GeneralLinear.IsSupercuspidal πv ∧
        Nonempty (πf.Equiv (JacquetLanglands.splitTensor (splitJ) πv πaway))) →
    (∀ z : (FiniteCompletion ℚ v.1)ˣ, πf ((splitJ).symm (1, ((1, z), 1))) = 1) →
    ∀ ξ₀ : HeckeCharacter L,
    (∀ (x : FiniteIdeles L) (g : D.rationalInvolution.FiniteAdelicPoints),
      ((D.rationalInvolution.baseChange (FiniteAdeles ℚ)).underlyingUnit g :
          FiniteAdeles ℚ ⊗[ℚ] A) =
        Algebra.TensorProduct.map (AlgHom.id ℚ (FiniteAdeles ℚ))
          ((algebraMap F A).toRatAlgHom.comp (algebraMap L F).toRatAlgHom)
          ((finiteAdeleTensorEquiv ℚ L).symm (x : FiniteAdeles L)) →
      ρ' g = ((ξ₀ (ideleClassMap L (finiteIdelesInclusion L x)) : ℂˣ) : ℂ) • LinearMap.id) →
    ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances ℓ]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ)
      (M : Type) [Field M] [Algebra (FiniteCompletion K lam.1) M] [TopologicalSpace M]
      [IsTopologicalRing M] (hKM : Continuous (algebraMap (FiniteCompletion K lam.1) M))
      (j : M ≃+* ℂ)
      {V'' : Type} [AddCommGroup V''] [Module M V'']
      (τ : Representation M D.rationalInvolution.FiniteAdelicPoints V'') (eτ : V' ≃+ V''),
      (∀ (z : ℂ) (x : V'), eτ (z • x) = j.symm z • eτ x) →
      (∀ g (x : V'), eτ (ρ' g x) = τ g (eτ x)) →
    ∀ (hfix : CMHarrisLambdaTowerFixedVectorComparison D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
        hRigid lam (n - 1))
      (hfin : CMHarrisLambdaCohomologyFiniteDimensional D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence
        geometry (hRigid U) lam (n - 1))
      (hcont : CMHarrisLambdaCohomologyContinuous D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence
        geometry (hRigid U) lam (n - 1)),
    let Hπ : Objects F M := cmHarrisLambdaIsotypicFixedVectorsObjects D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry hRigid
      lam (n - 1) M hKM hfix U hfin hcont τ
    Nontrivial Hπ.val →
    ∀ (Lν : Type) [Field Lν] [NumberField Lν] (ιν : Lν →+* ℂ) (lamν : FinitePlacesAbove Lν ℓ)
      (ψ : LambdaAdicCharacter F Lν lamν.1) (κ : FiniteCompletion Lν lamν.1 →+* M),
      Continuous κ →
      (∀ c : Lν, j (κ (NumberField.FinitePlace.embedding lamν.1 c)) = ιν c) →
      GaloisRepresentation.Harris.IsNuBarRealization ιν lamν.1 n ξ₀ ψ →
      ∃ (a : ℕ) (ρπ : Objects.{0, 0, 0} F M), ρπ.val.rank = n ∧
        (∀ g : Field.absoluteGaloisGroup F,
          ((κ ((ψ g⁻¹ : (FiniteCompletion Lν lamν.1)ˣ) : FiniteCompletion Lν lamν.1)) •
              Hπ.val.representation g⁻¹).charpoly =
            (ρπ.val.representation g).charpoly ^ a) ∧
        ∃ T : Finset ℕ, ∀ (p₀ : ℕ) [Fact p₀.Prime], p₀ ∉ T →
          ∀ (c : UnramifiedChart D.toSecondKindInvolution (rationalPrimePlace p₀) n)
            (πp : SmoothRep.{0, 0, 0} ℂ
              (LocalPoints D.toSecondKindInvolution (rationalPrimePlace p₀))),
            (∃ πaway : Rep.{0} ℂ (D.rationalInvolution.PrimeToPoints p₀),
              Nonempty (ρ'.Equiv (Representation.tprod
                (πp.representation.comp
                  (D.rationalInvolution.finiteLocalMap (rationalPrimePlace p₀)).toMonoidHom)
                (πaway.ρ.comp ((MonoidHom.snd _ _).comp
                  (D.rationalInvolution.finiteAdelicPointsSplit p₀
                    (Fact.out : p₀.Prime).ne_zero).toMulEquiv.toMonoidHom))))) →
            ∀ ξ : c.torus →* ℂˣ, c.HasPrincipalSeriesParameter πp ξ →
            ∀ w : FinitePlacesAbove F (rationalPrimePlace p₀),
              ∃ Q : Polynomial M, HasEulerPolynomialAt ρπ w.1 Q ∧
                unitaryEulerPolynomial (Q.map (j : M →+* ℂ)) =
                  Langlands.Unramified.Eigenvalues.eulerPolynomial (c.baseChangeEigenvalues ξ w)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
