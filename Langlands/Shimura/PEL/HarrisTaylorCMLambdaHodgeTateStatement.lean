import Langlands.Shimura.PEL.HarrisTaylorCMLambdaCohomologyObjects
import Langlands.Galois.TaylorMultiplicityRemovalStatement

/-! # The Hodge–Tate property of the `λ`-adic cohomology of the CM Shimura varieties

The statement that the `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` of a small CM level `U` with
Harris's coefficient system `W`, viewed as a representation of `Gal(F̄/F)` on a `ℚ_ℓ`-vector
space, has a Hodge–Tate decomposition at every finite place of `F` above the residue
characteristic `ℓ` of `λ`. This is the input that Harris (1999), proof of Theorem 5.7, printed
pp. 313–314, draws from the geometric origin of `W` for Taylor's argument; the underlying
theorem is Faltings (1988), Chapter III, Theorem 4.1, printed p. 298.

The decomposition is that of the underlying `ℚ_ℓ`-representation
(`HasUnderlyingHodgeTateDecomposition`): it is `C_w`-linear and Galois-equivariant but not
required to be `K_λ`-linear, so the Hodge–Tate weights may differ between the embeddings of
`K_λ`. See `HarrisTaylorCMLambdaHodgeTateStatement.md`.
-/

noncomputable section

universe u uK uL uV wS wR

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.GaloisRepresentation.HodgeTate

variable (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Algebra ℚ_[p] F]
  [FiniteDimensional ℚ_[p] F] (Λ : Type uL) [Field Λ] [TopologicalSpace Λ] [Algebra ℚ_[p] Λ]

/-- A Hodge–Tate decomposition of the underlying `ℚ_p`-representation of `A`: a
`C_F`-linear isomorphism `Φ : ⊕_{i < n} C_F(k i) ≅ C_F ⊗_{ℚ_p} V` that intertwines the
semilinear actions of `σ ∈ Gal(F̄/F)`, namely `x ↦ χ(σ)^{k i} σ(x)` on the summand of index
`i` and `σ ⊗ ρ(σ)` on `C_F ⊗_{ℚ_p} V`. The space `V` is a `ℚ_p`-vector space through
`ℚ_p → Λ`, so `n` is its dimension over `ℚ_p`. Unlike `HasHodgeTateDecomposition`, the
isomorphism need not commute with the action of `Λ`. -/
def HasUnderlyingHodgeTateDecomposition (A : Objects.{u, uL, uV} F Λ) (n : ℕ)
    (k : Fin n → ℤ) : Prop :=
  letI : Module ℚ_[p] A.val := Module.compHom A.val (algebraMap ℚ_[p] Λ)
  haveI : IsScalarTower ℚ_[p] Λ A.val := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ∃ Φ : (Fin n → Completed p F) ≃ₗ[Completed p F] (Completed p F ⊗[ℚ_[p]] A.val),
    ∀ (σ : Field.absoluteGaloisGroup F) (x : Fin n → Completed p F),
      Φ (fun i => cyclotomic p σ ^ k i * galoisRingHom p σ (x i)) =
        TensorProduct.map (galoisLinear p σ)
          ((A.val.representation σ).restrictScalars ℚ_[p]) (Φ x)

end Langlands.GaloisRepresentation.HodgeTate

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Global.CompletionPadic

variable {K : Type uK} [Field K] [NumberField K] {L : Type uL} [Field L] [NumberField L]

/-- The restriction of the `λ`-adic representation `A` to a decomposition group at a place
`v` of `K` above the residue characteristic `ℓ` of `λ` has a Hodge–Tate decomposition, as a
`ℚ_ℓ`-representation, with twists `k i`, `i < n`. Both completions are `ℚ_ℓ`-algebras through
their canonical `ℓ`-adic structures, as in `HasHodgeTateDecompositionAt`. -/
def HasUnderlyingHodgeTateDecompositionAt (lam : FinitePlace L)
    (A : LambdaAdic.{uK, uL, uV} K L lam) (v : FinitePlace K)
    (hv : residuePrime v = residuePrime lam) (n : ℕ) (k : Fin n → ℤ) : Prop :=
  letI : Algebra ℚ_[residuePrime lam] (FiniteCompletion K v) := padicAlgebraAt v hv
  letI : Algebra ℚ_[residuePrime lam] (FiniteCompletion L lam) := padicAlgebra lam
  haveI : FiniteDimensional ℚ_[residuePrime lam] (FiniteCompletion K v) :=
    (padicFieldAt v hv).finiteDimensional
  HodgeTate.HasUnderlyingHodgeTateDecomposition (residuePrime lam) (FiniteCompletion K v)
    (FiniteCompletion L lam) (atFinitePlace v A) n k

end Langlands.GaloisRepresentation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
open Langlands.Global AdelicFunctoriality
open Langlands.Global.CompletionPadic (residuePrime)
open Langlands.GaloisRepresentation (HasUnderlyingHodgeTateDecompositionAt)

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
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

variable (l : FinitePlacesAbove K p) (degree : ℕ)

/-- **The cohomology is Hodge–Tate above `ℓ`** (Faltings 1988, III, Theorem 4.1, p. 298, as
used by Harris 1999, proof of Theorem 5.7, pp. 313–314). Suppose that `A` is a division
algebra, as in Harris's setting, where the Shimura varieties are proper. Whenever
`H^d(S_U ×_F F̄, W)_λ` is finite-dimensional over `K_λ` with continuous Galois action, so
that it is the `λ`-adic representation `cmHarrisLambdaCohomologyObjects`, then at every
finite place `w` of `F` above the residue characteristic `ℓ` of `λ` its restriction to a
decomposition group at `w`, viewed as a representation on a `ℚ_ℓ`-vector space, has a
Hodge–Tate decomposition `C_w ⊗_{ℚ_ℓ} H^d(S_U ×_F F̄, W)_λ ≅ ⊕_{i < r} C_w(k i)` for some
integers `k 0, …, k (r - 1)` (repetitions allowed). The isomorphism is `C_w`-linear and
Galois-equivariant; it is not required to be `K_λ`-linear. -/
def CMHarrisLambdaCohomologyHodgeTateStatement : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    (hfin : CMHarrisLambdaCohomologyFiniteDimensional D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree)
    (hcont : CMHarrisLambdaCohomologyContinuous D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree)
    (w : Global.FinitePlace F) (hw : residuePrime w = residuePrime l.1),
    ∃ (r : ℕ) (k : Fin r → ℤ),
      HasUnderlyingHodgeTateDecompositionAt l.1
        (cmHarrisLambdaCohomologyObjects D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree
          hfin hcont)
        w hw r k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
