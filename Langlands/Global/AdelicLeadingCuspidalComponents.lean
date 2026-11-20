import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.Global.PositiveRealTorusIntrinsic
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicModularCharacterAdjointDeterminantProof
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.Automorphic.GroupSchemeActualDifferential

/-! # Cuspidal exponents and leading cuspidal components

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §6.1 (the maps
`H_P`), §6.2 (cuspidal exponents, constant terms, cuspidal projection and components) and §6.3
(leading cuspidal components), for a supplied compatible family of standard parabolics of a
connected reductive group over a number field. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Polynomial

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- Complex-valued polynomial functions of degree at most `n` on a real vector space `V`: the
complex span of the products `v ↦ ℓ₁(v) ⋯ ℓₖ(v)` of `k ≤ n` real-linear forms. -/
def polynomialFunctions (n : ℕ) : Submodule ℂ (V → ℂ) :=
  Submodule.span ℂ {f | ∃ (k : ℕ) (_ : k ≤ n) (ℓ : Fin k → V →ₗ[ℝ] ℝ),
    f = fun v => ∏ j, ((ℓ j v : ℝ) : ℂ)}

end Polynomial

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The standard parabolics for a maximal split torus `i` and a generic cocharacter `ν`, indexed
by the sets `J` of simple relative roots of their Levi factors. -/
abbrev StandardIndex [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :=
  {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν}

/-- A compatible family of standard parabolics `P_J = M_J U_J` of a connected reductive group `G`,
with split components `A_J → M_J`, for one maximal split torus `T`, one generic cocharacter `ν`
and one choice of integral coroots. -/
structure StandardParabolicFamily [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] where
  connectedReductive : IsConnectedReductive G
  T : CommGroupScheme (Spec (CommRingCat.of F))
  i : T.toGrp ⟶ G
  ν : cocharacterLattice T
  maximalSplit : IsMaximalSplitTorus i
  generic : IsGenericCocharacter i ν
  coroots : letI := maximalSplit.isSplitSubtorus.mono; RelativeRootReflectionData i
  P : StandardIndex F G i ν → GroupScheme (Spec (CommRingCat.of F))
  M : StandardIndex F G i ν → GroupScheme (Spec (CommRingCat.of F))
  U : StandardIndex F G i ν → GroupScheme (Spec (CommRingCat.of F))
  A : StandardIndex F G i ν → CommGroupScheme (Spec (CommRingCat.of F))
  p : ∀ J, P J ⟶ G
  iU : ∀ J, U J ⟶ P J
  l : ∀ J, M J ⟶ P J
  a : ∀ J, (A J).toGrp ⟶ M J
  f : ∀ J, A J ⟶ T
  torus : ∀ J, T.toGrp ⟶ M J
  isCompatible : ∀ J,
    ParabolicRootPresentationData.IsCompatible ⟨T, i, ν, J.1, f J⟩ (p J) (l J) (a J)
  isUnipotentRadical : ∀ J, LeviSubgroup.IsGeometricUnipotentRadical (iU J)
  torus_comp : ∀ J, torus J ≫ l J ≫ p J = i
  leviDim : StandardIndex F G i ν → ℕ
  leviSmooth : ∀ J, SmoothOfRelativeDimension (leviDim J) (M J).X.hom
  affineP : ∀ J, IsAffine (P J).X.left
  finiteTypeP : ∀ J, LocallyOfFiniteType (P J).X.hom
  affineM : ∀ J, IsAffine (M J).X.left
  finiteTypeM : ∀ J, LocallyOfFiniteType (M J).X.hom
  affineU : ∀ J, IsAffine (U J).X.left
  closedU : ∀ J, IsClosedImmersion (iU J ≫ p J).hom.hom.left

namespace StandardParabolicFamily

attribute [instance] affineP finiteTypeP affineM finiteTypeM affineU closedU

variable {F G} [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

instance mono_i : Mono 𝓕.i.hom.hom.left := 𝓕.maximalSplit.isSplitSubtorus.mono

/-- The index `J = Δ₀` of all simple roots, the standard parabolic `G` itself. -/
def top : StandardIndex F G 𝓕.i 𝓕.ν := ⟨simpleRelativeRoots 𝓕.i 𝓕.ν, subset_rfl⟩

omit [NumberField F] in
theorem le_top (Q : StandardIndex F G 𝓕.i 𝓕.ν) : Q ≤ 𝓕.top := Q.2

omit [NumberField F] in
/-- The index order is the containment of the actual parabolics (`standardParabolicOrder`). -/
theorem le_iff_range_le (Q P : StandardIndex F G 𝓕.i 𝓕.ν) :
    Q ≤ P ↔ SubgroupFunctor.range (𝓕.p Q) ≤ SubgroupFunctor.range (𝓕.p P) := by
  rw [(𝓕.isCompatible Q).parabolic_eq, (𝓕.isCompatible P).parabolic_eq]
  exact ((standardParabolicOrder F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit 𝓕.ν
    𝓕.generic).1 Q.1 P.1 Q.2 P.2).1

/-! ### The split component and its actions -/

/-- `𝔄_P`: the positive real points of the split component `A_P`, the image in `P(𝔸)` of the
intrinsic positive scalar subgroup of `A_P(𝔸)`. -/
def positiveSplitComponent (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    Subgroup (AdelicGroupPoints F (𝓕.P J)) :=
  PositiveRealTorus.imageSubgroup F (𝓕.A J) (𝓕.P J) (𝓕.a J ≫ 𝓕.l J)

/-- The unnormalized left action `φ ↦ φ(a ·)` of `a ∈ P(𝔸)` on functions on `G(𝔸)`. -/
def unnormalizedAction (J : StandardIndex F G 𝓕.i 𝓕.ν) (x : AdelicGroupPoints F (𝓕.P J))
    (φ : AdelicGroupPoints F G → ℂ) : AdelicGroupPoints F G → ℂ :=
  fun g => φ (map F (𝓕.P J) G (𝓕.p J) x * g)

/-- `δ_P(x)^{1/2} = x^{ρ_P}`, with `2ρ_P = det(Ad | Lie P)`. -/
def halfModulus (J : StandardIndex F G 𝓕.i 𝓕.ν) (x : AdelicGroupPoints F (𝓕.P J)) : ℂ :=
  parameterPower F (𝓕.P J) (halfModulusParameter F (𝓕.P J)) x

/-- The normalized action `(a · φ)(g) = δ_P(a)^{-1/2} φ(a g)` (Bernstein–Lapid (6.2)). -/
def normalizedAction (J : StandardIndex F G 𝓕.i 𝓕.ν) (x : AdelicGroupPoints F (𝓕.P J))
    (φ : AdelicGroupPoints F G → ℂ) : AdelicGroupPoints F G → ℂ :=
  fun g => parameterPower F (𝓕.P J) (-halfModulusParameter F (𝓕.P J)) x *
    φ (map F (𝓕.P J) G (𝓕.p J) x * g)

theorem unnormalizedAction_mul (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (x y : AdelicGroupPoints F (𝓕.P J)) (φ : AdelicGroupPoints F G → ℂ) :
    𝓕.unnormalizedAction J (x * y) φ = 𝓕.unnormalizedAction J y (𝓕.unnormalizedAction J x φ) := by
  funext g
  simp only [unnormalizedAction, map_mul, mul_assoc]

/-- `𝔄_P` is commutative: it is the image of points of the commutative group scheme `A_P`. -/
theorem positiveSplitComponent_mul_comm (J : StandardIndex F G 𝓕.i 𝓕.ν)
    {x y : AdelicGroupPoints F (𝓕.P J)} (hx : x ∈ 𝓕.positiveSplitComponent J)
    (hy : y ∈ 𝓕.positiveSplitComponent J) : x * y = y * x := by
  obtain ⟨x', -, rfl⟩ := hx
  obtain ⟨y', -, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm x' y']

/-- The unnormalized left action of `𝔄_P` on functions on `G(𝔸)`, `(a φ)(g) = φ(a g)`. -/
def splitComponentRepresentation (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    Representation ℂ (𝓕.positiveSplitComponent J) (AdelicGroupPoints F G → ℂ) where
  toFun x :=
    { toFun := 𝓕.unnormalizedAction J x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro φ
    funext g
    simp [unnormalizedAction]
  map_mul' x y := by
    apply LinearMap.ext
    intro φ
    change 𝓕.unnormalizedAction J ((x : AdelicGroupPoints F (𝓕.P J)) * y) φ =
      𝓕.unnormalizedAction J x (𝓕.unnormalizedAction J y φ)
    rw [𝓕.positiveSplitComponent_mul_comm J x.2 y.2, unnormalizedAction_mul]

theorem parameterPower_mul (H : GroupScheme (Spec (CommRingCat.of F)))
    (lam : ComplexCharacterParameter F H) (x y : AdelicGroupPoints F H) :
    parameterPower F H lam (x * y) = parameterPower F H lam x * parameterPower F H lam y := by
  rw [← parameterCharacter_apply, ← parameterCharacter_apply, ← parameterCharacter_apply, map_mul,
    Units.val_mul]

/-- The normalized action `(a · φ)(g) = δ_P(a)^{-1/2} φ(a g)` of `𝔄_P` (Bernstein–Lapid (6.2)). -/
def normalizedSplitComponentRepresentation (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    Representation ℂ (𝓕.positiveSplitComponent J) (AdelicGroupPoints F G → ℂ) where
  toFun x :=
    { toFun := 𝓕.normalizedAction J x
      map_add' := fun φ ψ => by
        funext g
        simp only [normalizedAction, Pi.add_apply, mul_add]
      map_smul' := fun c φ => by
        funext g
        simp only [normalizedAction, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    apply LinearMap.ext
    intro φ
    funext g
    simp [normalizedAction, parameterPower, characterLog_one]
  map_mul' x y := by
    apply LinearMap.ext
    intro φ
    funext g
    change 𝓕.normalizedAction J ((x : AdelicGroupPoints F (𝓕.P J)) * y) φ g =
      𝓕.normalizedAction J x (𝓕.normalizedAction J y φ) g
    rw [𝓕.positiveSplitComponent_mul_comm J x.2 y.2]
    simp only [normalizedAction, parameterPower_mul, map_mul, mul_assoc]
    ring

theorem parameterPower_add (H : GroupScheme (Spec (CommRingCat.of F)))
    (lam mu : ComplexCharacterParameter F H) (x : AdelicGroupPoints F H) :
    parameterPower F H (lam + mu) x = parameterPower F H lam x * parameterPower F H mu x := by
  simp only [parameterPower, map_add, LinearMap.add_apply, Complex.exp_add]

/-- `x^{ρ_P}` is the square root of the normalized idele norm of `det(Ad(x) | Lie P)`. -/
theorem halfModulus_eq_sqrt (J : StandardIndex F G 𝓕.i 𝓕.ν) (x : AdelicGroupPoints F (𝓕.P J)) :
    𝓕.halfModulus J x = ((Real.sqrt ((characterNorm F (𝓕.P J)
      (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul x : ℝ≥0) : ℝ) : ℝ) : ℂ) := by
  set n : ℝ := ((characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul x :
    ℝ≥0) : ℝ) with hn
  have hpos : 0 < n := by
    rw [hn]
    exact_mod_cast pos_iff_ne_zero.mpr
      (characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul x).ne_zero
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Complex.ofReal_exp]
  change Complex.exp ((1 / 2 : ℂ) * ((Real.log n : ℝ) : ℂ)) = _
  congr 1
  push_cast
  ring

/-- For smooth connected `P`, `x^{ρ_P}` is the square root of the modular character of
`P(𝔸)` (by the published `adelicModularCharacterAdjointDeterminant`). -/
theorem halfModulus_eq_sqrt_modularCharacter (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (hconn : ConnectedSpace (𝓕.P J).X.left) (x : AdelicGroupPoints F (𝓕.P J)) :
    𝓕.halfModulus J x = ((Real.sqrt (Measure.modularCharacter x : ℝ) : ℝ) : ℂ) := by
  rw [𝓕.halfModulus_eq_sqrt J x, adelicModularCharacterAdjointDeterminant F (𝓕.P J)
    (𝓕.isCompatible J).parabolic.smooth hconn x]

/-! ### Generalized exponents -/

/-- The polynomial description of `𝒜^{un}_{P,λ}` (6.10) for the unnormalized action: for some `n`
and every `g`, `a ↦ φ(a g) a^{-λ}` on `𝔄_P` is a polynomial of degree at most `n` in `H_P(a)`.
For smooth orbit maps this is the generalized-eigenspace condition. -/
def HasUnnormalizedExponent (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (lam : ComplexCharacterParameter F (𝓕.P J)) (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ n : ℕ, ∀ g : AdelicGroupPoints F G,
    ∃ Q ∈ polynomialFunctions (RealCharacterDual F (𝓕.P J)) n,
      ∀ x ∈ 𝓕.positiveSplitComponent J,
        𝓕.unnormalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x =
          Q (characterLog F (𝓕.P J) x)

/-- The polynomial description of `𝒜_{P,λ}` for the normalized action (Bernstein–Lapid (6.3)). -/
def HasExponent (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (lam : ComplexCharacterParameter F (𝓕.P J)) (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ n : ℕ, ∀ g : AdelicGroupPoints F G,
    ∃ Q ∈ polynomialFunctions (RealCharacterDual F (𝓕.P J)) n,
      ∀ x ∈ 𝓕.positiveSplitComponent J,
        𝓕.normalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x =
          Q (characterLog F (𝓕.P J) x)

/-- The normalized exponent `λ` is the unnormalized exponent `λ + ρ_P`. -/
theorem hasExponent_iff (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (lam : ComplexCharacterParameter F (𝓕.P J)) (φ : AdelicGroupPoints F G → ℂ) :
    𝓕.HasExponent J lam φ ↔
      𝓕.HasUnnormalizedExponent J (lam + halfModulusParameter F (𝓕.P J)) φ := by
  have key : ∀ (x : AdelicGroupPoints F (𝓕.P J)) (g : AdelicGroupPoints F G),
      𝓕.normalizedAction J x φ g * parameterPower F (𝓕.P J) (-lam) x =
        𝓕.unnormalizedAction J x φ g *
          parameterPower F (𝓕.P J) (-(lam + halfModulusParameter F (𝓕.P J))) x := by
    intro x g
    simp only [normalizedAction, unnormalizedAction, neg_add_rev, parameterPower_add]
    ring
  simp only [HasExponent, HasUnnormalizedExponent, key]

/-! ### Leading exponents -/

/-- The embedding `𝔞_P^* → 𝔞_0^*` by restriction of characters to the maximal split torus. -/
def chamberEmbedding (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    RealCharacterParameter F (𝓕.P J) →ₗ[ℝ] RealTorusSpace.Vstar 𝓕.T :=
  realParameterRestriction (𝓕.torus J ≫ 𝓕.l J)

/-- The closed positive chamber `𝔞_{0,+}^*`: `⟨y, α^∨⟩ ≥ 0` for every simple root `α`. -/
def closedPositiveChamber : Set (RealTorusSpace.Vstar 𝓕.T) :=
  {y | ∀ α : relativeRoots 𝓕.i, α.1 ∈ simpleRelativeRoots 𝓕.i 𝓕.ν →
    0 ≤ RealTorusSpace.pair 𝓕.T y ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot α)}

/-- An (unnormalized) exponent `λ` is leading when `Re λ ∈ 𝔞_{0,+}^*`. -/
def IsLeadingExponent (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (lam : ComplexCharacterParameter F (𝓕.P J)) : Prop :=
  𝓕.chamberEmbedding J (parameterRealPart F (𝓕.P J) lam) ∈ 𝓕.closedPositiveChamber

/-! ### Constant terms and cuspidality -/

/-- The constant term `∫_{U_Q(F) \ U_Q(𝔸)} φ(u g) du` along the standard parabolic `Q`. -/
def constantTerm (Q : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  subgroupConstantTerm F (𝓕.iU Q ≫ 𝓕.p Q) φ

/-- `C_{P,Q} φ`, set to `0` unless `Q ⊆ P`. -/
def parabolicConstantTerm (P Q : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  open Classical in if Q ≤ P then 𝓕.constantTerm Q φ else 0

/-- Cuspidality on `U(𝔸) M(F) \ G(𝔸)`: the constant terms along all `Q ⊊ P` vanish. -/
def IsCuspidalAlong (P : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, Q < P → 𝓕.constantTerm Q φ = 0

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

/-- Automorphic functions on `U(𝔸) M(F) \ G(𝔸)` for the norm of `rho` and the subgroup `Kinf`
(Bernstein–Lapid's `𝒜_P` for a faithful closed embedding `rho` and `Kinf = K_∞`). -/
def IsAutomorphicOn (P : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
    (parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P)) Kinf rho φ

/-! ### Cusp forms on the Levi and the cuspidal projection -/

/-- `K_∞ ∩ M(F_∞)`. -/
def leviInfiniteCompact (J : StandardIndex F G 𝓕.i 𝓕.ν) :
    Subgroup (InfiniteAdelicGroupPoints F (𝓕.M J)) :=
  Kinf.comap ((𝓕.M J).affinePointsTarget (𝓕.l J ≫ 𝓕.p J)
    (CommAlgCat.of F (NumberField.InfiniteAdeleRing F)))

/-- Cuspidality on `M(F) \ M(𝔸)`: vanishing constant terms along every proper parabolic. -/
def IsLeviCuspidal (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    Prop :=
  ∀ (P' U' : GroupScheme (Spec (CommRingCat.of F))) (p' : P' ⟶ 𝓕.M J) (r : U' ⟶ P')
    [IsAffine U'.X.left] [IsClosedImmersion (r ≫ p').hom.hom.left],
    IsParabolicSubgroup p' → LeviSubgroup.IsGeometricUnipotentRadical r →
      SubgroupFunctor.range p' ≠ ⊤ → subgroupConstantTerm F (r ≫ p') ψ = 0

/-- Cusp forms on `M(F) \ M(𝔸)`. -/
def IsLeviCuspForm (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    Prop :=
  IsAutomorphicFunctionOn F (𝓕.M J) (𝓕.leviSmooth J)
      (adelicDifferentialCommutator_of_smooth F (𝓕.M J) (𝓕.leviSmooth J))
      (rationalSubgroup F (𝓕.M J)) (𝓕.leviInfiniteCompact Kinf J)
      (𝓕.l J ≫ 𝓕.p J ≫ rho) ψ ∧
    𝓕.IsLeviCuspidal J ψ

/-- The integrand `m ↦ φ(m g) conj ψ(m)` on `M(F) \ M(𝔸)^1`, at the chosen representative. -/
def leviPairingIntegrand (J : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    NormOneRationalQuotient F (𝓕.M J) → ℂ :=
  fun x => φ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
      ((Quotient.out x : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) * g) *
    starRingEnd ℂ (ψ ((Quotient.out x : normOneSubgroup F (𝓕.M J)) :
      AdelicGroupPoints F (𝓕.M J)))

/-- The pairing `(φ(· g), ψ)_{X_M^1}`. -/
def leviPairing (J : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ) : ℂ :=
  ∫ x, 𝓕.leviPairingIntegrand J φ g ψ x ∂normOneRationalQuotientHaarMeasure F (𝓕.M J)

/-- `φc` is the cuspidal projection `φ^{cusp}` of `φ` along `P` (Bernstein–Lapid (6.8)): `φc` is a
cuspidal automorphic function on `U(𝔸) M(F) \ G(𝔸)` and, for every cusp form `ψ` on `M(F) \ M(𝔸)`
and every `g`, both pairings over `M(F) \ M(𝔸)^1` converge absolutely and agree. -/
def IsCuspidalProjection (P : StandardIndex F G 𝓕.i 𝓕.ν) (φ φc : AdelicGroupPoints F G → ℂ) :
    Prop :=
  𝓕.IsAutomorphicOn hsmooth Kinf rho P φc ∧ 𝓕.IsCuspidalAlong P φc ∧
    ∀ ψ : AdelicGroupPoints F (𝓕.M P) → ℂ, 𝓕.IsLeviCuspForm Kinf rho P ψ →
      ∀ g : AdelicGroupPoints F G,
        Integrable (𝓕.leviPairingIntegrand P φ g ψ) (normOneRationalQuotientHaarMeasure F (𝓕.M P)) ∧
        Integrable (𝓕.leviPairingIntegrand P φc g ψ)
          (normOneRationalQuotientHaarMeasure F (𝓕.M P)) ∧
        𝓕.leviPairing P φ g ψ = 𝓕.leviPairing P φc g ψ

/-! ### Cuspidal components, exponent decompositions and leading parts -/

/-- `ψ` is the cuspidal component `C^{cusp}_{P,Q} φ = (C_{P,Q} φ)^{cusp}` of `φ` along `Q`;
it is `0` unless `Q ⊆ P`. -/
def IsCuspidalComponent (P Q : StandardIndex F G 𝓕.i 𝓕.ν) (φ ψ : AdelicGroupPoints F G → ℂ) :
    Prop :=
  (Q ≤ P → 𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) ψ) ∧
    (¬ Q ≤ P → ψ = 0)

/-- A supplied finite decomposition `ψ = ∑_{λ ∈ s} c λ` of a function on `U(𝔸) M(F) \ G(𝔸)` into
cuspidal automorphic components with generalized unnormalized exponents `λ`. -/
structure IsExponentDecomposition (P : StandardIndex F G 𝓕.i 𝓕.ν)
    (ψ : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (𝓕.P P)))
    (c : ComplexCharacterParameter F (𝓕.P P) → AdelicGroupPoints F G → ℂ) : Prop where
  sum_eq : ψ = ∑ lam ∈ s, c lam
  automorphic : ∀ lam ∈ s, 𝓕.IsAutomorphicOn hsmooth Kinf rho P (c lam)
  cuspidal : ∀ lam ∈ s, 𝓕.IsCuspidalAlong P (c lam)
  exponent : ∀ lam ∈ s, 𝓕.HasUnnormalizedExponent P lam (c lam)

/-- The sum of the components of a decomposition whose exponents are leading. -/
def leadingSum (P : StandardIndex F G 𝓕.i 𝓕.ν) (s : Finset (ComplexCharacterParameter F (𝓕.P P)))
    (c : ComplexCharacterParameter F (𝓕.P P) → AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  open Classical in ∑ lam ∈ s.filter (𝓕.IsLeadingExponent P), c lam

/-- `ψdom = p^{dom}_P ψ`: the leading part of `ψ` computed from some exponent decomposition. -/
def IsLeadingPart (P : StandardIndex F G 𝓕.i 𝓕.ν) (ψ ψdom : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ (s : Finset (ComplexCharacterParameter F (𝓕.P P)))
    (c : ComplexCharacterParameter F (𝓕.P P) → AdelicGroupPoints F G → ℂ),
    𝓕.IsExponentDecomposition hsmooth Kinf rho P ψ s c ∧ ψdom = 𝓕.leadingSum P s c

/-- `λ` is an unnormalized cuspidal exponent of `φ` along `Q ⊆ P`: it carries a nonzero
component in an exponent decomposition of a cuspidal component of `φ` along `Q`. -/
def IsUnnormalizedCuspidalExponent (P Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F (𝓕.P Q)) : Prop :=
  Q ≤ P ∧ ∃ (φc : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ),
    𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) φc ∧
      𝓕.IsExponentDecomposition hsmooth Kinf rho Q φc s c ∧ lam ∈ s ∧ c lam ≠ 0

/-- `ψ` is the leading cuspidal component `p^{dom}_Q (C^{cusp}_{P,Q} φ)` of `φ` along `Q`, for
`φ` on `U_P(𝔸) M_P(F) \ G(𝔸)`; it is `0` unless `Q ⊆ P`. -/
def IsLeadingCuspidalComponent (P Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (φ ψ : AdelicGroupPoints F G → ℂ) : Prop :=
  (Q ≤ P → ∃ φc : AdelicGroupPoints F G → ℂ,
      𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) φc ∧
        𝓕.IsLeadingPart hsmooth Kinf rho Q φc ψ) ∧
    (¬ Q ≤ P → ψ = 0)

/-- `L = 𝓛_P φ` (Bernstein–Lapid (6.11b)): `L Q` is the leading cuspidal component of `φ` along
`Q` for every standard `Q`. -/
def IsLeadingCuspidalComponents (P : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ)
    (L : StandardIndex F G 𝓕.i 𝓕.ν → AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ Q, 𝓕.IsLeadingCuspidalComponent hsmooth Kinf rho P Q φ (L Q)

/-- `L = 𝓛 φ` for `φ` on `G(F) \ G(𝔸)` (Bernstein–Lapid (6.11a)): every standard `Q` lies in `G`. -/
def IsGlobalLeadingCuspidalComponents (φ : AdelicGroupPoints F G → ℂ)
    (L : StandardIndex F G 𝓕.i 𝓕.ν → AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ Q, ∃ φc : AdelicGroupPoints F G → ℂ,
    𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) φc ∧
      𝓕.IsLeadingPart hsmooth Kinf rho Q φc (L Q)

/-- The global version is the parabolic version for the top index `J = Δ₀`. -/
theorem isGlobalLeadingCuspidalComponents_iff (φ : AdelicGroupPoints F G → ℂ)
    (L : StandardIndex F G 𝓕.i 𝓕.ν → AdelicGroupPoints F G → ℂ) :
    𝓕.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho φ L ↔
      𝓕.IsLeadingCuspidalComponents hsmooth Kinf rho 𝓕.top φ L := by
  constructor
  · intro h Q
    exact ⟨fun _ => h Q, fun hQ => absurd (𝓕.le_top Q) hQ⟩
  · intro h Q
    exact (h Q).1 (𝓕.le_top Q)

end StandardParabolicFamily

end Langlands.Global
