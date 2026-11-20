import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.PositiveRealTorusIntrinsic
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet
import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Local finiteness of the system `Ξ_main` (Bernstein–Lapid, Theorem 7.2)

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §7.2, Theorem 7.2,
in the Fréchet form given by the proof in §7.6, number field case. Over an open set `W ⊆ ℂⁿ`
of parameters, consider the system of linear equations on functions `f` of uniform moderate
growth on `G(F) \ G(𝔸)`

* `∑_k b_{ik}(s) δ(h_{ik}) f = c_i(s) f` for `i ∈ Idx`, where `δ(h) f (x) = ∫ h(g) f(x g) dg`
  for smooth compactly supported test functions `h_{ik}` on `G(𝔸)`, the coefficients are
  holomorphic and for every `s` some `c_i(s)` is nonzero;
* `D_α(s)(a_α) (C_{U_α} f) = 0` for every simple relative root `α`, where `C_{U_α}` is the
  constant term along the unipotent radical `U_α` of the maximal standard parabolic `P_α`,
  `a_α ∈ A_{P_α}^G` satisfies `|α(a_α)| > 1`, the polynomial `D_α(s)` is monic of fixed degree
  with holomorphic coefficients and acts through left translation by `a_α`;
* `D̃_j(s)(z_j) f = 0` for `j < r`, where `z_j ∈ A_G` give a basis `H_G(z_j)` of `𝔞_G` and
  `D̃_j(s)` is monic of fixed degree with holomorphic coefficients and nowhere vanishing
  constant coefficient.

Then near every parameter the solutions in `𝔉^R_L` (`L` compact open) form a family of finite
type, for every sufficiently large `R`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left]

/-- A smooth compactly supported test function on `G(𝔸)` (Bernstein–Lapid, Example 3.1;
`C_c^∞(G(𝔸))`): it is smooth in the sense of `IsAdelicSmoothFunction` (continuous,
plot-smooth infinite slices, right invariant under an open subgroup of `G(𝔸_f)`), compactly
supported, and left invariant under an open subgroup of `G(𝔸_f)`. -/
def IsAdelicTestFunction (h : AdelicGroupPoints F G → ℂ) : Prop :=
  IsAdelicSmoothFunction F G h ∧ HasCompactSupport h ∧
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∀ l ∈ L, ∀ g : AdelicGroupPoints F G, h (ofFinite F G l * g) = h g

variable [LocallyOfFiniteType G.X.hom]

/-- The right convolution action `δ(h) f (x) = ∫_{G(𝔸)} h(g) f(x g) dg` of a function `h` on
`G(𝔸)`, for the Haar measure `Measure.haar` of `G(𝔸)` (Bernstein–Lapid §7.1). It is `0` where
the integrand is not integrable. -/
def rightConvolution (h f : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) : ℂ :=
  ∫ g, h g * f (x * g) ∂(Measure.haar : Measure (AdelicGroupPoints F G))

variable {F G}

/-- The function `φ` satisfies the difference equation `D(a) φ = 0` for left translation by
`a`: `∑_k D_k φ(a^k g) = 0` for every `g`, where `D = ∑_k D_k X^k`. -/
def IsTranslationPolynomialSolution (a : AdelicGroupPoints F G) (D : Polynomial ℂ)
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ g : AdelicGroupPoints F G,
    ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ (a ^ k * g) = 0

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Data

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  (Δ : Type u) (r n : ℕ) (W : TopologicalSpace.Opens (Fin n → ℂ))

/-- The analytic data of the system `Ξ_main` of Bernstein–Lapid §7.2 over a parameter set
`W ⊆ ℂⁿ`: for `i ∈ Idx`, finitely many test functions `h i k` with coefficients `b i k` and a
scalar `c i` (the equations `∑_k b i k s • δ(h i k) f = c i s • f`); for every simple root
`α ∈ Δ`, a polynomial `D α s` of degree `degree α` (the constant-term equations); for
`j < r`, a polynomial `centralD j s` of degree `centralDegree j` (the central equations). -/
structure LocalFinitenessData where
  /-- The index type of the Harish-Chandra equations. -/
  Idx : Type u
  /-- The number of test functions in the `i`-th equation. -/
  m : Idx → ℕ
  /-- The test functions of the `i`-th equation. -/
  h : ∀ i, Fin (m i) → AdelicGroupPoints F G → ℂ
  /-- Their coefficients. -/
  b : ∀ i, Fin (m i) → W → ℂ
  /-- The eigenvalue of the `i`-th equation. -/
  c : Idx → W → ℂ
  /-- The degree of the constant-term polynomial of `α`. -/
  degree : Δ → ℕ
  /-- The constant-term polynomial of `α`. -/
  D : Δ → W → Polynomial ℂ
  /-- The degree of the `j`-th central polynomial. -/
  centralDegree : Fin r → ℕ
  /-- The `j`-th central polynomial. -/
  centralD : Fin r → W → Polynomial ℂ

variable {F G Δ r n W} [IsAffine G.X.left]

/-- Bernstein–Lapid's hypotheses on the data of `Ξ_main` (§7.2): the `h i k` are smooth
compactly supported test functions; `b i k`, `c i` and all polynomial coefficients are
holomorphic on `W`; at every `s` some `c i s` is nonzero; every `D α s` is monic of degree
`degree α`; every `centralD j s` is monic of degree `centralDegree j` with nonzero constant
coefficient. -/
def LocalFinitenessData.IsAdmissible (X : LocalFinitenessData F G Δ r n W) : Prop :=
  (∀ i k, IsAdelicTestFunction F G (X.h i k)) ∧
    (∀ i k, IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (X.b i k) Set.univ) ∧
    (∀ i, IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (X.c i) Set.univ) ∧
    (∀ s, ∃ i, X.c i s ≠ 0) ∧
    (∀ α s, (X.D α s).Monic ∧ (X.D α s).natDegree = X.degree α) ∧
    (∀ α k, IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => (X.D α s).coeff k) Set.univ) ∧
    (∀ j s, (X.centralD j s).Monic ∧ (X.centralD j s).natDegree = X.centralDegree j ∧
      (X.centralD j s).coeff 0 ≠ 0) ∧
    ∀ j k, IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => (X.centralD j s).coeff k) Set.univ

variable [LocallyOfFiniteType G.X.hom]

/-- The solutions at `s ∈ W` of the system `Ξ_main(s)` in `𝔉^R_L`: the functions `f` of
`v ∈ 𝔉^R_L` with `∑_k b i k s • δ(h i k) f = c i s • f` for every `i`,
`D α s (a α) (C_{U_α} f) = 0` for every `α`, where `C_{U_α}` is the constant term along
`u α : U_α → G` and the polynomial acts by left translation by `a α`, and
`centralD j s (z j) f = 0` for every `j`. -/
def LocalFinitenessData.solutions (X : LocalFinitenessData F G Δ r n W)
    {Ua : Δ → GroupScheme (Spec (CommRingCat.of F))} [∀ α, IsAffine (Ua α).X.left]
    (u : ∀ α, Ua α ⟶ G) [∀ α, IsClosedImmersion (u α).hom.hom.left]
    (a : Δ → AdelicGroupPoints F G) (z : Fin r → AdelicGroupPoints F G) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (R : ℝ)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (s : W) :
    Set (UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) :=
  {v | (∀ i, ∀ x : AdelicGroupPoints F G,
      ∑ k, X.b i k s * rightConvolution F G (X.h i k)
          (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v) x =
        X.c i s * UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v x) ∧
    (∀ α, IsTranslationPolynomialSolution (a α) (X.D α s)
      (subgroupConstantTerm F (u α)
        (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v))) ∧
    ∀ j, IsTranslationPolynomialSolution (z j) (X.centralD j s)
      (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v)}

end Data

section GroupData

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- The group-theoretic data of `Ξ_main` (Bernstein–Lapid §7.2) for the minimal parabolic fixed
by a maximal split torus `iT : T → G` and a generic cocharacter `ν`, with simple roots
`Δ₀ = simpleRelativeRoots iT ν`:

* for every `α ∈ Δ₀`, `u α : U_α → G` has as functor of points the unipotent radical
  `standardUnipotent iT ν (Δ₀ \ {α})` of the maximal standard parabolic `P_α`;
* `t α ∈ A_T` (positive real subgroup of `T(𝔸)`) with `β(t α) = 1` for `β ∈ Δ₀ \ {α}`,
  `α(t α)` the positive scalar idele of a real `x > 1`, and `H_G(iT(t α)) = 0`, so that
  `a_α = iT(t α) ∈ A_{P_α}^G` and `⟨α, H_0(a_α)⟩ > 0`;
* `z j ∈ A_T` (`j < r`) with every simple root trivial on `z j`, so that `iT(z j) ∈ A_G`,
  and the logarithms `H_G(iT(z j))` form a basis of `𝔞_G`. -/
def IsLocalFinitenessGroupData (iT : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F))}
    (u : ∀ α, Ua α ⟶ G) (t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp) {r : ℕ}
    (z : Fin r → AdelicGroupPoints F T.toGrp) : Prop :=
  (∀ α, SubgroupFunctor.range (u α) =
      standardUnipotent iT ν (simpleRelativeRoots iT ν \ {α.1})) ∧
    (∀ α, t α ∈ PositiveRealTorus.intrinsicSubgroup F T) ∧
    (∀ α β : simpleRelativeRoots iT ν, β ≠ α → Lie.characterValue β.1 (t α) = 1) ∧
    (∀ α : simpleRelativeRoots iT ν, ∃ x : NNRealˣ, 1 < (x : NNReal) ∧
      PositiveRealIdeles.full F x = Lie.characterValue α.1 (t α)) ∧
    (∀ α, characterLog F G (map F T.toGrp G iT (t α)) = 0) ∧
    (∀ j, z j ∈ PositiveRealTorus.intrinsicSubgroup F T) ∧
    (∀ j (β : simpleRelativeRoots iT ν), Lie.characterValue β.1 (z j) = 1) ∧
    LinearIndependent ℝ (fun j => characterLog F G (map F T.toGrp G iT (z j))) ∧
    Submodule.span ℝ (Set.range fun j => characterLog F G (map F T.toGrp G iT (z j))) = ⊤

end GroupData

/-- Local finiteness of the system `Ξ_main` (Bernstein–Lapid, Theorem 7.2, number field case,
in the Fréchet form of its proof in §7.6). Let `G` be connected reductive over a number field
`F`, `iT : T → G` a maximal split torus and `ν` a generic cocharacter. Take group data
`u`, `t`, `z` of `Ξ_main` (`IsLocalFinitenessGroupData`) and admissible analytic data `X` over an
open set `W ⊆ ℂⁿ`. Then for every compact open subgroup `L ≤ G(𝔸_f)` and every `s₀ ∈ W` there
are an open neighbourhood `U` of `s₀` and `R₀` such that for every `R ≥ R₀` the solutions of
`Ξ_main(s)` in `𝔉^R_L` (`LocalFinitenessData.solutions`, with `a α = iT(t α)` and `iT(z j)`)
are of finite type on `U`. -/
def UniformGrowthLocalFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (iT : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus iT → IsGenericCocharacter iT ν →
    ∀ (Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F)))
      [∀ α, IsAffine (Ua α).X.left] (u : ∀ α, Ua α ⟶ G)
      [∀ α, IsClosedImmersion (u α).hom.hom.left]
      (t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp) (r : ℕ)
      (z : Fin r → AdelicGroupPoints F T.toGrp),
      IsLocalFinitenessGroupData iT ν u t z →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
      (hrho : IsClosedSubgroup rho) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth)
      (n : ℕ) (W : TopologicalSpace.Opens (Fin n → ℂ))
      (X : LocalFinitenessData F G (simpleRelativeRoots iT ν) r n W),
      X.IsAdmissible →
      ∀ L : Subgroup (FiniteAdelicGroupPoints F G),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
        IsCompact (L : Set (FiniteAdelicGroupPoints F G)) →
      ∀ s₀ : W, ∃ U : Set W, IsOpen U ∧ s₀ ∈ U ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        IsFiniteTypeOn 𝓘(ℂ, Fin n → ℂ)
          (X.solutions u (fun α => map F T.toGrp G iT (t α))
            (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc R L)
          U

end Langlands.Global
