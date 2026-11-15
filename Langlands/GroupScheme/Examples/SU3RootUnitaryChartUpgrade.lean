import Langlands.GroupScheme.Rational.RootHeisenbergUnitaryChart
import Langlands.GroupScheme.Examples.SU3RootUnitaryWeilChart
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Upgrade of unitary charts

Proof of `UnitaryChartUpgradeStatement`. Expanding points of the Weil restriction
`W = R_{E/K} U_{L/E}` in a `K`-basis of `E`, a point of `W` over a test scheme with global
functions `R` has basis components `(α, z)`, and the chart form of `φ` is a polynomial map
`(α, z) ↦ (w, x) = (Bm z + Q(α), Am α)` with `K`-matrices `Am`, `Bm` and a quadratic map `Q`.
It defines a map `Ψ_T` from points of `W` to chart points of `U`, natural in the test scheme.
The defect of `Ψ` from being multiplicative is a family of polynomial identities in the
components, natural in `R`; it vanishes over `K` because `φ` is a homomorphism, hence
(`K` being infinite) over every `K`-algebra. Invertibility of `Am` and `Bm` makes every `Ψ_T`
bijective, so `Ψ` is an isomorphism of group schemes `W ≅ U`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace UnitaryChartUpgrade

/-! ### Polynomial identities -/

section Polynomial

variable {K : Type u} [Field K]

/-- **Polynomial identity principle.** Over an infinite field `K`, a family of maps
`(I → R) → (J → R)`, natural along `K`-algebra maps, that vanishes over `K` vanishes over every
`K`-algebra. -/
theorem eq_zero_of_natural [Infinite K] {I : Type u} {J : Type*}
    (F : ∀ (R : Type u) [CommRing R] [Algebra K R], (I → R) → J → R)
    (hF : ∀ (R R' : Type u) [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
      (f : R →ₐ[K] R') (x : I → R), F R' (fun i => f (x i)) = fun l => f (F R x l))
    (h0 : ∀ x : I → K, F K x = 0)
    (R : Type u) [CommRing R] [Algebra K R] (x : I → R) : F R x = 0 := by
  have hX : F (MvPolynomial I K) MvPolynomial.X = 0 := by
    funext l
    apply MvPolynomial.funext
    intro v
    have h := congrFun (hF (MvPolynomial I K) K (MvPolynomial.aeval v) MvPolynomial.X) l
    simp only [MvPolynomial.aeval_X] at h
    rw [h0 v] at h
    rw [Pi.zero_apply, map_zero]
    exact h.symm
  have h := hF (MvPolynomial I K) R (MvPolynomial.aeval x) MvPolynomial.X
  simp only [MvPolynomial.aeval_X] at h
  rw [show (fun i => x i) = x from rfl] at h
  rw [h, hX]
  funext l
  simp

/-- A matrix over `K` acting on vectors over a `K`-algebra. -/
def matVec {I J : Type*} [Fintype J] (R : Type u) [CommRing R] [Algebra K R]
    (M : Matrix I J K) (v : J → R) : I → R :=
  Matrix.mulVec (M.map (algebraMap K R)) v

/-- The quadratic map `α ↦ ∑ₛ ∑ₜ αₛ αₜ cₛₜ` with coefficients in `K`, over a `K`-algebra. -/
def quad {I J : Type*} [Fintype J] (R : Type u) [CommRing R] [Algebra K R]
    (c : J → J → I → K) (v : J → R) : I → R :=
  fun l => ∑ s, ∑ t, v s * v t * algebraMap K R (c s t l)

variable {I J : Type*} [Fintype J] {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R']
  [Algebra K R']

theorem matVec_apply (M : Matrix I J K) (v : J → R) (i : I) :
    matVec R M v i = ∑ j, algebraMap K R (M i j) * v j := by
  simp [matVec, Matrix.mulVec, dotProduct]

theorem matVec_map (f : R →ₐ[K] R') (M : Matrix I J K) (v : J → R) :
    matVec R' M (fun j => f (v j)) = fun i => f (matVec R M v i) := by
  funext i
  simp only [matVec_apply, map_sum, map_mul, AlgHom.commutes]

theorem quad_map (f : R →ₐ[K] R') (c : J → J → I → K) (v : J → R) :
    quad R' c (fun j => f (v j)) = fun l => f (quad R c v l) := by
  funext l
  simp only [quad, map_sum, map_mul, AlgHom.commutes]

theorem matVec_add (M : Matrix I J K) (v v' : J → R) :
    matVec R M (v + v') = matVec R M v + matVec R M v' :=
  Matrix.mulVec_add (M.map (algebraMap K R)) v v'

theorem matVec_sub (M : Matrix I J K) (v v' : J → R) :
    matVec R M (v - v') = matVec R M v - matVec R M v' :=
  Matrix.mulVec_sub (M.map (algebraMap K R)) v v'

theorem matVec_self (M : Matrix I J K) (v : J → K) : matVec K M v = Matrix.mulVec M v := by
  simp [matVec]

theorem matVec_matVec {Mu : Type*} [Fintype I] (M' : Matrix Mu I K) (M : Matrix I J K)
    (v : J → R) : matVec R M' (matVec R M v) = matVec R (M' * M) v := by
  rw [matVec, matVec, matVec, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem matVec_one [DecidableEq J] (v : J → R) : matVec R (1 : Matrix J J K) v = v := by
  rw [matVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem quad_self (c : J → J → I → K) (v : J → K) :
    quad K c v = fun l => ∑ s, ∑ t, v s * v t * c s t l := by
  rfl

theorem matVec_algebraMap (M : Matrix I J K) (v : J → K) :
    matVec R M (fun j => algebraMap K R (v j)) = fun i => algebraMap K R (matVec K M v i) :=
  matVec_map (Algebra.ofId K R) M v

theorem quad_algebraMap (c : J → J → I → K) (v : J → K) :
    quad R c (fun j => algebraMap K R (v j)) = fun l => algebraMap K R (quad K c v l) :=
  quad_map (Algebra.ofId K R) c v

theorem matVec_add_quad_map {Lb : Type*} [Fintype Lb] (f : R →ₐ[K] R') (M : Matrix I Lb K)
    (c : J → J → I → K) (z : Lb → R) (v : J → R) :
    matVec R' M (fun j => f (z j)) + quad R' c (fun j => f (v j)) =
      fun l => f ((matVec R M z + quad R c v) l) := by
  rw [matVec_map, quad_map]
  funext l
  simp only [Pi.add_apply, map_add]

theorem matVec_injective [Fintype I] [DecidableEq J] {M : Matrix I J K} {M' : Matrix J I K}
    (h : M' * M = 1) : Function.Injective (matVec R M) := fun v v' hv => by
  have h' := congrArg (matVec R M') hv
  rwa [matVec_matVec, matVec_matVec, h, matVec_one, matVec_one] at h'

theorem matVec_matVec_eq_self [Fintype I] [DecidableEq I] {M : Matrix I J K}
    {M' : Matrix J I K} (h : M * M' = 1) (v : I → R) : matVec R M (matVec R M' v) = v := by
  rw [matVec_matVec, h, matVec_one]

/-- Expansion of a bilinear map on linear combinations. -/
theorem bilin_sum_smul {M : Type*} [AddCommGroup M] [Module K M]
    (Φ : M →ₗ[K] M →ₗ[K] (I → K)) (w : J → M) (v : J → K) :
    Φ (∑ s, v s • w s) (∑ t, v t • w t) = quad K (fun s t => Φ (w s) (w t)) v := by
  funext l
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, quad_self, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

end Polynomial

/-! ### Linear algebra of the chart form -/

section Linear

open SU3Root WeilChart

variable {K : Type u} [Field K] (E L : Type u) [Field E] [Field L] [Algebra K E] [Algebra E L]
  [Algebra K L] [IsScalarTower K E L] [Algebra.IsQuadraticExtension E L] [Algebra.IsSeparable E L]
  {n : ℕ} (b : Module.Basis (Fin n) K E) {d m : ℕ}
  (A : L →ₗ[K] (Fin d → K)) (B : L →ₗ[K] (Fin m → K)) (H : L →ₗ[K] L →ₗ[K] (Fin m → K))

/-- The `K`-basis `(i, j) ↦ b_j • e_i` of `L`, for the basis `b` of `E` over `K` and the chart
basis `e` of `L` over `E`. -/
def towerBasis : Module.Basis (ULift.{u} (Fin 2) × Fin n) K L :=
  b.smulTower' (chartData E L).basis

theorem towerBasis_apply (q : ULift.{u} (Fin 2) × Fin n) :
    towerBasis E L b q = b q.2 • (chartData E L).basis q.1 :=
  b.smulTower'_apply _ _

/-- The `K`-linear map `ζ ↦ (∑ⱼ ζⱼ bⱼ) • f` onto the trace-zero line, for the chart center `f`. -/
def centerMap : (Fin n → K) →ₗ[K] L :=
  (LinearMap.toSpanSingleton E L (chartData E L).center).restrictScalars K ∘ₗ
    b.equivFun.symm.toLinearMap

theorem centerMap_apply (ζ : Fin n → K) :
    centerMap E L b ζ = b.equivFun.symm ζ • (chartData E L).center :=
  rfl

/-- The `K`-bilinear form `Φ(x, y) = B(λ (x σ(y))) + H(x, y)`, whose diagonal is the part of the
chart form quadratic in the first parameter. -/
def chartForm : L →ₗ[K] L →ₗ[K] (Fin m → K) :=
  ((LinearMap.mul K L).compl₂ ((conjugation E L).toAlgHom.restrictScalars K).toLinearMap).compr₂
    (B ∘ₗ LinearMap.mulLeft K (chartData E L).traceOne) + H

theorem chartForm_apply (x y : L) :
    chartForm E L B H x y =
      B ((chartData E L).traceOne * x * conjugation E L y) + H x y := by
  simp [chartForm, mul_assoc]

/-- The coefficients of the quadratic part of the chart form in the tower basis. -/
def chartCoeff (s t : ULift.{u} (Fin 2) × Fin n) : Fin m → K :=
  chartForm E L B H (towerBasis E L b s) (towerBasis E L b t)

/-- The matrix of the first chart coordinate in the tower basis. -/
def vecMatrix : Matrix (Fin d) (ULift.{u} (Fin 2) × Fin n) K :=
  LinearMap.toMatrix' (A ∘ₗ (towerBasis E L b).equivFun.symm.toLinearMap)

/-- The matrix of the second chart coordinate on the trace-zero line. -/
def scalarMatrix : Matrix (Fin m) (Fin n) K :=
  LinearMap.toMatrix' (B ∘ₗ centerMap E L b)

theorem vecMatrix_mulVec (α : ULift.{u} (Fin 2) × Fin n → K) :
    Matrix.mulVec (vecMatrix E L b A) α = A ((towerBasis E L b).equivFun.symm α) := by
  rw [vecMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem scalarMatrix_mulVec (ζ : Fin n → K) :
    Matrix.mulVec (scalarMatrix E L b B) ζ = B (centerMap E L b ζ) := by
  rw [scalarMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem quad_chartCoeff (α : ULift.{u} (Fin 2) × Fin n → K) :
    quad K (chartCoeff E L b B H) α =
      chartForm E L B H ((towerBasis E L b).equivFun.symm α)
        ((towerBasis E L b).equivFun.symm α) := by
  rw [Module.Basis.equivFun_symm_apply, bilin_sum_smul]
  rfl

/-- The first parameter of a field parameter in the tower basis. -/
theorem towerBasis_rationalComponents (p : rationalParameters E L) :
    (towerBasis E L b).equivFun.symm (rationalComponents L b p).1 = p.first := by
  rw [first_eq_rationalCoordinates, Module.Basis.equivFun_symm_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← b.sum_repr ((rationalCoordinates L p).vec i), Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [towerBasis_apply, smul_assoc]
  rfl

/-- The scalar of a field parameter on the trace-zero line. -/
theorem centerMap_rationalComponents (p : rationalParameters E L) :
    centerMap E L b (rationalComponents L b p).2 =
      (rationalCoordinates L p).scalar • (chartData E L).center := by
  rw [centerMap_apply]
  congr 1
  rw [Module.Basis.equivFun_symm_apply]
  exact b.sum_repr _

/-- **The chart form in components.** On the components of a field parameter `p`, the chart
coordinates of `φ(p)` are the matrix and quadratic expressions of the components. -/
theorem chartForm_rationalComponents (p : rationalParameters E L) :
    Matrix.mulVec (scalarMatrix E L b B) (rationalComponents L b p).2 +
        quad K (chartCoeff E L b B H) (rationalComponents L b p).1 =
      B p.second + H p.first p.first := by
  rw [scalarMatrix_mulVec, quad_chartCoeff, towerBasis_rationalComponents, chartForm_apply,
    centerMap_rationalComponents, second_eq_rationalCoordinates L p, map_add]
  abel

/-- A matrix of a bijective linear map has a two-sided inverse matrix. -/
theorem exists_toMatrix'_inverse {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (f : (I → K) →ₗ[K] (J → K)) (hf : Function.Bijective f) :
    ∃ M' : Matrix I J K, M' * LinearMap.toMatrix' f = 1 ∧ LinearMap.toMatrix' f * M' = 1 := by
  let g := LinearEquiv.ofBijective f hf
  refine ⟨LinearMap.toMatrix' g.symm.toLinearMap, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    exact g.symm_apply_apply x
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    exact g.apply_symm_apply x

theorem exists_vecMatrix_inverse (hA : Function.Bijective A) :
    ∃ M' : Matrix (ULift.{u} (Fin 2) × Fin n) (Fin d) K,
      M' * vecMatrix E L b A = 1 ∧ vecMatrix E L b A * M' = 1 :=
  exists_toMatrix'_inverse _ (hA.comp (towerBasis E L b).equivFun.symm.bijective)

/-- The values of `centerMap` have trace zero. -/
theorem centerMap_add_conjugation (ζ : Fin n → K) :
    centerMap E L b ζ + conjugation E L (centerMap E L b ζ) = 0 := by
  rw [centerMap_apply, map_smul, ← smul_add, (chartData E L).center_add, smul_zero]

/-- `B` restricted to the trace-zero line is bijective. -/
theorem bijective_scalar
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w) :
    Function.Bijective (B ∘ₗ centerMap E L b) := by
  constructor
  · intro ζ ζ' h
    have h1 : centerMap E L b ζ = centerMap E L b ζ' :=
      (hB _).unique ⟨centerMap_add_conjugation E L b ζ, rfl⟩
        ⟨centerMap_add_conjugation E L b ζ', h.symm⟩
    rw [centerMap_apply, centerMap_apply] at h1
    exact b.equivFun.symm.injective (smul_left_injective E (chartData E L).center_ne_zero h1)
  · intro w
    obtain ⟨z, ⟨hz, hBz⟩, -⟩ := hB w
    obtain ⟨c, hc⟩ := exists_algebraMap_mul_eq_of_traceZero E L (chartData E L).center_ne_zero
      (chartData E L).center_add hz
    refine ⟨b.equivFun c, ?_⟩
    rw [LinearMap.comp_apply, centerMap_apply, LinearEquiv.symm_apply_apply, Algebra.smul_def, hc,
      hBz]

theorem exists_scalarMatrix_inverse
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w) :
    ∃ M' : Matrix (Fin n) (Fin m) K,
      M' * scalarMatrix E L b B = 1 ∧ scalarMatrix E L b B * M' = 1 :=
  exists_toMatrix'_inverse _ (bijective_scalar E L b B hB)

end Linear

/-! ### The chart map on points -/

section Chart

open SU3Root WeilChart HeisenbergNormalForm

variable {K : Type u} [Field K] {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G U U₂ : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}
    {C : DoubleRootCommutatorPairing i a hj hj₂} (N : HeisenbergNormalForm C) {d m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (e' : ∀ T : Over (Spec (CommRingCat.of K)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)))
    (E L : Type u) [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [FiniteDimensional K E] [Algebra.IsQuadraticExtension E L]
    [Algebra.IsSeparable E L] {n : ℕ} (b : Module.Basis (Fin n) K E)
    (A : L →ₗ[K] (Fin d → K)) (B : L →ₗ[K] (Fin m → K)) (H : L →ₗ[K] L →ₗ[K] (Fin m → K))

/-- The chart map `Ψ_T` from points of `W` to points of `U`: the point of `W` with basis
components `(α, ζ)` goes to the chart point with coordinates `(Bm ζ + Q(α), Am α)`. -/
def chartMap (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (weilGroup K E L).X) : T ⟶ U.X :=
  N.testChartPoint e e' T
    (matVec (sections K T) (scalarMatrix E L b B) (pointComponents L b T x).2 +
      quad (sections K T) (chartCoeff E L b B H) (pointComponents L b T x).1)
    (matVec (sections K T) (vecMatrix E L b A) (pointComponents L b T x).1)

/-- The defect of the chart map from being multiplicative, a polynomial expression in the first
components `α, α'` of two points. -/
def defect (R : Type u) [CommRing R] [Algebra K R] (α α' : ULift.{u} (Fin 2) × Fin n → R) :
    Fin m → R :=
  matVec R (scalarMatrix E L b B) (weilForm b (chartData E L).coeff R α α') +
    quad R (chartCoeff E L b B H) (α + α') - quad R (chartCoeff E L b B H) α -
      quad R (chartCoeff E L b B H) α' -
        coordinatePairing e e' N.cocycle (matVec R (vecMatrix E L b A) α)
          (matVec R (vecMatrix E L b A) α')

variable {e e'}

/-- The Heisenberg law of chart points, with the coordinates and the cocycle written over the
relative global sections `sections K T`. -/
theorem testChartPoint_mul_sections (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (T : Over (Spec (CommRingCat.of K)))
    (w w' : Fin m → sections K T) (x x' : Fin d → sections K T) :
    N.testChartPoint e e' T w x * N.testChartPoint e e' T w' x' =
      N.testChartPoint e e' T
        ((w + w' + coordinatePairing (A := sections K T) e e' N.cocycle x x' :
          Fin m → sections K T))
        ((x + x' : Fin d → sections K T)) := by
  refine (N.testChartPoint_mul e e' T w w' x x').trans ?_
  exact congrArg (fun c : Fin m → sections K T => N.testChartPoint e e' T (w + w' + c) (x + x'))
    (chartCocycle_eq_coordinatePairing N he he' T x x')

/-- **Multiplicativity and the defect.** The chart map is multiplicative on two points exactly
when the defect vanishes on their first components. -/
theorem chartMap_mul_iff (he : IsNaturalVectorCoordinates e) (he' : IsNaturalVectorCoordinates e')
    (T : Over (Spec (CommRingCat.of K))) (x y : T ⟶ (weilGroup K E L).X) :
    chartMap N e e' E L b A B H T (x * y) =
        chartMap N e e' E L b A B H T x * chartMap N e e' E L b A B H T y ↔
      defect N e e' E L b A B H (sections K T) (pointComponents L b T x).1
        (pointComponents L b T y).1 = 0 := by
  have hmul := testChartPoint_mul_sections N he he' T
    (matVec (sections K T) (scalarMatrix E L b B) (pointComponents L b T x).2 +
      quad (sections K T) (chartCoeff E L b B H) (pointComponents L b T x).1)
    (matVec (sections K T) (scalarMatrix E L b B) (pointComponents L b T y).2 +
      quad (sections K T) (chartCoeff E L b B H) (pointComponents L b T y).1)
    (matVec (sections K T) (vecMatrix E L b A) (pointComponents L b T x).1)
    (matVec (sections K T) (vecMatrix E L b A) (pointComponents L b T y).1)
  rw [chartMap, chartMap, chartMap, hmul, pointComponents_mul_fst,
    pointComponents_mul_snd, defect]
  simp only [matVec_add]
  constructor
  · intro h
    have hw := (N.testChartPoint_injective e e' h).1
    change (_ : Fin m → sections K T) = _ at hw
    linear_combination hw
  · intro h
    congr 1
    linear_combination h

/-- **The rational chart.** On the rational point of a field parameter `p`, the chart map is
the chart form `incl(B v + H(u, u)) * sec(A u)`. -/
theorem chartMap_rationalPoint (p : rationalParameters E L) :
    chartMap N e e' E L b A B H (baseTest K) (rationalPoint L p) =
      N.chartPoint e e' (A p.first) (B p.second + H p.first p.first) := by
  rw [chartMap, pointComponents_rationalPoint, chartPoint_eq_testChartPoint]
  simp only [matVec_algebraMap, quad_algebraMap, matVec_self]
  rw [← chartForm_rationalComponents E L b B H p, vecMatrix_mulVec, towerBasis_rationalComponents]
  congr 1
  funext l
  rw [Pi.add_apply, ← map_add]
  rfl

omit [FiniteDimensional K E] in
/-- The defect is natural in the coefficient algebra. -/
theorem defect_map (he : IsNaturalVectorCoordinates e) (he' : IsNaturalVectorCoordinates e')
    {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R'] (f : R →ₐ[K] R')
    (α α' : ULift.{u} (Fin 2) × Fin n → R) :
    defect N e e' E L b A B H R' (fun q => f (α q)) (fun q => f (α' q)) =
      fun l => f (defect N e e' E L b A B H R α α' l) := by
  have hadd : (fun q => f (α q)) + (fun q => f (α' q)) = fun q => f ((α + α') q) := by
    funext q
    simp only [Pi.add_apply, map_add]
  simp only [defect]
  rw [weilForm_map, matVec_map, hadd, quad_map, quad_map, quad_map, matVec_map, matVec_map,
    coordinatePairing_naturality he he']
  funext l
  simp only [Pi.sub_apply, Pi.add_apply, map_sub, map_add]

omit [Algebra K L] [IsScalarTower K E L] in
/-- Every point of `W` over the identity test scheme is the rational point of a field
parameter. -/
theorem exists_rationalPoint_eq (x : baseTest K ⟶ (weilGroup K E L).X) :
    ∃ p : rationalParameters E L, rationalPoint L p = x :=
  ⟨unitaryRationalPointsEquiv E L (AffineWeil.sectionsEquiv K E (unitaryParameterGroup E L) x),
    by rw [rationalPoint, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]⟩

omit [Algebra K L] [IsScalarTower K E L] in
theorem rationalPoint_mul (p q : rationalParameters E L) :
    rationalPoint (K := K) L (p * q) = rationalPoint L p * rationalPoint L q := by
  simp only [rationalPoint, map_mul]

/-- **Rational multiplicativity.** Over the identity test scheme the chart map is
multiplicative, because `φ` is a homomorphism. -/
theorem chartMap_mul_baseTest (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (x y : baseTest K ⟶ (weilGroup K E L).X) :
    chartMap N e e' E L b A B H (baseTest K) (x * y) =
      chartMap N e e' E L b A B H (baseTest K) x * chartMap N e e' E L b A B H (baseTest K) y := by
  obtain ⟨p, rfl⟩ := exists_rationalPoint_eq E L x
  obtain ⟨q, rfl⟩ := exists_rationalPoint_eq E L y
  rw [← rationalPoint_mul, chartMap_rationalPoint, chartMap_rationalPoint, chartMap_rationalPoint,
    ← hφ, ← hφ, ← hφ, map_mul]

/-- The defect vanishes over the global sections of the identity test scheme. -/
theorem defect_baseTest_eq_zero (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (β β' : ULift.{u} (Fin 2) × Fin n → sections K (baseTest K)) :
    defect N e e' E L b A B H (sections K (baseTest K)) β β' = 0 := by
  have h := (chartMap_mul_iff N E L b A B H he he' (baseTest K)
    (componentPoint L b (baseTest K) (β, 0)) (componentPoint L b (baseTest K) (β', 0))).1
    (chartMap_mul_baseTest N E L b A B H φ hφ _ _)
  simpa only [pointComponents_componentPoint] using h

/-- The defect vanishes over `K`. -/
theorem defect_field_eq_zero (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (α α' : ULift.{u} (Fin 2) × Fin n → K) :
    defect N e e' E L b A B H K α α' = 0 := by
  let ε : K →ₐ[K] sections K (baseTest K) :=
    (identitySectionsEquiv (CommRingCat.of K)).symm.toAlgHom
  have h := defect_map N E L b A B H he he' ε α α'
  rw [defect_baseTest_eq_zero N E L b A B H he he' φ hφ] at h
  funext l
  have hl := congrFun h l
  have hinj : Function.Injective ε := (identitySectionsEquiv (CommRingCat.of K)).symm.injective
  apply hinj
  rw [← hl, Pi.zero_apply, Pi.zero_apply, map_zero]

/-- **The defect vanishes identically**, by the polynomial identity principle. -/
theorem defect_eq_zero [Infinite K] (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (R : Type u) [CommRing R] [Algebra K R] (α α' : ULift.{u} (Fin 2) × Fin n → R) :
    defect N e e' E L b A B H R α α' = 0 :=
  eq_zero_of_natural (K := K)
    (I := (ULift.{u} (Fin 2) × Fin n) ⊕ (ULift.{u} (Fin 2) × Fin n))
    (fun R _ _ x => defect N e e' E L b A B H R (fun q => x (Sum.inl q)) (fun q => x (Sum.inr q)))
    (fun _ _ _ _ _ _ f _ => defect_map N E L b A B H he he' f _ _)
    (fun _ => defect_field_eq_zero N E L b A B H he he' φ hφ _ _) R (Sum.elim α α')

/-- **Multiplicativity of the chart map** over every test scheme. -/
theorem chartMap_mul [Infinite K] (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (T : Over (Spec (CommRingCat.of K))) (x y : T ⟶ (weilGroup K E L).X) :
    chartMap N e e' E L b A B H T (x * y) =
      chartMap N e e' E L b A B H T x * chartMap N e e' E L b A B H T y :=
  (chartMap_mul_iff N E L b A B H he he' T x y).2 (defect_eq_zero N E L b A B H he he' φ hφ _ _ _)

/-- **Bijectivity of the chart map**, from the invertibility of the coordinate matrices. -/
theorem chartMap_bijective (hA : Function.Bijective A)
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w)
    (T : Over (Spec (CommRingCat.of K))) :
    Function.Bijective (chartMap N e e' E L b A B H T) := by
  obtain ⟨Am', hAm1, hAm2⟩ := exists_vecMatrix_inverse E L b A hA
  obtain ⟨Bm', hBm1, hBm2⟩ := exists_scalarMatrix_inverse E L b B hB
  constructor
  · intro x y hxy
    obtain ⟨hw, hx⟩ := N.testChartPoint_injective e e' hxy
    change (_ : Fin m → sections K T) = _ at hw
    change (_ : Fin d → sections K T) = _ at hx
    have h1 : (pointComponents L b T x).1 = (pointComponents L b T y).1 := matVec_injective hAm1 hx
    rw [h1] at hw
    have h2 : (pointComponents L b T x).2 = (pointComponents L b T y).2 :=
      matVec_injective hBm1 (add_right_cancel hw)
    have h := congrArg (componentPoint L b T) (Prod.ext h1 h2)
    simpa only [componentPoint_pointComponents] using h
  · intro g
    obtain ⟨w, x, hwx⟩ := N.exists_testChartPoint_eq e e' g
    let w' : Fin m → sections K T := w
    let x' : Fin d → sections K T := x
    let α : ULift.{u} (Fin 2) × Fin n → sections K T := matVec (sections K T) Am' x'
    let ζ : Fin n → sections K T :=
      matVec (sections K T) Bm' (w' - quad (sections K T) (chartCoeff E L b B H) α)
    refine ⟨componentPoint L b T (α, ζ), ?_⟩
    have h1 : matVec (sections K T) (scalarMatrix E L b B) ζ +
        quad (sections K T) (chartCoeff E L b B H) α = w' := by
      simp only [ζ, matVec_matVec_eq_self hBm2, sub_add_cancel]
    have h2 : matVec (sections K T) (vecMatrix E L b A) α = x' := matVec_matVec_eq_self hAm2 x'
    rw [chartMap, pointComponents_componentPoint]
    exact (congrArg₂ (N.testChartPoint e e' T) h1 h2).trans hwx

/-- **Naturality of the chart map** in the test scheme. -/
theorem chartMap_naturality (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') {T T' : Over (Spec (CommRingCat.of K))} (f : T' ⟶ T)
    (x : T ⟶ (weilGroup K E L).X) :
    chartMap N e e' E L b A B H T' (f ≫ x) = f ≫ chartMap N e e' E L b A B H T x := by
  have hc := comp_testChartPoint N he he' f
    (matVec (sections K T) (scalarMatrix E L b B) (pointComponents L b T x).2 +
      quad (sections K T) (chartCoeff E L b B H) (pointComponents L b T x).1)
    (matVec (sections K T) (vecMatrix E L b A) (pointComponents L b T x).1)
  rw [chartMap, chartMap, hc, pointComponents_naturality]
  let g : sections K T →ₐ[K] sections K T' := ((algΓ (CommRingCat.of K)).map f).unop.hom
  have h1 := matVec_add_quad_map g (scalarMatrix E L b B) (chartCoeff E L b B H)
    (pointComponents L b T x).2 (pointComponents L b T x).1
  have h2 := matVec_map g (vecMatrix E L b A) (pointComponents L b T x).1
  exact congrArg₂ (N.testChartPoint e e' T') h1 h2

/-- The chart maps as multiplicative equivalences of points. -/
def pointsMulEquiv [Infinite K] (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (hA : Function.Bijective A)
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w)
    (T : Over (Spec (CommRingCat.of K))) : (T ⟶ (weilGroup K E L).X) ≃* (T ⟶ U.X) :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (chartMap N e e' E L b A B H T) (chartMap_mul N E L b A B H he he' φ hφ T))
    (chartMap_bijective N E L b A B H hA hB T)

theorem pointsMulEquiv_apply [Infinite K] (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (hA : Function.Bijective A)
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w)
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (weilGroup K E L).X) :
    pointsMulEquiv N E L b A B H he he' φ hφ hA hB T x = chartMap N e e' E L b A B H T x :=
  rfl

/-- **The chart isomorphism** `W ≅ U` of group schemes. -/
def chartIso [Infinite K] (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (hA : Function.Bijective A)
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w) :
    weilGroup K E L ≅ U :=
  isoOfPoints (pointsMulEquiv N E L b A B H he he' φ hφ hA hB)
    (fun f x => chartMap_naturality N E L b A B H he he' f x)

theorem comp_chartIso_hom [Infinite K] (he : IsNaturalVectorCoordinates e)
    (he' : IsNaturalVectorCoordinates e') (φ : rationalParameters E L →* rationalPoints U)
    (hφ : ∀ p, φ p = N.chartPoint e e' (A p.first) (B p.second + H p.first p.first))
    (hA : Function.Bijective A)
    (hB : ∀ w : Fin m → K, ∃! z : L, z + conjugation E L z = 0 ∧ B z = w)
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (weilGroup K E L).X) :
    x ≫ (chartIso N E L b A B H he he' φ hφ hA hB).hom.hom.hom =
      chartMap N e e' E L b A B H T x :=
  comp_isoOfPoints_hom _ _ T x

end Chart

end UnitaryChartUpgrade

open UnitaryChartUpgrade SU3Root WeilChart in
/-- **Upgrade of unitary charts.** The chart isomorphism `R_{E/K} U_{L/E} ≅ U` built from the
chart form of `φ` restricts to `φ` on rational points, and its composite with `j` represents
the root subgroup `U_a`. -/
theorem unitaryChartUpgrade : UnitaryChartUpgradeStatement.{u} := by
  intro K _ _ S G U U₂ _ _ _ _ _ i a j hj j₂ hj₂ C _ N _ _ _ d m e e' he he' E L _ _ _ _ _ _ _ _ _ _
    _ _ A B H φ hA hB hφ
  let b := Module.finBasis K E
  refine ⟨(chartIso N E L b A B H he.1 he'.1 φ hφ hA hB).hom, fun p => ?_, ?_⟩
  · rw [rationalPoints.map_apply]
    exact (comp_chartIso_hom N E L b A B H he.1 he'.1 φ hφ hA hB _ _).trans
      ((chartMap_rationalPoint N E L b A B H p).trans (hφ p).symm)
  · refine ⟨?_, (SubgroupFunctor.range_iso_comp _ j).trans hj.2⟩
    let iso := chartIso N E L b A B H he.1 he'.1 φ hφ hA hB
    have hsplit : iso.hom.hom.hom ≫ iso.inv.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, iso.hom_inv_id, Grp.id_hom_hom]
    have : IsSplitMono iso.hom.hom.hom := IsSplitMono.mk' ⟨_, hsplit⟩
    have := hj.1
    rw [Grp.comp_hom_hom]
    exact mono_comp _ _

end Langlands.GroupScheme.RelativeRoot
