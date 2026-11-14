import Langlands.GroupScheme.BilinearCoordinateGroup
import Langlands.GroupScheme.Examples.SU3RootHeisenbergComparison
import Langlands.GroupScheme.Rational.Characters
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-! # Bilinear coordinates on the quadratic unitary parameter group

Let `L / k` be a separable quadratic extension with conjugation `σ`. For a commutative
`k`-algebra `S`, the published quadratic root parameters over `S` are the pairs `(u, v)` in
`S ⊗[k] L` with `v + bar(v) = u * bar(u)` and law `(u, v)(u', v') = (u + u', v + v' + u * bar(u'))`.
Given a `k`-basis `e` of `L`, an element `λ` with `λ + σ(λ) = 1` and a nonzero `f` with
`f + σ(f) = 0`, the map `(a, b) ↦ (∑ aᵢ ⊗ eᵢ, b ⊗ f + λ u bar(u))` identifies the bilinear
coordinate group of `BilinearCoordinateGroup` with these parameters, naturally in `S`. This
module proves this and uses it to construct the actual affine group scheme over `Spec k`
corepresenting the published functor `tensorParametersFunctor k L`.
-/

noncomputable section

universe u v w w'

open scoped TensorProduct
open CategoryTheory Opposite AlgebraicGeometry Module

attribute [local instance] CategoryTheory.Hom.group

namespace Langlands.GroupScheme.SU3Root

open BilinearCoordinate

section Field

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

local notation "σ" => conjugation k L

local instance su3RootUnitaryCoordinatesFiniteDimensional : FiniteDimensional k L :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two k L]; decide)

/-- The bilinear correction `σ(λ) x σ(y) − λ σ(x) y` of the coordinate change (C.4.1). -/
def correction (lam x y : L) : L := σ lam * x * σ y - lam * σ x * y

/-- The correction has trace zero, for every `λ`. -/
theorem correction_add_conjugation (lam x y : L) :
    correction k L lam x y + σ (correction k L lam x y) = 0 := by
  have h : ∀ z, σ (σ z) = z := conjugation_involutive k L
  simp only [correction, map_sub, map_mul, h]
  ring

theorem correction_smul_left (lam : L) (c : k) (x y : L) :
    correction k L lam (algebraMap k L c * x) y = algebraMap k L c * correction k L lam x y := by
  simp only [correction, map_mul, AlgEquiv.commutes]
  ring

theorem correction_smul_right (lam : L) (c : k) (x y : L) :
    correction k L lam x (algebraMap k L c * y) = algebraMap k L c * correction k L lam x y := by
  simp only [correction, map_mul, AlgEquiv.commutes]
  ring

theorem correction_add_left (lam x x' y : L) :
    correction k L lam (x + x') y = correction k L lam x y + correction k L lam x' y := by
  simp only [correction, map_add]
  ring

theorem correction_add_right (lam x y y' : L) :
    correction k L lam x (y + y') = correction k L lam x y + correction k L lam x y' := by
  simp only [correction, map_add]
  ring

/-- A trace-zero element is a `k`-multiple of any nonzero trace-zero element. -/
theorem exists_algebraMap_mul_eq_of_traceZero {f z : L} (hf : f ≠ 0) (hf' : f + σ f = 0)
    (hz : z + σ z = 0) : ∃ c : k, algebraMap k L c * f = z := by
  have hσf : σ f = -f := by linear_combination hf'
  have hσz : σ z = -z := by linear_combination hz
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_conjugation_eq k L (x := z / f) (by
    rw [map_div₀, hσf, hσz, neg_div_neg_eq])
  exact ⟨c, by rw [hc, div_mul_cancel₀ _ hf]⟩

/-- The data of a bilinear coordinate chart on the unitary parameter group: a `k`-basis `e`
of `L`, an element `λ` of trace one, a nonzero trace-zero element `f`, and the coefficients
`cᵢⱼ` with `cᵢⱼ f = σ(λ) eᵢ σ(eⱼ) − λ σ(eᵢ) eⱼ`. -/
structure CoordinateData (ι : Type w) [Fintype ι] where
  /-- The basis of the vector coordinate. -/
  basis : Basis ι k L
  /-- The trace-one element `λ`. -/
  traceOne : L
  traceOne_add : traceOne + σ traceOne = 1
  /-- The trace-zero generator `f` of the scalar coordinate. -/
  center : L
  center_ne_zero : center ≠ 0
  center_add : center + σ center = 0
  /-- The cocycle coefficients. -/
  coeff : ι → ι → k
  coeff_mul_center : ∀ i j,
    algebraMap k L (coeff i j) * center = correction k L traceOne (basis i) (basis j)

namespace CoordinateData

variable {k L} {ι : Type w} [Fintype ι] (D : CoordinateData k L ι)

/-- The elements `f` and `λ` are linearly independent. -/
theorem linearIndependent_center_traceOne : LinearIndependent k ![D.center, D.traceOne] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [Algebra.smul_def, Algebra.smul_def] at h
  have hσ := congrArg σ h
  rw [map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_zero] at hσ
  have ht : algebraMap k L t = 0 := by
    linear_combination h + hσ - algebraMap k L s * D.center_add -
      algebraMap k L t * D.traceOne_add
  have ht' : t = 0 := (map_eq_zero_iff _ (algebraMap k L).injective).mp ht
  refine ⟨?_, ht'⟩
  rw [ht, zero_mul, add_zero] at h
  exact (map_eq_zero_iff _ (algebraMap k L).injective).mp
    ((mul_eq_zero.mp h).resolve_right D.center_ne_zero)

/-- The basis `(f, λ)` of `L`, adapted to the trace. -/
def traceBasis : Basis (Fin 2) k L :=
  basisOfLinearIndependentOfCardEqFinrank D.linearIndependent_center_traceOne
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two k L, Fintype.card_fin])

@[simp] theorem traceBasis_zero : D.traceBasis 0 = D.center := by
  simp [traceBasis]

@[simp] theorem traceBasis_one : D.traceBasis 1 = D.traceOne := by
  simp [traceBasis]

/-- A chart with arbitrary basis, `λ` and `f`: the coefficients are determined. -/
theorem exists_coeff (lam f : L) (hf : f ≠ 0) (hf' : f + σ f = 0) (x y : L) :
    ∃ c : k, algebraMap k L c * f = correction k L lam x y :=
  exists_algebraMap_mul_eq_of_traceZero k L hf hf' (correction_add_conjugation k L lam x y)

end CoordinateData

/-- The chart determined by a basis, `λ` and `f`, with the coefficients it forces. -/
def CoordinateData.ofBasis {ι : Type w} [Fintype ι] (e : Basis ι k L) (lam : L)
    (hlam : lam + σ lam = 1) (f : L) (hf : f ≠ 0) (hf' : f + σ f = 0) :
    CoordinateData k L ι where
  basis := e
  traceOne := lam
  traceOne_add := hlam
  center := f
  center_ne_zero := hf
  center_add := hf'
  coeff i j := Classical.choose (CoordinateData.exists_coeff lam f hf hf' (e i) (e j))
  coeff_mul_center i j := Classical.choose_spec (CoordinateData.exists_coeff lam f hf hf' (e i) (e j))

/-- The canonical chart: Mathlib's chosen basis, the published trace-one element and a chosen
nonzero trace-zero element. -/
def canonicalCoordinateData : CoordinateData k L (ULift.{w} (Fin 2)) :=
  CoordinateData.ofBasis k L ((Module.finBasisOfFinrankEq k L
      (Algebra.IsQuadraticExtension.finrank_eq_two k L)).reindex Equiv.ulift.symm)
    (traceOne k L) (traceOne_add_conjugate k L)
    (Classical.choose (exists_ne_zero_add_conjugation_eq_zero k L))
    (Classical.choose_spec (exists_ne_zero_add_conjugation_eq_zero k L)).1
    (Classical.choose_spec (exists_ne_zero_add_conjugation_eq_zero k L)).2

end Field

/-! ### The identification on a test algebra -/

section Tensor

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {ι : Type w} [Fintype ι] (D : CoordinateData k L ι)
  (S : Type w') [CommRing S] [Algebra k S]

local notation "σ" => conjugation k L

omit [Fintype ι] in
@[simp] theorem tensorBar_tmul (s : S) (x : L) :
    (tensorInvolution k L S).bar (s ⊗ₜ[k] x) = s ⊗ₜ[k] σ x := rfl

/-- The cocycle coefficients in `S`. -/
abbrev coeffs : ι → ι → S := fun i j => algebraMap k S (D.coeff i j)

/-- The vector `u = ∑ aᵢ ⊗ eᵢ`. -/
def tensorVec (a : ι → S) : S ⊗[k] L := ∑ i, a i ⊗ₜ[k] D.basis i

/-- The second parameter `b ⊗ f + λ u bar(u)`. -/
def secondCoord (a : ι → S) (b : S) : S ⊗[k] L :=
  b ⊗ₜ[k] D.center + (1 ⊗ₜ[k] D.traceOne) * tensorVec D S a * (tensorInvolution k L S).bar (tensorVec D S a)

theorem tensorVec_add (a a' : ι → S) :
    tensorVec D S (a + a') = tensorVec D S a + tensorVec D S a' := by
  simp only [tensorVec, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]

@[simp] theorem tensorVec_zero : tensorVec D S 0 = 0 := by
  simp [tensorVec]

theorem traceOne_tmul_add_bar :
    (1 ⊗ₜ[k] D.traceOne : S ⊗[k] L) + (tensorInvolution k L S).bar (1 ⊗ₜ[k] D.traceOne) = 1 := by
  rw [tensorBar_tmul, ← TensorProduct.tmul_add, D.traceOne_add, Algebra.TensorProduct.one_def]

theorem center_tmul_add_bar (b : S) :
    b ⊗ₜ[k] D.center + (tensorInvolution k L S).bar (b ⊗ₜ[k] D.center) = 0 := by
  rw [tensorBar_tmul, ← TensorProduct.tmul_add, D.center_add, TensorProduct.tmul_zero]

theorem secondCoord_add_bar (a : ι → S) (b : S) :
    secondCoord D S a b + (tensorInvolution k L S).bar (secondCoord D S a b) =
      tensorVec D S a * (tensorInvolution k L S).bar (tensorVec D S a) := by
  have h1 := center_tmul_add_bar D S b
  have h2 := traceOne_tmul_add_bar D S
  simp only [secondCoord, map_add, map_mul, RingInvolution.bar_bar]
  linear_combination h1 + (tensorVec D S a * (tensorInvolution k L S).bar (tensorVec D S a)) * h2

theorem const_mul_tensorVec_mul_bar (z : L) (a a' : ι → S) :
    (1 ⊗ₜ[k] z) * tensorVec D S a * (tensorInvolution k L S).bar (tensorVec D S a') =
      ∑ i, ∑ j, (a i * a' j) ⊗ₜ[k] (z * D.basis i * σ (D.basis j)) := by
  simp only [tensorVec, map_sum, tensorBar_tmul, Finset.mul_sum, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact Finset.sum_comm

theorem const_mul_bar_mul_tensorVec (z : L) (a a' : ι → S) :
    (1 ⊗ₜ[k] z) * (tensorInvolution k L S).bar (tensorVec D S a) * tensorVec D S a' =
      ∑ i, ∑ j, (a i * a' j) ⊗ₜ[k] (z * σ (D.basis i) * D.basis j) := by
  simp only [tensorVec, map_sum, tensorBar_tmul, Finset.mul_sum, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact Finset.sum_comm

theorem form_tmul_center (a a' : ι → S) :
    form (coeffs D S) a a' ⊗ₜ[k] D.center =
      (tensorInvolution k L S).bar (1 ⊗ₜ[k] D.traceOne) * tensorVec D S a * (tensorInvolution k L S).bar (tensorVec D S a') -
        (1 ⊗ₜ[k] D.traceOne) * (tensorInvolution k L S).bar (tensorVec D S a) * tensorVec D S a' := by
  rw [tensorBar_tmul, const_mul_tensorVec_mul_bar, const_mul_bar_mul_tensorVec,
    ← Finset.sum_sub_distrib]
  simp only [form, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.tmul_sub, mul_assoc, ← Algebra.smul_def, TensorProduct.smul_tmul,
    Algebra.smul_def, D.coeff_mul_center]
  rfl

/-- The parameter attached to bilinear coordinates. -/
def toParametersFun (x : Coordinates (coeffs D S)) : tensorParameters k L S :=
  ⟨(tensorVec D S x.vec, secondCoord D S x.vec x.scalar), secondCoord_add_bar D S x.vec x.scalar⟩

@[simp] theorem first_toParametersFun (x : Coordinates (coeffs D S)) :
    (toParametersFun D S x).first = tensorVec D S x.vec := rfl

@[simp] theorem second_toParametersFun (x : Coordinates (coeffs D S)) :
    (toParametersFun D S x).second = secondCoord D S x.vec x.scalar := rfl

/-- The `S`-basis `1 ⊗ eᵢ` of `S ⊗[k] L`. -/
abbrev tensorBasis : Basis ι S (S ⊗[k] L) := Algebra.TensorProduct.basis S D.basis

/-- The `S`-basis `(1 ⊗ f, 1 ⊗ λ)` of `S ⊗[k] L`. -/
abbrev tensorTraceBasis : Basis (Fin 2) S (S ⊗[k] L) := Algebra.TensorProduct.basis S D.traceBasis

theorem tensorVec_eq (a : ι → S) : tensorVec D S a = (tensorBasis D S).equivFun.symm a := by
  simp [tensorVec, TensorProduct.smul_tmul']

/-- The vector coordinates of an element of `S ⊗[k] L`. -/
def vecCoord (y : S ⊗[k] L) : ι → S := (tensorBasis D S).equivFun y

theorem tensorVec_vecCoord (y : S ⊗[k] L) : tensorVec D S (vecCoord D S y) = y := by
  rw [tensorVec_eq, vecCoord, LinearEquiv.symm_apply_apply]

theorem vecCoord_tensorVec (a : ι → S) : vecCoord D S (tensorVec D S a) = a := by
  rw [tensorVec_eq, vecCoord, LinearEquiv.apply_symm_apply]

/-- The scalar coordinate of a trace-zero element of `S ⊗[k] L`. -/
def scalarCoord (y : S ⊗[k] L) : S := (tensorTraceBasis D S).repr y 0

theorem scalarCoord_tmul (b : S) : scalarCoord D S (b ⊗ₜ[k] D.center) = b := by
  have h : b ⊗ₜ[k] D.center = b • tensorTraceBasis D S 0 := by
    rw [Algebra.TensorProduct.basis_repr_symm_apply', D.traceBasis_zero]
  rw [scalarCoord, h, map_smul, Basis.repr_self]
  simp

/-- A trace-zero element of `S ⊗[k] L` is `b ⊗ f` for its scalar coordinate `b`. -/
theorem eq_scalarCoord_tmul {y : S ⊗[k] L} (hy : y + (tensorInvolution k L S).bar y = 0) :
    y = scalarCoord D S y ⊗ₜ[k] D.center := by
  have hsum := (tensorTraceBasis D S).sum_repr y
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_repr_symm_apply',
    Algebra.TensorProduct.basis_repr_symm_apply', D.traceBasis_zero,
    D.traceBasis_one] at hsum
  set p := (tensorTraceBasis D S).repr y 0
  set q := (tensorTraceBasis D S).repr y 1
  have hq : q ⊗ₜ[k] (1 : L) = 0 := by
    have h := hy
    rw [← hsum, map_add, tensorBar_tmul, tensorBar_tmul] at h
    have h1 := center_tmul_add_bar D S p
    rw [tensorBar_tmul] at h1
    calc q ⊗ₜ[k] (1 : L) = q ⊗ₜ[k] (D.traceOne + σ D.traceOne) := by rw [D.traceOne_add]
      _ = p ⊗ₜ[k] D.center + q ⊗ₜ[k] D.traceOne + (p ⊗ₜ[k] σ D.center + q ⊗ₜ[k] σ D.traceOne) -
          (p ⊗ₜ[k] D.center + p ⊗ₜ[k] σ D.center) := by
        rw [TensorProduct.tmul_add]; abel
      _ = 0 := by rw [h, h1, sub_zero]
  have hq0 : q = 0 := by
    apply Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := L)
      (algebraMap k L).injective
    simpa [Algebra.TensorProduct.includeLeft_apply] using hq
  rw [hq0, TensorProduct.zero_tmul, add_zero] at hsum
  exact hsum.symm

/-- The trace-zero part `v − λ u bar(u)` of a parameter. -/
def traceZeroPart (p : tensorParameters k L S) : S ⊗[k] L :=
  p.second - (1 ⊗ₜ[k] D.traceOne) * p.first * (tensorInvolution k L S).bar p.first

theorem traceZeroPart_add_bar (p : tensorParameters k L S) :
    traceZeroPart D S p + (tensorInvolution k L S).bar (traceZeroPart D S p) = 0 := by
  have h1 := p.equation
  have h2 := traceOne_tmul_add_bar D S
  simp only [traceZeroPart, map_sub, map_mul, RingInvolution.bar_bar]
  linear_combination h1 - (p.first * (tensorInvolution k L S).bar p.first) * h2

/-- The bilinear coordinates of a parameter. -/
def ofParameters (p : tensorParameters k L S) : Coordinates (coeffs D S) :=
  ⟨vecCoord D S p.first, scalarCoord D S (traceZeroPart D S p)⟩

/-- **Generic coordinates.** Bilinear coordinates with the coefficients `cᵢⱼ` are identified
with the quadratic root parameters over `S`, by `(a, b) ↦ (∑ aᵢ ⊗ eᵢ, b ⊗ f + λ u bar(u))`. -/
def toParameters : Coordinates (coeffs D S) ≃* tensorParameters k L S where
  toFun := toParametersFun D S
  invFun := ofParameters D S
  left_inv x := by
    apply Coordinates.ext
    · exact vecCoord_tensorVec D S x.vec
    · change scalarCoord D S (secondCoord D S x.vec x.scalar -
          (1 ⊗ₜ[k] D.traceOne) * tensorVec D S x.vec * (tensorInvolution k L S).bar (tensorVec D S x.vec)) = x.scalar
      rw [secondCoord, add_sub_cancel_right, scalarCoord_tmul]
  right_inv p := by
    apply Parameters.ext
    · exact tensorVec_vecCoord D S p.first
    · change secondCoord D S (vecCoord D S p.first) (scalarCoord D S (traceZeroPart D S p)) =
        p.second
      rw [secondCoord, tensorVec_vecCoord, ← eq_scalarCoord_tmul D S (traceZeroPart_add_bar D S p),
        traceZeroPart, sub_add_cancel]
  map_mul' x y := by
    apply Parameters.ext
    · exact tensorVec_add D S x.vec y.vec
    · change secondCoord D S (x.vec + y.vec) (x.scalar + y.scalar + form (coeffs D S) x.vec y.vec) =
        secondCoord D S x.vec x.scalar + secondCoord D S y.vec y.scalar +
          tensorVec D S x.vec * (tensorInvolution k L S).bar (tensorVec D S y.vec)
      have hk := form_tmul_center D S x.vec y.vec
      have hΛ := traceOne_tmul_add_bar D S
      simp only [secondCoord, tensorVec_add, map_add, TensorProduct.add_tmul]
      linear_combination hk + (tensorVec D S x.vec * (tensorInvolution k L S).bar (tensorVec D S y.vec)) * hΛ

@[simp] theorem first_toParameters (x : Coordinates (coeffs D S)) :
    (toParameters D S x).first = ∑ i, x.vec i ⊗ₜ[k] D.basis i := rfl

@[simp] theorem second_toParameters (x : Coordinates (coeffs D S)) :
    (toParameters D S x).second = x.scalar ⊗ₜ[k] D.center +
      (1 ⊗ₜ[k] D.traceOne) * tensorVec D S x.vec * (tensorInvolution k L S).bar (tensorVec D S x.vec) := rfl

/-- The identification is natural in the test algebra. -/
theorem toParameters_naturality {S' : Type w'} [CommRing S'] [Algebra k S'] (g : S →ₐ[k] S')
    (x : Coordinates (coeffs D S)) :
    toParameters D S' (Coordinates.map g.toRingHom (fun i j => g.commutes (D.coeff i j)) x) =
      tensorParametersMap k L g (toParameters D S x) := by
  have hvec : tensorVec D S' (fun i => g (x.vec i)) =
      tensorCoefficientMap k L g (tensorVec D S x.vec) := by
    simp [tensorVec, map_sum]
  apply Parameters.ext
  · exact hvec
  · change secondCoord D S' (fun i => g (x.vec i)) (g x.scalar) =
      tensorCoefficientMap k L g (secondCoord D S x.vec x.scalar)
    simp only [secondCoord, map_add, map_mul, tensorCoefficientMap_tmul, map_one,
      tensorCoefficientMap_bar, hvec]

end Tensor

/-! ### The group scheme -/

section Scheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {ι : Type u} [Fintype ι] (D : CoordinateData k L ι)

/-- A chart corepresents the published quadratic tensor parameter functor by the polynomial
ring `k[xᵢ, y]`. -/
def corepresentableBy :
    (tensorParametersFunctor.{u} k L ⋙ forget GrpCat).CorepresentableBy
      (coordinateAlgebra (CommRingCat.of k) ι) where
  homEquiv := (BilinearCoordinate.corepresentableBy (CommRingCat.of k) D.coeff).homEquiv.trans
    (toParameters D _).toEquiv
  homEquiv_comp g f := by
    change toParameters D _
        ((BilinearCoordinate.corepresentableBy (CommRingCat.of k) D.coeff).homEquiv (f ≫ g)) =
      tensorParametersMap k L g.hom (toParameters D _
        ((BilinearCoordinate.corepresentableBy (CommRingCat.of k) D.coeff).homEquiv f))
    rw [(BilinearCoordinate.corepresentableBy (CommRingCat.of k) D.coeff).homEquiv_comp]
    exact toParameters_naturality D _ g.hom _

/-- The affine group scheme over `Spec k` attached to a chart. -/
abbrev chartGroupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.groupScheme (tensorParametersFunctor.{u} k L) (corepresentableBy k L D)

/-- **The unitary parameter group scheme** `U_{L/k}` over `Spec k`: the affine group scheme
corepresenting the published functor of quadratic root parameters, built from the canonical
chart. -/
abbrev unitaryParameterGroup : GroupScheme (Spec (CommRingCat.of k)) :=
  chartGroupScheme k L (canonicalCoordinateData.{u, u, u} k L)

/-- Points of `U_{L/k}` over every test scheme `T` are the quadratic root parameters over the
relative global sections of `T`. -/
def unitaryPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (unitaryParameterGroup k L).X) ≃*
      tensorParameters k L ((algΓ (CommRingCat.of k)).obj T).unop :=
  Corepresented.pointsEquiv (R := CommRingCat.of k) (tensorParametersFunctor.{u} k L)
    (corepresentableBy k L (canonicalCoordinateData.{u, u, u} k L)) T

/-- The point identification is natural in the test scheme. -/
theorem unitaryPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (unitaryParameterGroup k L).X) :
    unitaryPointsEquiv k L T' (a ≫ x) =
      tensorParametersMap k L ((algΓ (CommRingCat.of k)).map a).unop.hom
        (unitaryPointsEquiv k L T x) :=
  Corepresented.pointsEquiv_naturality (R := CommRingCat.of k)
    (tensorParametersFunctor.{u} k L)
    (corepresentableBy k L (canonicalCoordinateData.{u, u, u} k L)) a x

end Scheme

/-! ### Rational points -/

section Rational

/-- The relative global sections of the identity test scheme are the base ring. -/
def identitySectionsEquiv (R : CommRingCat.{u}) :
    ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop ≃ₐ[R] R :=
  AlgEquiv.ofRingEquiv (f := ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv :
      ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop ≃+* R)) (fun r => by
    change (Scheme.ΓSpecIso R).hom ((𝟙 (Spec R) : Spec R ⟶ Spec R).appTop
      ((Scheme.ΓSpecIso R).inv r)) = r
    simp)

theorem identitySectionsEquiv_apply (R : CommRingCat.{u})
    (y : ((algΓ R).obj (Over.mk (𝟙 (Spec R)))).unop) :
    identitySectionsEquiv R y = (Scheme.ΓSpecIso R).hom y := rfl

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Coefficient change along an algebra isomorphism identifies parameter groups. -/
def tensorParametersCongr {S : Type w} {S' : Type w'} [CommRing S] [CommRing S'] [Algebra k S]
    [Algebra k S'] (e : S ≃ₐ[k] S') : tensorParameters k L S ≃* tensorParameters k L S' :=
  Parameters.mapEquiv (Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[k] L)).toRingEquiv
    (fun a => by
      induction a using TensorProduct.inductionOn with
      | tmul s x => rfl
      | add x y hx hy => simp only [map_add, hx, hy])

@[simp] theorem first_tensorParametersCongr {S : Type w} {S' : Type w'} [CommRing S]
    [CommRing S'] [Algebra k S] [Algebra k S'] (e : S ≃ₐ[k] S') (p : tensorParameters k L S) :
    (tensorParametersCongr k L e p).first =
      Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[k] L) p.first := rfl

@[simp] theorem second_tensorParametersCongr {S : Type w} {S' : Type w'} [CommRing S]
    [CommRing S'] [Algebra k S] [Algebra k S'] (e : S ≃ₐ[k] S') (p : tensorParameters k L S) :
    (tensorParametersCongr k L e p).second =
      Algebra.TensorProduct.congr e (AlgEquiv.refl : L ≃ₐ[k] L) p.second := rfl

end Rational

section RationalPoints

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- **Rational points.** The `k`-points of `U_{L/k}` are the field parameters
`{(u, v) ∈ L² | v + σ(v) = u σ(u)}` with the published law. -/
def unitaryRationalPointsEquiv :
    rationalPoints (unitaryParameterGroup k L) ≃* rationalParameters k L :=
  (unitaryPointsEquiv k L (Over.mk (𝟙 _))).trans
    ((tensorParametersCongr k L (identitySectionsEquiv (CommRingCat.of k))).trans
      (rationalParametersEquiv k L))

end RationalPoints

end Langlands.GroupScheme.SU3Root
