import Langlands.GroupScheme.CentralSurjectionImage.BimultRigidity

/-! # Rigidity over rings with connected spectrum -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

/-- An idempotent of a ring with connected spectrum is zero or one. -/
theorem idempotent_eq_zero_or_one {R : Type u} [CommRing R]
    [PreconnectedSpace (PrimeSpectrum R)] {e : R} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
    exact TopologicalSpace.Opens.ext (by simpa using h)
  · right
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
    exact TopologicalSpace.Opens.ext (by simpa using h)

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left]

/-- A multiplicative point with connected coefficient spectrum that specializes to
one is identically one, including over nonreduced coefficient rings. -/
theorem IsMultG.eq_one_of_connectedSpectrum {R : Type u} [CommRing R] [PreconnectedSpace (PrimeSpectrum R)] [Algebra k R]
    {Λ : Type u} [AddCommGroup Λ] {p : Lie.AffinePoints G (AddMonoidAlgebra R Λ)}
    (hp : IsMultG p) (ev : R →ₐ[k] k)
    (h1 : Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ ev) p = 1) : p = 1 := by
  classical
  apply hp.eq_one_of_weight_eq_zero
  intro γ hγ
  let : Bialgebra (CommRingCat.of k) (coordAlgebra G) :=
    AffineLinearEmbedding.bialgebra (corep G)
  apply LinearMap.ext
  intro b
  obtain ⟨N, Mx, hcomul, hcounit, hspan⟩ :=
    AffineLinearEmbedding.exists_matrix_coefficients (K := CommRingCat.of k)
      (B := coordAlgebra G) {b}
  let P : Λ → Matrix (Fin N) (Fin N) R := fun δ => Matrix.of fun i j => weight p δ (Mx i j)
  have hPmul : ∀ δ ε, P δ * P ε = if δ = ε then P δ else 0 := by
    intro δ ε
    ext i j
    have h := LinearMap.congr_fun (hp.conv_weight δ ε) (Mx i j)
    have hc : (comul G) (Mx i j) = ∑ l, Mx i l ⊗ₜ[CommRingCat.of k] Mx l j := hcomul i j
    simp only [conv, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, hc,
      map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply] at h
    rw [Matrix.mul_apply]
    simp only [P, Matrix.of_apply]
    rw [h]
    split_ifs <;> simp
  have hP0 : (P 0).map ev = 1 := by
    ext i j
    simp only [Matrix.map_apply, P, Matrix.of_apply]
    rw [← weight_coeffMap, h1, weight_one]
    simp only [↓reduceIte]
    have := hcounit i j
    change (counit G) (Mx i j) = _ at this
    rw [this]
    simp [Matrix.one_apply]
  have hP00 : P 0 * P 0 = P 0 := by simpa using hPmul 0 0
  have hidem : IsIdempotentElem (P 0).det := by
    rw [IsIdempotentElem, ← Matrix.det_mul, hP00]
  have hdet : (P 0).det = 1 := by
    rcases idempotent_eq_zero_or_one hidem with h | h
    · exfalso
      have h' := congrArg ev h
      have key : ev (P 0).det = ((P 0).map ev).det := RingHom.map_det ev.toRingHom (P 0)
      rw [map_zero, key, hP0, Matrix.det_one] at h'
      exact one_ne_zero h'
    · exact h
  have hunit : IsUnit (P 0) := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one)
  have hP01 : P 0 = 1 :=
    hunit.mul_left_cancel (hP00.trans (mul_one _).symm)
  have hPγ : P γ = 0 := by
    have h := hPmul γ 0
    simp only [hγ, ↓reduceIte, hP01, mul_one] at h
    exact h
  have hle : Submodule.span (CommRingCat.of k)
      (Set.range fun q : Fin N × Fin N => Mx q.1 q.2) ≤ LinearMap.ker (weight p γ) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact congrFun (congrFun (congrArg Matrix.of.symm hPγ) i) j
  exact hle (hspan (Finset.mem_coe.mpr (Finset.mem_singleton_self b)))


end Langlands.GroupScheme.CentralSurjectionImage
