import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Langlands.GroupScheme.Derived.CentralIntersection.LinearAlgebra

/-! # Spectral decomposition of a finite commutative algebra over an algebraically closed field -/

noncomputable section

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

section Decomposition

variable {K B : Type*} [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B] [Module.Finite K B]

variable (K B) in
/-- A finite commutative algebra over an algebraically closed field has a complete family of
nonzero orthogonal idempotents `e i` and algebra maps `χ i` to the field such that every element
`x` acts on `e i` by `χ i x` up to a nilpotent. -/
theorem exists_spectralDecomposition :
    ∃ (r : ℕ) (e : Fin r → B) (χ : Fin r → (B →ₐ[K] K)),
      CompleteOrthogonalIdempotents e ∧ (∀ i, e i ≠ 0) ∧
        ∀ i x, IsNilpotent ((x - algebraMap K B (χ i x)) * e i) := by
  classical
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  let ι := MaximalSpectrum B
  have : Fintype ι := Fintype.ofFinite ι
  let φ := IsArtinianRing.quotNilradicalEquivPi B
  let v : ι → B ⧸ nilradical B := fun m => φ.symm (Pi.single m 1)
  have hv : CompleteOrthogonalIdempotents v :=
    (CompleteOrthogonalIdempotents.single (fun m : ι => B ⧸ m.asIdeal)).map
      φ.symm.toRingEquiv.toRingHom
  obtain ⟨e', he', hfe⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (Ideal.Quotient.mk (nilradical B))
    (fun x hx => by
      rw [Ideal.mk_ker] at hx
      exact mem_nilradical.1 hx)
    hv (fun m => Ideal.Quotient.mk_surjective _)
  have hfe' : ∀ m, Ideal.Quotient.mk (nilradical B) (e' m) = v m := fun m => congrFun hfe m
  have hbij : ∀ m : ι, Function.Bijective (algebraMap K (B ⧸ m.asIdeal)) := by
    intro m
    have := m.isMaximal
    have : Module.Finite K (B ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let res : ∀ m : ι, K ≃ₐ[K] B ⧸ m.asIdeal := fun m =>
    AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ m.asIdeal)) (hbij m)
  let χ' : ι → (B →ₐ[K] K) := fun m =>
    (res m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m.asIdeal)
  have hχ' : ∀ m x, algebraMap K (B ⧸ m.asIdeal) (χ' m x) = Ideal.Quotient.mk m.asIdeal x := by
    intro m x
    change res m ((res m).symm _) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  have hφ : ∀ (x : B) (m : ι),
      φ (Ideal.Quotient.mk (nilradical B) x) m = Ideal.Quotient.mk m.asIdeal x := fun x m => rfl
  have hne : ∀ m, e' m ≠ 0 := by
    intro m h
    have h1 : v m = 0 := by rw [← hfe' m, h, map_zero]
    have h2 : φ (v m) m = (1 : B ⧸ m.asIdeal) := by
      change φ (φ.symm _) m = _
      rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same]
    rw [h1, map_zero] at h2
    have := m.isMaximal
    exact zero_ne_one (Pi.zero_apply (M := fun m : ι => B ⧸ m.asIdeal) m ▸ h2)
  have hnil : ∀ m x, IsNilpotent ((x - algebraMap K B (χ' m x)) * e' m) := by
    intro m x
    rw [← mem_nilradical, ← Ideal.Quotient.eq_zero_iff_mem]
    apply φ.injective
    rw [map_zero]
    funext m'
    rw [map_mul, hfe', map_mul]
    change φ _ m' * φ (φ.symm _) m' = 0
    rw [AlgEquiv.apply_symm_apply, hφ]
    by_cases hm : m' = m
    · subst hm
      rw [Pi.single_eq_same, mul_one, map_sub, ← hχ', Ideal.Quotient.mk_algebraMap, sub_self]
    · rw [Pi.single_eq_of_ne hm, mul_zero]
  let eqv := Fintype.equivFin ι
  refine ⟨Fintype.card ι, e' ∘ eqv.symm, χ' ∘ eqv.symm,
    (CompleteOrthogonalIdempotents.equiv eqv.symm).2 he', fun i => hne _, fun i x => hnil _ _⟩

end Decomposition

/-- Spectral data on a commutative algebra: a complete family of nonzero orthogonal idempotents
`e i` and algebra maps `χ i` to the field such that `x - χ i x` is nilpotent on `e i`. -/
structure SpectralData (K B : Type*) [Field K] [CommRing B] [Algebra K B] where
  /-- The number of blocks. -/
  r : ℕ
  /-- The block idempotents. -/
  e : Fin r → B
  /-- The block eigenvalue maps. -/
  χ : Fin r → (B →ₐ[K] K)
  complete : CompleteOrthogonalIdempotents e
  ne_zero : ∀ i, e i ≠ 0
  isNilpotent : ∀ i x, IsNilpotent ((x - algebraMap K B (χ i x)) * e i)

theorem nonempty_spectralData (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] : Nonempty (SpectralData K B) := by
  obtain ⟨r, e, χ, h1, h2, h3⟩ := exists_spectralDecomposition K B
  exact ⟨⟨r, e, χ, h1, h2, h3⟩⟩

/-- An element `a e + b (1 - e)` with `e` idempotent and `a, b` nonzero is a unit. -/
theorem isUnit_idempotent_combination {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    {e : B} (he : IsIdempotentElem e) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsUnit (algebraMap K B a * e + algebraMap K B b * (1 - e)) := by
  refine IsUnit.of_mul_eq_one (algebraMap K B a⁻¹ * e + algebraMap K B b⁻¹ * (1 - e)) ?_
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  have h3 : algebraMap K B a * algebraMap K B a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h4 : algebraMap K B b * algebraMap K B b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  calc (algebraMap K B a * e + algebraMap K B b * (1 - e)) *
        (algebraMap K B a⁻¹ * e + algebraMap K B b⁻¹ * (1 - e))
      = (algebraMap K B a * algebraMap K B a⁻¹) * (e * e) +
          (algebraMap K B b * algebraMap K B b⁻¹) * ((1 - e) * (1 - e)) +
          (algebraMap K B a * algebraMap K B b⁻¹ + algebraMap K B b * algebraMap K B a⁻¹) *
            (e * (1 - e)) := by ring
    _ = 1 := by rw [h3, h4, he.eq, h2, h1]; ring

namespace SpectralData

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B] (D : SpectralData K B)

theorem e_mul_self (i : Fin D.r) : D.e i * D.e i = D.e i := (D.complete.idem i).eq

theorem e_mul_e_of_ne {i j : Fin D.r} (h : i ≠ j) : D.e i * D.e j = 0 := D.complete.ortho h

theorem sum_e : ∑ i, D.e i = 1 := D.complete.complete

/-- The element acting by the scalar `t i` on the block `e i`. -/
def diag (t : Fin D.r → K) : B := ∑ i, algebraMap K B (t i) * D.e i

theorem diag_def (t : Fin D.r → K) : D.diag t = ∑ i, algebraMap K B (t i) * D.e i := rfl

theorem diag_mul_e (t : Fin D.r → K) (i : Fin D.r) :
    D.diag t * D.e i = algebraMap K B (t i) * D.e i := by
  rw [diag, Finset.sum_mul, Finset.sum_eq_single i]
  · rw [mul_assoc, e_mul_self]
  · intro j _ hji
    rw [mul_assoc, D.e_mul_e_of_ne hji, mul_zero]
  · simp

theorem diag_mul (t t' : Fin D.r → K) : D.diag t * D.diag t' = D.diag (t * t') := by
  rw [D.diag_def t', Finset.mul_sum, D.diag_def (t * t')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, diag_mul_e, ← mul_assoc, ← map_mul, Pi.mul_apply, mul_comm (t' i)]

theorem diag_const (c : K) : D.diag (fun _ => c) = algebraMap K B c := by
  rw [diag, ← Finset.mul_sum, sum_e, mul_one]

theorem diag_one : D.diag 1 = 1 := by
  have h := D.diag_const (1 : K)
  rw [map_one] at h
  exact h

theorem isUnit_diag {t : Fin D.r → K} (ht : ∀ i, t i ≠ 0) : IsUnit (D.diag t) := by
  refine IsUnit.of_mul_eq_one (D.diag t⁻¹) ?_
  rw [diag_mul, ← D.diag_one]
  congr 1
  funext i
  simp [ht i]

/-- The semisimple part `∑ χ i x • e i` of an element. -/
def semisimplePart (x : B) : B := D.diag fun i => D.χ i x

theorem sub_semisimplePart (x : B) :
    x - D.semisimplePart x = ∑ i, (x - algebraMap K B (D.χ i x)) * D.e i := by
  simp only [semisimplePart, diag, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_e,
    mul_one]

theorem isNilpotent_sub_semisimplePart (x : B) : IsNilpotent (x - D.semisimplePart x) := by
  rw [sub_semisimplePart]
  exact isNilpotent_sum fun i _ => D.isNilpotent i x

theorem isUnit_sub_algebraMap {x : B} {μ : K} (h : ∀ i, D.χ i x ≠ μ) :
    IsUnit (x - algebraMap K B μ) := by
  have h1 : x - algebraMap K B μ =
      D.diag (fun i => D.χ i x - μ) + (x - D.semisimplePart x) := by
    have : D.diag (fun i => D.χ i x - μ) = D.semisimplePart x - algebraMap K B μ := by
      rw [← diag_const, semisimplePart, diag, diag, diag, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, sub_mul]
    rw [this]
    ring
  rw [h1]
  exact (D.isNilpotent_sub_semisimplePart x).isUnit_add_left_of_commute
    (D.isUnit_diag fun i => sub_ne_zero.2 (h i)) (Commute.all _ _)

theorem χ_ne_zero_of_isUnit {x : B} (hx : IsUnit x) (i : Fin D.r) : D.χ i x ≠ 0 :=
  (hx.map (D.χ i)).ne_zero

/-- The block element `x e i + (1 - e i)`. -/
def block (x : B) (i : Fin D.r) : B := x * D.e i + (1 - D.e i)

theorem block_sub_mul_e (x : B) (i : Fin D.r) :
    (D.block x i - algebraMap K B (D.χ i x)) * D.e i =
      (x - algebraMap K B (D.χ i x)) * D.e i := by
  have h : (1 - D.e i) * D.e i = 0 := by rw [sub_mul, one_mul, e_mul_self, sub_self]
  rw [block, sub_mul, add_mul, h, add_zero, mul_assoc, e_mul_self, ← sub_mul]

theorem isUnit_block_sub {x : B} {i : Fin D.r} {μ : K} (h1 : D.χ i x ≠ μ) (h2 : (1 : K) ≠ μ) :
    IsUnit (D.block x i - algebraMap K B μ) := by
  have he := D.complete.idem i
  have hdecomp : D.block x i - algebraMap K B μ =
      (algebraMap K B (D.χ i x - μ) * D.e i + algebraMap K B (1 - μ) * (1 - D.e i)) +
        (x - algebraMap K B (D.χ i x)) * D.e i := by
    simp only [block, map_sub, map_one]
    ring
  rw [hdecomp]
  exact (D.isNilpotent i x).isUnit_add_left_of_commute
    (isUnit_idempotent_combination he (sub_ne_zero.2 h1) (sub_ne_zero.2 h2)) (Commute.all _ _)

theorem χ_eq_one_of_isNilpotent [IsReduced K] {x : B} (hx : IsNilpotent (x - 1)) (i : Fin D.r) :
    D.χ i x = 1 := by
  have h := hx.map (D.χ i)
  rw [map_sub, map_one] at h
  exact sub_eq_zero.1 h.eq_zero

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
  (ψ : B →ₐ[K] Matrix n n K) (hψ : Function.Injective ψ)

include hψ in
theorem isNilpotent_of_map {x : B} (hx : IsNilpotent (ψ x)) : IsNilpotent x := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, hψ (by rw [map_pow, hk, map_zero])⟩

/-- Every eigenvalue of the image of `x` is one of the block eigenvalues `χ i x`. -/
theorem exists_eq_of_isRoot {x : B} {c : K} (hc : (ψ x).charpoly.IsRoot c) :
    ∃ i, D.χ i x = c := by
  by_contra h
  simp only [not_exists] at h
  have hu := (D.isUnit_sub_algebraMap h).map ψ
  rw [map_sub, AlgHom.commutes] at hu
  have hσ : c ∈ spectrum K (ψ x) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hc
  rw [spectrum.mem_iff] at hσ
  exact hσ (by rw [← neg_sub]; exact hu.neg)

include hψ in
/-- Every block eigenvalue `χ i x` is an eigenvalue of the image of `x`. -/
theorem isRoot_charpoly_χ (x : B) (i : Fin D.r) : (ψ x).charpoly.IsRoot (D.χ i x) := by
  apply Matrix.mem_spectrum_iff_isRoot_charpoly.1
  rw [spectrum.mem_iff]
  intro hu
  have hu' : IsUnit (ψ x - algebraMap K (Matrix n n K) (D.χ i x)) := by
    rw [← neg_sub]; exact hu.neg
  have hcomm : Commute (ψ (D.e i)) (ψ x - algebraMap K (Matrix n n K) (D.χ i x)) := by
    rw [← AlgHom.commutes ψ, ← map_sub]
    exact (Commute.all _ _).map ψ
  have hnil : IsNilpotent ((ψ x - algebraMap K (Matrix n n K) (D.χ i x)) * ψ (D.e i)) := by
    rw [← AlgHom.commutes ψ, ← map_sub, ← map_mul]
    exact (D.isNilpotent i x).map ψ
  have hne : IsNilpotent (ψ (D.e i)) := (hu'.isNilpotent_unit_mul_of_commute_iff hcomm).1 hnil
  apply D.ne_zero i
  apply hψ
  rw [map_zero]
  exact ((D.complete.idem i).map ψ).eq_zero_of_isNilpotent hne

include hψ in
/-- The determinant of the image of a block element `x e i + (1 - e i)` is `χ i x ^ a` with
`1 ≤ a ≤ card n`. -/
theorem det_block [IsAlgClosed K] (x : B) (i : Fin D.r) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ Fintype.card n ∧ (ψ (D.block x i)).det = D.χ i x ^ a := by
  classical
  set c := D.χ i x with hc
  set Y := ψ (D.block x i) with hY
  have hroots : ∀ μ ∈ Y.charpoly.roots, μ = c ∨ μ = 1 := by
    intro μ hμ
    by_contra h
    simp only [not_or] at h
    have hu := (D.isUnit_block_sub (x := x) (i := i) (Ne.symm h.1) (Ne.symm h.2)).map ψ
    rw [map_sub, AlgHom.commutes] at hu
    have hσ : μ ∈ spectrum K Y := Matrix.mem_spectrum_iff_isRoot_charpoly.2
      ((Polynomial.mem_roots Y.charpoly_monic.ne_zero).1 hμ)
    rw [spectrum.mem_iff] at hσ
    exact hσ (by rw [← neg_sub]; exact hu.neg)
  have hdet : Y.det = c ^ Y.charpoly.roots.count c := by
    rw [Matrix.det_eq_prod_roots_charpoly]
    exact Langlands.GroupScheme.CentralIntersection.multiset_prod_eq_pow_count c _ hroots
  by_cases hc1 : c = 1
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
      by_contra hn
      rw [not_nonempty_iff] at hn
      apply D.ne_zero i
      apply hψ
      rw [map_zero]
      ext a
      exact (IsEmpty.false a).elim
    · rw [hdet, hc1, one_pow, one_pow]
  have hcσ : c ∈ spectrum K Y := by
    rw [spectrum.mem_iff]
    intro hu
    have hu' : IsUnit (Y - algebraMap K (Matrix n n K) c) := by
      rw [← neg_sub]; exact hu.neg
    have hcomm : Commute (ψ (D.e i)) (Y - algebraMap K (Matrix n n K) c) := by
      rw [← AlgHom.commutes ψ c, ← map_sub]
      exact (Commute.all _ _).map ψ
    have hnil : IsNilpotent ((Y - algebraMap K (Matrix n n K) c) * ψ (D.e i)) := by
      rw [← AlgHom.commutes ψ c, ← map_sub, ← map_mul, block_sub_mul_e]
      exact (D.isNilpotent i x).map ψ
    have hne : IsNilpotent (ψ (D.e i)) := (hu'.isNilpotent_unit_mul_of_commute_iff hcomm).1 hnil
    apply D.ne_zero i
    apply hψ
    rw [map_zero]
    exact ((D.complete.idem i).map ψ).eq_zero_of_isNilpotent hne
  refine ⟨Y.charpoly.roots.count c, ?_, ?_, hdet⟩
  · apply Multiset.count_pos.2
    exact (Polynomial.mem_roots Y.charpoly_monic.ne_zero).2
      (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hcσ)
  · exact (Multiset.count_le_card _ _).trans
      ((Polynomial.card_roots' _).trans (Matrix.charpoly_natDegree_eq_dim Y).le)

end Matrix

end SpectralData

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
