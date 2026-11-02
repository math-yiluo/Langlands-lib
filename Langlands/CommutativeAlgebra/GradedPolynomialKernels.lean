import Langlands.CommutativeAlgebra.PolynomialResidueKernels
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Graded polynomial vectors and finite residue generators -/

universe u v

namespace Langlands.CommutativeAlgebra

section Components

variable {R : Type u} [CommRing R] {σ : Type v} {n : ℕ}

/-- An actual polynomial-vector submodule closed under every degree projection. -/
def PolynomialVectorGraded
    (K : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R)) : Prop :=
  ∀ d x, x ∈ K → homogeneousPolynomialVectorComponent n d x ∈ K

theorem homogeneousPolynomialVectorComponent_of_mem {d e : ℕ}
    {x : Fin n → MvPolynomial σ R} (hx : x ∈ homogeneousPolynomialVectors R σ n e) :
    homogeneousPolynomialVectorComponent n d x = if d = e then x else 0 := by
  classical
  by_cases h : d = e
  · subst d
    simpa using homogeneousPolynomialVectorComponent_eq_self n e x hx
  · simp only [h, ↓reduceIte]
    funext i
    simpa [homogeneousPolynomialVectorComponent_apply, h] using
      (MvPolynomial.homogeneousComponent_of_mem (m := d) (hx i trivial))

theorem homogeneousPolynomialVectors_smul_mem {d e : ℕ}
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous d)
    {x : Fin n → MvPolynomial σ R} (hx : x ∈ homogeneousPolynomialVectors R σ n e) :
    p • x ∈ homogeneousPolynomialVectors R σ n (d + e) := by
  intro i _
  exact hp.mul (hx i trivial)

theorem sum_homogeneousPolynomialVectorComponent (x : Fin n → MvPolynomial σ R) :
    ∃ D : ℕ, (∑ d ∈ Finset.range (D + 1),
      homogeneousPolynomialVectorComponent n d x) = x := by
  classical
  let D := Finset.univ.sup (fun i : Fin n => (x i).totalDegree)
  refine ⟨D, ?_⟩
  funext i
  simp only [Finset.sum_apply, homogeneousPolynomialVectorComponent_apply]
  have hi : (x i).totalDegree ≤ D :=
    Finset.le_sup (f := fun i : Fin n => (x i).totalDegree) (Finset.mem_univ i)
  calc
    ∑ d ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent d (x i) =
        ∑ d ∈ Finset.range ((x i).totalDegree + 1),
          MvPolynomial.homogeneousComponent d (x i) := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (Nat.add_le_add_right hi 1)
      · intro d _ hd
        apply MvPolynomial.homogeneousComponent_eq_zero
        simp only [Finset.mem_range, not_lt] at hd
        omega
    _ = x i := MvPolynomial.sum_homogeneousComponent _

theorem homogeneousPolynomialVectorComponent_smul_mem
    (L : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
    {e : ℕ} {x : Fin n → MvPolynomial σ R}
    (hx : x ∈ homogeneousPolynomialVectors R σ n e) (hL : x ∈ L)
    (p : MvPolynomial σ R) (d : ℕ) :
    homogeneousPolynomialVectorComponent n d (p • x) ∈ L := by
  classical
  rw [← MvPolynomial.sum_homogeneousComponent p, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [homogeneousPolynomialVectorComponent_of_mem
    (homogeneousPolynomialVectors_smul_mem
      (MvPolynomial.homogeneousComponent_isHomogeneous j p) hx)]
  split_ifs
  · exact L.smul_mem _ hL
  · exact L.zero_mem

theorem polynomialVectorGraded_span
    (s : Set (Fin n → MvPolynomial σ R))
    (hs : ∀ x ∈ s, ∃ d, x ∈ homogeneousPolynomialVectors R σ n d) :
    PolynomialVectorGraded (Submodule.span (MvPolynomial σ R) s) := by
  intro d x hx
  have h : ∀ p : MvPolynomial σ R, ∀ d,
      homogeneousPolynomialVectorComponent n d (p • x) ∈
        Submodule.span (MvPolynomial σ R) s := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he⟩ := hs x hx
      intro p d
      exact homogeneousPolynomialVectorComponent_smul_mem _ he
        (Submodule.subset_span hx) p d
    | zero =>
      intro p d
      simp only [smul_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      intro p d
      rw [smul_add, map_add]
      exact Submodule.add_mem _ (ihx p d) (ihy p d)
    | smul a x hx ih =>
      intro p d
      rw [smul_smul]
      exact ih (p * a) d
  simpa using h 1 d

theorem polynomialVectorGraded_span_homogeneous
    (K : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
    (hK : PolynomialVectorGraded K) :
    Submodule.span (MvPolynomial σ R)
      {x | x ∈ K ∧ ∃ d, x ∈ homogeneousPolynomialVectors R σ n d} = K := by
  apply le_antisymm
  · apply Submodule.span_le.2
    exact fun _ hx => hx.1
  · intro x hx
    obtain ⟨D, hD⟩ := sum_homogeneousPolynomialVectorComponent x
    rw [← hD]
    apply Submodule.sum_mem
    intro d _
    apply Submodule.subset_span
    exact ⟨hK d x hx, d, homogeneousPolynomialVectorComponent_mem n d x⟩

end Components

section Reduction

variable {R : Type u} [CommRing R] {σ : Type v}

/-- Polynomial-vector coefficient reduction with its polynomial semilinearity. -/
noncomputable def polynomialVectorQuotientMap (I : Ideal R) (n : ℕ) :
    (Fin n → MvPolynomial σ R) →ₛₗ[MvPolynomial.map (σ := σ) (Ideal.Quotient.mk I)]
      (Fin n → MvPolynomial σ (R ⧸ I)) where
  toFun := polynomialVectorReduction I n
  map_add' := map_add _
  map_smul' p x := by
    funext i
    exact map_mul (MvPolynomial.map (Ideal.Quotient.mk I)) p (x i)

@[simp]
theorem polynomialVectorQuotientMap_apply (I : Ideal R) (n : ℕ)
    (x : Fin n → MvPolynomial σ R) :
    polynomialVectorQuotientMap I n x = polynomialVectorReduction I n x := rfl

theorem polynomialVectorReduction_component (I : Ideal R) (n d : ℕ)
    (x : Fin n → MvPolynomial σ R) :
    polynomialVectorReduction I n (homogeneousPolynomialVectorComponent n d x) =
      homogeneousPolynomialVectorComponent n d (polynomialVectorReduction I n x) := by
  classical
  funext i
  ext a
  simp only [polynomialVectorReduction_apply, homogeneousPolynomialVectorComponent_apply,
    MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp

end Reduction

section FiniteExtraction

variable {A : Type*} [Semiring A] {V : Type*} {W : Type*}
variable [AddCommMonoid W] [Module A W] [IsNoetherian A W]

private theorem exists_finset_span_image (g : V → W) (s : Set V) :
    ∃ t : Finset V, (↑t : Set V) ⊆ s ∧
      Submodule.span A (g '' (↑t : Set V)) = Submodule.span A (g '' s) := by
  classical
  obtain ⟨t, ht, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (g '' s)).1
      (IsNoetherian.noetherian (R := A) (Submodule.span A (g '' s)))
  have hpre : ∀ y : (t : Set W), ∃ x : V, x ∈ s ∧ g x = (y : W) :=
    fun y => ht y.property
  choose lift hlift hglift using hpre
  let t' : Finset V := t.attach.image lift
  have hsub : (↑t' : Set V) ⊆ s := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx
    exact hlift y
  refine ⟨t', hsub, le_antisymm (Submodule.span_mono (Set.image_mono hsub)) ?_⟩
  rw [hspan]
  apply Submodule.span_mono
  intro y hy
  refine ⟨lift ⟨y, hy⟩, ?_, hglift ⟨y, hy⟩⟩
  exact Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩

end FiniteExtraction

section ValuationKernel

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {σ : Type v} [Finite σ] {n m : ℕ}

/-- Graded containment of polynomial kernels can be checked after coefficient
reduction by an ideal in the Jacobson radical. -/
theorem polynomialKernel_le_of_reduction
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (Fin m → MvPolynomial σ R))
    (hK : PolynomialVectorGraded (LinearMap.ker f))
    (L : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
    (hL : L ≤ LinearMap.ker f) (hLg : PolynomialVectorGraded L)
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (hred : ∀ x ∈ LinearMap.ker f, ∃ y ∈ L,
      polynomialVectorReduction I n y = polynomialVectorReduction I n x) :
    LinearMap.ker f ≤ L := by
  have hpiece (d : ℕ) (x : Fin n → MvPolynomial σ R)
      (hx : x ∈ LinearMap.ker f) (hxd : x ∈ homogeneousPolynomialVectors R σ n d) :
      x ∈ L := by
    let H := homogeneousPolynomialVectors R σ n d
    let fd := (f.restrictScalars R).comp H.subtype
    let gd := homogeneousPolynomialVectorReduction (σ := σ) I n d
    let Ld := (L.restrictScalars R).comap H.subtype
    have := homogeneousPolynomialVectors_finite (R := R) (σ := σ) n d
    have hLd : Ld ≤ LinearMap.ker fd := by
      intro z hz
      exact hL hz
    have himage : (LinearMap.ker fd).map gd ≤ Ld.map gd := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hzy⟩ := hred z.val hz
      let yd : H := ⟨homogeneousPolynomialVectorComponent n d y,
        homogeneousPolynomialVectorComponent_mem n d y⟩
      refine ⟨yd, hLg d y hy, ?_⟩
      change polynomialVectorReduction I n
        (homogeneousPolynomialVectorComponent n d y) = polynomialVectorReduction I n z.val
      rw [polynomialVectorReduction_component, hzy,
        ← polynomialVectorReduction_component,
        homogeneousPolynomialVectorComponent_eq_self n d z.val z.property]
    have hle := valuationKernel_le_of_reduction_image_le fd gd I hI
      (homogeneousPolynomialVectorReduction_ker I n d) Ld hLd himage
    exact hle (show (⟨x, hxd⟩ : H) ∈ LinearMap.ker fd from hx)
  intro x hx
  obtain ⟨D, hD⟩ := sum_homogeneousPolynomialVectorComponent x
  rw [← hD]
  apply Submodule.sum_mem
  intro d _
  exact hpiece d _ (hK d x hx) (homogeneousPolynomialVectorComponent_mem n d x)

/-- A polynomial kernel closed under degree projections is finitely generated
 over a polynomial ring in finitely many variables over any valuation domain. -/
theorem polynomialKernel_fg_of_graded
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (Fin m → MvPolynomial σ R))
    (hK : PolynomialVectorGraded (LinearMap.ker f)) : (LinearMap.ker f).FG := by
  classical
  let I := IsLocalRing.maximalIdeal R
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let g := polynomialVectorQuotientMap (σ := σ) I n
  let S : Set (Fin n → MvPolynomial σ R) :=
    {x | x ∈ LinearMap.ker f ∧ ∃ d, x ∈ homogeneousPolynomialVectors R σ n d}
  have hS : Submodule.span (MvPolynomial σ R) S = LinearMap.ker f :=
    polynomialVectorGraded_span_homogeneous _ hK
  obtain ⟨t, htS, htspan⟩ := exists_finset_span_image
    (A := MvPolynomial σ (R ⧸ I)) g S
  let L := Submodule.span (MvPolynomial σ R) (↑t : Set (Fin n → MvPolynomial σ R))
  have hL : L ≤ LinearMap.ker f := by
    apply Submodule.span_le.2
    exact fun x hx => (htS hx).1
  have hLg : PolynomialVectorGraded L :=
    polynomialVectorGraded_span _ (fun x hx => (htS hx).2)
  have : RingHomSurjective (MvPolynomial.map (σ := σ) (Ideal.Quotient.mk I)) :=
    ⟨MvPolynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective⟩
  have hKL : LinearMap.ker f ≤ L := by
    apply polynomialKernel_le_of_reduction f hK L hL hLg I
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro x hx
    have hxspan : g x ∈ Submodule.span (MvPolynomial σ (R ⧸ I)) (g '' S) := by
      apply Submodule.image_span_subset_span g S
      exact ⟨x, hS.symm ▸ hx, rfl⟩
    rw [← htspan, Submodule.span_image g] at hxspan
    obtain ⟨y, hy, hgy⟩ := hxspan
    exact ⟨y, hy, hgy⟩
  have heq : L = LinearMap.ker f := le_antisymm hL hKL
  exact heq ▸ Submodule.fg_span t.finite_toSet

end ValuationKernel

end Langlands.CommutativeAlgebra
