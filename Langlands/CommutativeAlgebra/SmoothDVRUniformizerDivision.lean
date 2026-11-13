import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Division by a uniformizer in smooth algebras over a discrete valuation ring -/

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision

/-- In a smooth algebra over a discrete valuation ring, an element lying in every prime that
contains a uniformizer is divisible by the uniformizer: the special fibre is reduced. -/
theorem dvd_of_forall_mem_prime {R B : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    {π : R} (hπ : Irreducible π) (h : B)
    (hh : ∀ P : Ideal B, P.IsPrime → algebraMap R B π ∈ P → h ∈ P) :
    algebraMap R B π ∣ h := by
  let I : Ideal R := Ideal.span {π}
  have hI : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have hred : IsReduced ((R ⧸ I) ⊗[R] B) :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain (R ⧸ I) _
  let J : Ideal B := I.map (algebraMap R B)
  let e1 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  let e2 := Algebra.TensorProduct.comm R B (R ⧸ I)
  let φ : (B ⧸ J) →+* (R ⧸ I) ⊗[R] B :=
    e2.toRingEquiv.toRingHom.comp e1.toRingEquiv.toRingHom
  have hφ : Function.Injective φ := e2.injective.comp e1.injective
  have hredJ : IsReduced (B ⧸ J) := isReduced_of_injective φ hφ
  have hJ : J = Ideal.span {algebraMap R B π} := by
    simp only [J, I, Ideal.map_span, Set.image_singleton]
  have hrad : h ∈ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.mpr fun P hP ↦ ?_
    refine hh P hP.2 (hP.1 ?_)
    rw [hJ]
    exact Ideal.subset_span rfl
  obtain ⟨n, hn⟩ := hrad
  have hnil : IsNilpotent (Ideal.Quotient.mk J h) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  have hzero : Ideal.Quotient.mk J h = 0 := hnil.eq_zero
  have hmem : h ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hJ] at hmem
  exact Ideal.mem_span_singleton.mp hmem

end Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision
