import Langlands.Representation.Parabolic.IrreducibleInducingSubquotientProof
import Langlands.Representation.Filtration.CoarseJacquetFactorization
import Langlands.Representation.Tensor.SmoothSubquotients

/-! Factorized inducing constituents retaining the whole Jacquet quotient. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Parabolic

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Factor a lifted inducing constituent without losing its quotient,
factorwise occurrences, or the actual embedding of the original object. -/
theorem exists_factorized_inducing_subquotient :
    letI := T.topology
    ∀ {n : ℕ}, 0 < n → ∀ (B : BlockShape n)
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
      (Y : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
        (GeneralLinear (B.size i) F.Carrier)),
      π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
      SmoothRep.IsSubrepresentation π ((T.normalizedProductInductionFunctor B).obj Y) →
      ∃ X : ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
          (GeneralLinear (B.size i) F.Carrier),
        (∀ i, (X i).IsIrreducible) ∧
        (∀ i, (X i).IsAdmissible) ∧
        (∀ i, SmoothRep.IsSubquotient (X i) (Y i)) ∧
        SmoothRep.IsQuotient (FiniteTensor.externalSmoothObject X)
          ((T.normalizedJacquetFunctor B).obj π) ∧
        SmoothRep.IsSubrepresentation π ((T.normalizedProductInductionFunctor B).obj X) := by
  let := T.topology
  intro n hn B π Y hπi hπa hπf ⟨j, hj⟩
  let := T.leviTopologicalGroup B
  let := hπi
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      π.representation.asModule
  have hj0 : SmoothRep.hom j ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : π)
    apply hv
    apply hj
    rw [h]
    rfl
  let σ : SmoothRep.{0,uF,max uF uV} ℂ (B.Levi F.Carrier) :=
    FiniteTensor.externalSmoothObject Y
  have hfin : ((T.normalizedJacquetFunctor B).obj π).HasFiniteLength :=
    coarseJacquet_hasFiniteLength T B hπa hπf
  have hj0' : ∃ f : π.representation.IntertwiningMap
      (T.normalizedParabolicInduced B σ.representation), f ≠ 0 :=
    ⟨SmoothRep.hom j, hj0⟩
  obtain ⟨ρ, hρi, hρq, hρY, hρemb⟩ :=
    irreducibleInducingSubquotient.{uF,uV} F T n B π σ hπi hfin hj0'
  obtain ⟨k, hk⟩ := hρemb
  have hcofinal : ∀ H : OpenSubgroup (B.Levi F.Carrier),
      ∃ K : OpenSubgroup (B.Levi F.Carrier),
        IsCompact (K : Set (B.Levi F.Carrier)) ∧ K ≤ H := by
    intro H
    obtain ⟨K, hK, hKH⟩ := T.leviCompactOpen B H
      (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, fun x hx => hKH hx⟩
  have hρa : ρ.IsAdmissible :=
    SmoothRep.isAdmissible_of_subquotient_of_compactOpenCofinal hcofinal
      (A := (T.normalizedJacquetFunctor B).obj π) (D := ρ)
      (FiniteLengthAssembly.isAdmissible_normalizedJacquet T B π.representation hπa)
      hρq.isSubquotient
  obtain ⟨X, hXi, hXa, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization p F T n hn B ρ hρi hρa
  let E : ρ ≅ FiniteTensor.externalSmoothObject X := SmoothRep.mkIso e
  have hXY : SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject X)
      (FiniteTensor.externalSmoothObject Y) :=
    SmoothRep.IsSubquotient.of_iso_left E hρY
  obtain ⟨q, hq⟩ := hρq
  let I : (T.normalizedParabolicInductionFunctor B).obj ρ ≅
      (T.normalizedProductInductionFunctor B).obj X :=
    (T.normalizedParabolicInductionFunctor B).mapIso E
  refine ⟨X, hXi, hXa,
    FiniteTensor.isSubquotient_smooth_factor_of_external hXi hXY,
    ⟨q ≫ E.hom, ?_⟩, ⟨k ≫ I.hom, ?_⟩⟩
  · exact (SmoothRep.hom_hom_surjective E).comp hq
  · exact (SmoothRep.hom_hom_injective I).comp hk

end Langlands.Parabolic
