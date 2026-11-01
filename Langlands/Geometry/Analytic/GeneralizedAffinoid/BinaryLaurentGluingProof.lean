import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentGluingStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusNormalFormProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusOverlapProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusPrincipalRelationsProof

/-! # Scalar descent for the actual relative binary Laurent diagram -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

omit [CompleteSpace K] in
private theorem one_variable_ext
    {s t : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A}
    (h : ∀ m : ℕ, MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
      (series (PositivePolyradius.unit (Fin 1)) A s) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
        (series (PositivePolyradius.unit (Fin 1)) A t)) : s = t := by
  apply ext_coeff
  intro d
  have hd : Finsupp.single (0 : Fin 1) (d 0) = d := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  rw [← hd]
  exact h (d 0)

omit [CompleteSpace K] in
private theorem one_variable_coeff_constant (a : A) (m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
      (series (PositivePolyradius.unit (Fin 1)) A
        (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a)) =
      if m = 0 then a else 0 := by
  change MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
    (MvPowerSeries.C a) = if m = 0 then a else 0
  simp [MvPowerSeries.coeff_C]

/-- Equal positive and negative series in the actual annulus are a common constant. -/
private theorem equal_positive_negative_are_constants
    (s t : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A)
    (hst : RelativeUnitAnnulus.positive K A s = RelativeUnitAnnulus.negative K A t) :
    ∃ a : A, s = constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a ∧
      t = constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a := by
  obtain ⟨e, _, _, _, _, hpos, hneg⟩ := RelativeUnitAnnulus.normal_form K A
  have hzero :
      MvPowerSeries.coeff 0 (series (PositivePolyradius.unit (Fin 1)) A s) =
        MvPowerSeries.coeff 0 (series (PositivePolyradius.unit (Fin 1)) A t) := by
    simpa [hpos, hneg] using congrArg (fun z => e z (0 : ℤ)) hst
  have hs : ∀ m : ℕ, 0 < m →
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
        (series (PositivePolyradius.unit (Fin 1)) A s) = 0 := by
    intro m hm
    simpa [hpos, hneg, Nat.ne_of_gt hm] using congrArg (fun z => e z (m : ℤ)) hst
  have ht : ∀ m : ℕ, 0 < m →
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
        (series (PositivePolyradius.unit (Fin 1)) A t) = 0 := by
    intro m hm
    have hz := congrArg (fun z => e z (-(m : ℤ))) hst
    have hz' : 0 = MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) m)
        (series (PositivePolyradius.unit (Fin 1)) A t) := by
      simpa [hpos, hneg, Nat.ne_of_gt hm] using hz
    exact hz'.symm
  refine ⟨MvPowerSeries.coeff 0 (series (PositivePolyradius.unit (Fin 1)) A s), ?_, ?_⟩
  · apply one_variable_ext K A
    intro m
    rw [one_variable_coeff_constant]
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm, hs m (Nat.pos_of_ne_zero hm)]
  · apply one_variable_ext K A
    intro m
    rw [one_variable_coeff_constant]
    by_cases hm : m = 0
    · simpa [hm] using hzero.symm
    · simp [hm, ht m (Nat.pos_of_ne_zero hm)]

/-- Compatible sections of the actual upper and lower Laurent quotients descend uniquely. -/
theorem gluing : GluingStatement.{u} := by
  intro K _ _ _ hK P f sUpper sLower hcompat
  let A := ofStrict K P
  let S := GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A
  let C := constantAlgHom (PositivePolyradius.unit (Fin 1)) K A
  let T := X (PositivePolyradius.unit (Fin 1)) A 0
  let Jpos : Ideal S := Ideal.span ({T - C f} : Set S)
  let Jneg : Ideal S := Ideal.span ({C f * T - 1} : Set S)
  let J : Ideal (RelativeUnitAnnulus.Algebra K A) :=
    Ideal.span {RelativeUnitAnnulus.annulusX K A - RelativeUnitAnnulus.baseMap K A f}
  let Qpos := RelativeRationalPresentation.quotientMap K A
    (PositivePolyradius.unit (Fin 1)) 1 (fun _ => f)
  let Qneg := RelativeRationalPresentation.quotientMap K A
    (PositivePolyradius.unit (Fin 1)) f (fun _ => 1)
  obtain ⟨hJpos, hJneg, hJ, β, hβ⟩ := RelativeUnitAnnulus.principal_relations K hK P f
  have hposzero : ∀ s : S, Qpos s = 0 ↔ s ∈ Jpos := by
    intro s
    rw [RelativeRationalPresentation.quotientMap_eq_zero_iff, upperEquations_eq,
      Ideal.closure_eq_of_isClosed _ hJpos]
  have hnegzero : ∀ s : S, Qneg s = 0 ↔ s ∈ Jneg := by
    intro s
    rw [RelativeRationalPresentation.quotientMap_eq_zero_iff, lowerEquations_eq,
      Ideal.closure_eq_of_isClosed _ hJneg]
  have hbaseinj : Function.Injective
      (fun a : A => (upperBase K A f a, lowerBase K A f a)) := by
    intro a b hab
    have ha : Qpos (C (a - b)) = 0 := by
      change upperBase K A f (a - b) = 0
      rw [map_sub, sub_eq_zero]
      exact congrArg Prod.fst hab
    have hb : Qneg (C (a - b)) = 0 := by
      change lowerBase K A f (a - b) = 0
      rw [map_sub, sub_eq_zero]
      exact congrArg Prod.snd hab
    let p : Jpos := ⟨C (a - b), (hposzero _).mp ha⟩
    let q : Jneg := ⟨C (a - b), (hnegzero _).mp hb⟩
    have hβzero : β (p, q) = 0 := by
      apply Subtype.ext
      rw [hβ]
      change RelativeUnitAnnulus.positive K A (C (a - b)) -
        RelativeUnitAnnulus.negative K A (C (a - b)) = 0
      dsimp only [C]
      rw [RelativeUnitAnnulus.positive_constant, RelativeUnitAnnulus.negative_constant,
        sub_self]
    have hpq : (p, q) = 0 := β.injective (hβzero.trans β.map_zero.symm)
    have hC : C (a - b) = 0 := congrArg (fun z => (z.1 : S)) hpq
    have habzero : a - b = 0 :=
      (isometry_constantAlgHom (PositivePolyradius.unit (Fin 1)) K A).injective
        (hC.trans C.map_zero.symm)
    exact sub_eq_zero.mp habzero
  obtain ⟨s, hs⟩ := RelativeRationalPresentation.quotientMap_surjective K A
    (PositivePolyradius.unit (Fin 1)) 1 (fun _ => f) sUpper
  obtain ⟨t, ht⟩ := RelativeRationalPresentation.quotientMap_surjective K A
    (PositivePolyradius.unit (Fin 1)) f (fun _ => 1) sLower
  let d := RelativeUnitAnnulus.positive K A s - RelativeUnitAnnulus.negative K A t
  have hdker : d ∈ RingHom.ker (RelativeUnitAnnulus.toOverlap K A f).toAlgHom := by
    change RelativeUnitAnnulus.toOverlap K A f d = 0
    dsimp [d]
    rw [map_sub, RelativeUnitAnnulus.toOverlap_positive,
      RelativeUnitAnnulus.toOverlap_negative, hs, ht, hcompat, sub_self]
  have hd : d ∈ J := by
    rw [(RelativeUnitAnnulus.overlap_presentation K A f).2.1, Ideal.closure_eq_of_isClosed _ hJ] at hdker
    exact hdker
  obtain ⟨⟨p, q⟩, hpq⟩ := β.surjective ⟨d, hd⟩
  have hdiff :
      RelativeUnitAnnulus.positive K A (p : S) -
        RelativeUnitAnnulus.negative K A (q : S) = d := by
    rw [← hβ p q]
    exact congrArg Subtype.val hpq
  have hequal : RelativeUnitAnnulus.positive K A (s - (p : S)) =
      RelativeUnitAnnulus.negative K A (t - (q : S)) := by
    rw [map_sub, map_sub]
    dsimp [d] at hdiff
    linear_combination -hdiff
  obtain ⟨a, ha, hb⟩ :=
    equal_positive_negative_are_constants K A _ _ hequal
  have hpa : upperBase K A f a = sUpper := by
    rw [upperBase_apply, ← ha, map_sub, (hposzero _).mpr p.property, sub_zero]
    exact hs
  have hqa : lowerBase K A f a = sLower := by
    rw [lowerBase_apply, ← hb, map_sub, (hnegzero _).mpr q.property, sub_zero]
    exact ht
  refine ⟨a, ⟨hpa, hqa⟩, ?_⟩
  intro b hb
  apply hbaseinj
  exact Prod.ext (hb.1.trans hpa.symm) (hb.2.trans hqa.symm)

end Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent
