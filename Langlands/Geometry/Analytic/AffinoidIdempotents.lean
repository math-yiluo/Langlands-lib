import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity

/-! # Units and the Shilov idempotent theorem for presented affinoid algebras -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory Set Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

namespace Domain

/-- A domain with empty locus has a subsingleton algebra: the empty family is
a finite cover, and restrictions along it detect equality. -/
theorem subsingleton_algebra_of_locus_eq_empty (U : Domain K A) (h : U.locus = ∅) :
    Subsingleton U.algebra := by
  refine ⟨fun a b => FiniteCover.algebra_ext_of_restrict_eq
    (U := U) ⟨0, fun i => i.elim0, fun i => i.elim0, fun x hx => ?_⟩
    (fun i => i.elim0)⟩
  rw [h] at hx
  exact hx.elim

/-- An inclusion into the whole-spectrum domain restricts by the structural
map. -/
theorem restriction_toWhole {U : Domain K A} (f : U ⟶ whole K A) :
    f.restriction = U.baseMap :=
  (BoundedAlgHom.comp_id f.restriction).symm.trans f.comp_baseMap

end Domain

/-- An affinoid algebra with empty spectrum is the zero ring. -/
theorem subsingleton_of_isEmpty (h : IsEmpty (BanachSpectrum A)) : Subsingleton A :=
  (Domain.whole K A).subsingleton_algebra_of_locus_eq_empty (Set.univ_eq_empty_iff.2 h)

omit [CompleteSpace K] in
/-- The image of `a` in the Laurent chart `q ≤ |a|` is a unit. -/
theorem isUnit_baseMap_lowerBound (a : A) (q : ℝ) (hq : 0 < q) :
    IsUnit ((RationalChart.lowerBound a q hq).baseMap a) := by
  have h : (RationalChart.lowerBound a q hq).denominatorClass = a :=
    (presentationMap_surjective K A a).choose_spec
  have hu := (RationalChart.lowerBound a q hq).isUnit_map_denominator
    (BoundedAlgHom.id K (RationalChart.lowerBound a q hq).algebra)
  rw [h] at hu
  exact hu

/-- An element of an affinoid algebra is a unit if and only if no point of the
spectrum vanishes on it. -/
theorem isUnit_iff_forall_ne_zero (a : A) :
    IsUnit a ↔ ∀ x : BanachSpectrum A, x a ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ x hx
    have h1 : x ((u : A) * (u⁻¹ : Aˣ)) = 1 := by
      rw [Units.mul_inv]
      exact map_one x.toMulRingSeminorm
    rw [map_mul, show x.toMulRingSeminorm (u : A) = 0 from hx, zero_mul] at h1
    exact zero_ne_one h1
  · intro ha
    rcases isEmpty_or_nonempty (BanachSpectrum A) with he | hne
    · have := subsingleton_of_isEmpty he
      exact isUnit_of_subsingleton a
    obtain ⟨x₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (BanachSpectrum.evaluation a).continuous.continuousOn
    have hq : 0 < x₀ a := lt_of_le_of_ne (apply_nonneg x₀.toMulRingSeminorm a) (ha x₀).symm
    let d := RationalChart.lowerBound a (x₀ a) hq
    let c : Domain.FiniteCover (Domain.whole K A) :=
      ⟨1, fun _ => d.toDomain, fun _ => Domain.inclusionOfSubset _ _ (Set.subset_univ _),
        fun x _ => ⟨0, (RationalChart.mem_locus_lowerBound a (x₀ a) hq x).2
          (hmin (Set.mem_univ x))⟩⟩
    have hres : ∀ i, (c.map i).restriction = d.baseMap := fun i =>
      Domain.restriction_toWhole (c.map i)
    obtain ⟨b, hb, -⟩ := c.algebra_existsUnique (fun _ => Ring.inverse (d.baseMap a))
      (fun i j W f g => by
        have hfg : f.restriction = g.restriction :=
          congrArg Domain.Inclusion.restriction
            (Subsingleton.elim (α := Domain.Inclusion W d.toDomain) f g)
        exact congrArg (fun φ : BoundedAlgHom K d.algebra W.algebra =>
          φ (Ring.inverse (d.baseMap a))) hfg)
    let b' : A := b
    refine IsUnit.of_mul_eq_one b' (c.algebra_ext_of_restrict_eq fun i => ?_)
    have hbi : (c.map i).restriction b' = Ring.inverse (d.baseMap a) := congrFun hb i
    have hra : (c.map i).restriction a = d.baseMap a :=
      congrArg (fun φ : BoundedAlgHom K (Domain.whole K A).algebra (c.obj i).algebra => φ a)
        (hres i)
    refine (map_mul (c.map i).restriction.toAlgHom a b').trans ?_
    refine (congrArg₂ (· * ·) hra hbi).trans ?_
    refine (Ring.mul_inverse_cancel _ (isUnit_baseMap_lowerBound a (x₀ a) hq)).trans ?_
    exact (map_one (c.map i).restriction.toAlgHom).symm

omit [CompleteSpace K] in
/-- The values of a point on an idempotent are `0` or `1`. -/
theorem idempotent_apply_eq_zero_or_one {e : A} (he : IsIdempotentElem e)
    (x : BanachSpectrum A) : x e = 0 ∨ x e = 1 := by
  have h : x e * x e = x e := by
    rw [← map_mul x.toMulRingSeminorm]
    exact congrArg x.toMulRingSeminorm he
  have h' : x e * (x e - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

omit [CompleteSpace K] in
/-- The points where an idempotent takes the value `1` form a clopen set. -/
theorem isClopen_setOf_idempotent {e : A} (he : IsIdempotentElem e) :
    IsClopen {x : BanachSpectrum A | x e = 1} := by
  have hcont := (BanachSpectrum.evaluation e).continuous
  have hclosed : {x : BanachSpectrum A | x e = 1} = {x | 1 / 2 ≤ x e} := by
    ext x
    rcases idempotent_apply_eq_zero_or_one he x with h | h <;> simp [h]; norm_num
  have hopen : {x : BanachSpectrum A | x e = 1} = {x | 1 / 2 < x e} := by
    ext x
    rcases idempotent_apply_eq_zero_or_one he x with h | h <;> simp [h]; norm_num
  constructor
  · rw [hclosed]
    exact isClosed_le continuous_const hcont
  · rw [hopen]
    exact isOpen_lt continuous_const hcont

omit [CompleteSpace K] in
/-- A clopen subset of the spectrum and a finite cover of the spectrum by
rational charts, each contained in the subset or in its complement. -/
private theorem exists_rational_cover_of_isClopen (C : Set (BanachSpectrum A))
    (hC : IsClopen C) :
    ∃ (n : ℕ) (d : Fin n → RationalChart K A), (∀ x, ∃ i, x ∈ (d i).locus) ∧
      ∀ i, (d i).locus ⊆ C ∨ (d i).locus ⊆ Cᶜ := by
  have key : ∀ x : BanachSpectrum A, ∃ d : RationalChart K A,
      d.locus ∈ 𝓝 x ∧ (d.locus ⊆ C ∨ d.locus ⊆ Cᶜ) := by
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨d, hdN, hdC⟩ :=
        RationalChart.exists_rational_neighborhood x C (hC.isOpen.mem_nhds hx)
      exact ⟨d, hdN, Or.inl hdC⟩
    · obtain ⟨d, hdN, hdC⟩ :=
        RationalChart.exists_rational_neighborhood x Cᶜ (hC.isClosed.isOpen_compl.mem_nhds hx)
      exact ⟨d, hdN, Or.inr hdC⟩
  choose D hDN hDC using key
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (D x).locus) hDN
  refine ⟨t.card, fun i => D (t.equivFin.symm i), fun x => ?_, fun i => hDC _⟩
  have hx : x ∈ ⋃ x' ∈ t, (D x').locus := by
    rw [ht]
    trivial
  obtain ⟨x', hx', hxD⟩ := Set.mem_iUnion₂.1 hx
  refine ⟨t.equivFin ⟨x', hx'⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxD

/-- The Shilov idempotent theorem for presented affinoid algebras: every clopen
subset of the spectrum is the set where some idempotent takes the value `1`,
and the idempotent vanishes at all other points. -/
theorem exists_idempotent_of_isClopen (C : Set (BanachSpectrum A)) (hC : IsClopen C) :
    ∃ e : A, IsIdempotentElem e ∧ (∀ x ∈ C, x e = 1) ∧ ∀ x ∉ C, x e = 0 := by
  classical
  obtain ⟨n, d, hcov, hside⟩ := exists_rational_cover_of_isClopen C hC
  let c : Domain.FiniteCover (Domain.whole K A) :=
    ⟨n, fun i => (d i).toDomain, fun i => Domain.inclusionOfSubset _ _ (Set.subset_univ _),
      fun x _ => hcov x⟩
  have hres : ∀ i, (c.map i).restriction = (d i).baseMap := fun i =>
    Domain.restriction_toWhole (c.map i)
  let s : ∀ i : Fin c.size, (c.obj i).algebra := fun i =>
    if (d i).locus ⊆ C then 1 else 0
  have hs : c.AlgebraCompatible s := by
    intro i j W f g
    have hWi : W.locus ⊆ (d i).locus := f.subset
    have hWj : W.locus ⊆ (d j).locus := g.subset
    by_cases hi : (d i).locus ⊆ C <;> by_cases hj : (d j).locus ⊆ C
    · simp only [s, hi, hj, ite_true, map_one]
    · have hj' := (hside j).resolve_left hj
      have := W.subsingleton_algebra_of_locus_eq_empty
        (Set.eq_empty_of_forall_notMem fun x hx => hj' (hWj hx) (hi (hWi hx)))
      exact Subsingleton.elim _ _
    · have hi' := (hside i).resolve_left hi
      have := W.subsingleton_algebra_of_locus_eq_empty
        (Set.eq_empty_of_forall_notMem fun x hx => hi' (hWi hx) (hj (hWj hx)))
      exact Subsingleton.elim _ _
    · simp only [s, hi, hj, ite_false, map_zero]
  obtain ⟨e, he, -⟩ := c.algebra_existsUnique s hs
  have hei : ∀ i, (c.map i).restriction e = s i := fun i => congrFun he i
  have hval : ∀ (x : BanachSpectrum A) (i : Fin n), x ∈ (d i).locus →
      x e = if (d i).locus ⊆ C then 1 else 0 := by
    intro x i hx
    obtain ⟨y, hy⟩ := (d i).toDomain.spectrumToLocus_surjective ⟨x, hx⟩
    have hyx : BanachSpectrum.comap (d i).baseMap.toBoundedRingHom y = x :=
      congrArg Subtype.val hy
    have h2 : y ((c.map i).restriction e) = y ((d i).baseMap e) :=
      congrArg (fun φ : BoundedAlgHom K (Domain.whole K A).algebra (c.obj i).algebra =>
        y (φ e)) (hres i)
    rw [← hyx]
    refine h2.symm.trans ?_
    rw [hei i]
    by_cases hi : (d i).locus ⊆ C
    · simp only [s, hi, ite_true]
      exact map_one y.toMulRingSeminorm
    · simp only [s, hi, ite_false]
      exact map_zero y.toMulRingSeminorm
  refine ⟨e, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · refine c.algebra_ext_of_restrict_eq fun i => ?_
    change (c.map i).restriction (e * e) = (c.map i).restriction e
    rw [map_mul, hei i]
    by_cases hi : (d i).locus ⊆ C
    · simp only [s, hi, ite_true, mul_one]
    · simp only [s, hi, ite_false, mul_zero]
  · obtain ⟨i, hxi⟩ := hcov x
    rw [hval x i hxi]
    have hi : (d i).locus ⊆ C := by
      by_contra hi
      exact (hside i).resolve_left hi hxi hx
    simp [hi]
  · obtain ⟨i, hxi⟩ := hcov x
    rw [hval x i hxi]
    have hi : ¬ (d i).locus ⊆ C := fun hi => hx (hi hxi)
    simp [hi]

/-- The idempotent of a clopen subset is unique. -/
theorem idempotent_unique_of_isClopen (C : Set (BanachSpectrum A)) {e e' : A}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h1 : ∀ x ∈ C, x e = 1) (h0 : ∀ x ∉ C, x e = 0)
    (h1' : ∀ x ∈ C, x e' = 1) (h0' : ∀ x ∉ C, x e' = 0) : e = e' := by
  let w : A := (1 - e) - e'
  have hw : IsUnit w := by
    refine (isUnit_iff_forall_ne_zero w).2 fun x => ?_
    by_cases hx : x ∈ C
    · have hfe : x (1 - e) = 0 := by
        have hm : x ((1 - e) * e) = 0 := by
          rw [show (1 - e) * e = 0 by rw [sub_mul, one_mul, he.eq, sub_self]]
          exact map_zero x.toMulRingSeminorm
        rw [map_mul, h1 x hx, mul_one] at hm
        exact hm
      have hle : x e' ≤ x (1 - e) + x w := by
        have : e' = (1 - e) - w := by simp only [w]; abel
        calc x e' = x ((1 - e) - w) := congrArg x.toMulRingSeminorm this
          _ ≤ x (1 - e) + x w := map_sub_le_add x.toMulRingSeminorm _ _
      rw [h1' x hx, hfe, zero_add] at hle
      exact (lt_of_lt_of_le zero_lt_one hle).ne'
    · have hle : x 1 ≤ x w + x e + x e' := by
        have : (1 : A) = w + e + e' := by simp only [w]; abel
        calc x 1 = x (w + e + e') := congrArg x.toMulRingSeminorm this
          _ ≤ x (w + e) + x e' := map_add_le_add x.toMulRingSeminorm _ _
          _ ≤ x w + x e + x e' := by
            gcongr
            exact map_add_le_add x.toMulRingSeminorm _ _
      rw [h0 x hx, h0' x hx, add_zero, add_zero,
        show x 1 = 1 from map_one x.toMulRingSeminorm] at hle
      exact (lt_of_lt_of_le zero_lt_one hle).ne'
  have hprod : (e - e') * w = 0 := by
    simp only [w]
    have hee : e * e = e := he.eq
    have hee' : e' * e' = e' := he'.eq
    ring_nf
    linear_combination (-1 : A) * hee + hee'
  have := hw.mul_left_eq_zero.mp hprod
  exact sub_eq_zero.mp this

/-- `e` is the idempotent of the subset `C`: it is idempotent, takes the value
`1` at the points of `C` and vanishes at all other points. -/
def IsClopenIdempotent (C : Set (BanachSpectrum A)) (e : A) : Prop :=
  IsIdempotentElem e ∧ (∀ x ∈ C, x e = 1) ∧ ∀ x ∉ C, x e = 0

/-- The idempotent of a clopen subset of the spectrum. -/
def clopenIdempotent (C : Set (BanachSpectrum A)) (hC : IsClopen C) : A :=
  (exists_idempotent_of_isClopen C hC).choose

theorem isClopenIdempotent_clopenIdempotent (C : Set (BanachSpectrum A)) (hC : IsClopen C) :
    IsClopenIdempotent C (clopenIdempotent C hC) :=
  (exists_idempotent_of_isClopen C hC).choose_spec

theorem IsClopenIdempotent.unique {C : Set (BanachSpectrum A)} {e e' : A}
    (he : IsClopenIdempotent C e) (he' : IsClopenIdempotent C e') : e = e' :=
  idempotent_unique_of_isClopen C he.1 he'.1 he.2.1 he.2.2 he'.2.1 he'.2.2

omit [CompleteSpace K] in
/-- Conversely, every idempotent is the idempotent of the clopen set where it
takes the value `1`. -/
theorem isClopenIdempotent_setOf {e : A} (he : IsIdempotentElem e) :
    IsClopenIdempotent {x : BanachSpectrum A | x e = 1} e :=
  ⟨he, fun _ hx => hx, fun x hx => (idempotent_apply_eq_zero_or_one he x).resolve_right hx⟩

/-- The Weierstrass chart `|1 - e| ≤ 1/2` of the idempotent of a clopen
subset. -/
def clopenRationalChart (C : Set (BanachSpectrum A)) (hC : IsClopen C) : RationalChart K A :=
  RationalChart.upperBound (1 - clopenIdempotent C hC) (1 / 2) (by norm_num)

/-- The locus of `clopenRationalChart` is the clopen subset itself. -/
theorem locus_clopenRationalChart (C : Set (BanachSpectrum A)) (hC : IsClopen C) :
    (clopenRationalChart C hC).locus = C := by
  obtain ⟨he, h1, h0⟩ := isClopenIdempotent_clopenIdempotent C hC
  ext x
  rw [clopenRationalChart, RationalChart.mem_locus_upperBound]
  by_cases hx : x ∈ C
  · have hm : x ((1 - clopenIdempotent C hC) * clopenIdempotent C hC) = 0 := by
      rw [show (1 - clopenIdempotent C hC) * clopenIdempotent C hC = 0 by
        rw [sub_mul, one_mul, he.eq, sub_self]]
      exact map_zero x.toMulRingSeminorm
    rw [map_mul, h1 x hx, mul_one] at hm
    simp only [hx, iff_true]
    change x (1 - clopenIdempotent C hC) ≤ 1 / 2
    rw [hm]
    norm_num
  · have hle : x 1 ≤ x (1 - clopenIdempotent C hC) + x (clopenIdempotent C hC) := by
      calc x 1 = x ((1 - clopenIdempotent C hC) + clopenIdempotent C hC) := by
            rw [sub_add_cancel]
        _ ≤ _ := map_add_le_add x.toMulRingSeminorm _ _
    rw [h0 x hx, add_zero, show x 1 = 1 from map_one x.toMulRingSeminorm] at hle
    simp only [hx, iff_false, not_le]
    change 1 / 2 < x (1 - clopenIdempotent C hC)
    linarith

end Langlands.Analytic.PresentedAffinoidAlgebra
