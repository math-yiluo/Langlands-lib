import Langlands.BaseChange.TwistedCharacter.SemisimpleSlice
import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution

/-! # A conjugation-invariant open domain of semisimple descent -/

noncomputable section

namespace Langlands.BaseChange

open ContinuousLinearMap Function Set
open scoped RightActions _root_.Topology

variable {F R : Type*} [NontriviallyNormedField F] [NormedRing R] [NormedAlgebra F R]
  [CompleteSpace F] [CompleteSpace R] [FiniteDimensional F R]

/-- Twisted conjugation of `1 + Y` on the fixed algebra, in ambient algebra
coordinates for the conjugator. The semisimple center has been translated to `1`. -/
def adjointConjugationMap (α : R ≃ₐ[F] R) (z : R × adjointFixedAlgebra α) : R :=
  z.1 * (1 + z.2.val) * Ring.inverse (α z.1)

/-- The strict derivative in the full product of the conjugating directions and
fixed-algebra directions at `(1, Y)`. -/
def adjointConjugationDifferential (α : R ≃ₐ[F] R) (y : adjointFixedAlgebra α) :
    R × adjointFixedAlgebra α →L[F] R :=
  let p := fst F R (adjointFixedAlgebra α)
  let q := (adjointFixedAlgebra α).val.toLinearMap.toContinuousLinearMap.comp
    (snd F R (adjointFixedAlgebra α))
  let x := 1 + y.val
  (mulLeftRight F R 1 x).comp p + q -
    (mulLeftRight F R x 1).comp (α.toLinearMap.toContinuousLinearMap.comp p)

omit [CompleteSpace R] in
@[simp] theorem adjointConjugationDifferential_apply (α : R ≃ₐ[F] R)
    (y : adjointFixedAlgebra α) (z : R × adjointFixedAlgebra α) :
    adjointConjugationDifferential α y z =
      z.1 * (1 + y.val) + z.2.val - (1 + y.val) * α z.1 := by
  simp [adjointConjugationDifferential, mulLeftRight_apply, mul_add, add_mul]

private theorem hasStrictFDerivAt_adjointConjugationMap_one (α : R ≃ₐ[F] R)
    (y : adjointFixedAlgebra α) :
    HasStrictFDerivAt (adjointConjugationMap α) (adjointConjugationDifferential α y) (1, y) := by
  let S := adjointFixedAlgebra α
  let p := fst F R S
  let q := S.val.toLinearMap.toContinuousLinearMap.comp (snd F R S)
  let a := α.toLinearMap.toContinuousLinearMap.comp p
  have hp : HasStrictFDerivAt (fun z : R × S => z.1) p (1, y) := p.hasStrictFDerivAt
  have hq : HasStrictFDerivAt (fun z : R × S => 1 + z.2.val) q (1, y) :=
    q.hasStrictFDerivAt.const_add 1
  have ha : HasStrictFDerivAt (fun z : R × S => α z.1) a (1, y) := a.hasStrictFDerivAt
  have hα1 : α ((1, y) : R × S).1 = 1 := map_one α
  have hinv : HasStrictFDerivAt Ring.inverse (-(ContinuousLinearMap.id F R))
      (α ((1, y) : R × S).1) := by
    rw [hα1]
    have he : mulLeftRight F R (1 : R) 1 = ContinuousLinearMap.id F R := by
      ext z
      simp [mulLeftRight_apply]
    simpa only [Units.val_one, inv_one, he] using
      hasStrictFDerivAt_ringInverse (𝕜 := F) (1 : Rˣ)
  have hprod := (hp.mul' hq).mul' (hinv.comp ((1, y) : R × S) ha)
  change HasStrictFDerivAt (adjointConjugationMap α) _ _ at hprod
  have he : (((1, y) : R × S).1 * (1 + y.val)) •>
      (-ContinuousLinearMap.id F R).comp a +
      (((1, y) : R × S).1 •> q + p <• (1 + y.val)) <•
        Ring.inverse (α ((1, y) : R × S).1) = adjointConjugationDifferential α y := by
    rw [hα1, Ring.inverse_one]
    apply ContinuousLinearMap.ext
    intro z
    change 1 * (1 + y.val) * (-α z.1) + (1 * z.2.val + z.1 * (1 + y.val)) * 1 =
      adjointConjugationDifferential α y z
    simp only [one_mul, mul_one, mul_neg, adjointConjugationDifferential_apply]
    abel
  simpa only [Pi.mul_apply, he] using hprod

omit [CompleteSpace R] in
private theorem continuous_adjointConjugationDifferential (α : R ≃ₐ[F] R) :
    Continuous (adjointConjugationDifferential α) := by
  let S := adjointFixedAlgebra α
  let p := fst F R S
  let q := S.val.toLinearMap.toContinuousLinearMap.comp (snd F R S)
  let x (y : S) : R := 1 + y.val
  have hx : Continuous x := continuous_const.add continuous_subtype_val
  have hRight : Continuous fun y : S => mulLeftRight F R 1 (x y) :=
    (mulLeftRight F R 1).continuous.comp hx
  have hLeft : Continuous fun y : S => mulLeftRight F R (x y) 1 :=
    (mulLeftRight F R).continuous.comp hx |>.clm_apply continuous_const
  exact ((hRight.clm_comp (continuous_const (y := p))).add (continuous_const (y := q))).sub
    (hLeft.clm_comp continuous_const)

private theorem isOpen_surjective_differential {V : Type*} [NormedAddCommGroup V]
    [NormedSpace F V] : IsOpen {d : V →L[F] R | Surjective d} := by
  rw [isOpen_iff_mem_nhds]
  intro d hd
  have hd' : Surjective d := hd
  obtain ⟨e, he⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hd')
  let C (T : V →L[F] R) := T.comp e
  have hc : Continuous C := (ContinuousLinearMap.isBoundedLinearMap_comp_right e).continuous
  have hid : C d = ContinuousLinearMap.id F R := by
    ext x
    exact DFunLike.congr_fun he x
  have hn : {f : R →L[F] R | f.IsInvertible} ∈ 𝓝 (C d) := by
    rw [hid]
    exact (ContinuousLinearEquiv.refl F R).nhds
  filter_upwards [hc.continuousAt.preimage_mem_nhds hn] with T hT
  obtain ⟨a, ha⟩ := (show (C T).IsInvertible from hT)
  intro z
  obtain ⟨x, rfl⟩ := a.surjective z
  exact ⟨e x, (DFunLike.congr_fun ha x).symm⟩

/-- The fixed-algebra domain where `1 + Y` is a unit and the conjugation map is a
submersion at conjugator `1`. -/
def adjointConjugationDomain (α : R ≃ₐ[F] R) : Set (adjointFixedAlgebra α) :=
  {y | IsUnit (1 + y) ∧ Surjective (adjointConjugationDifferential α y)}

/-- The submersion condition is open and contains zero for a semisimple adjoint. -/
theorem isOpen_adjointConjugationDomain (α : R ≃ₐ[F] R) :
    IsOpen (adjointConjugationDomain α) := by
  let := FiniteDimensional.complete F (adjointFixedAlgebra α)
  exact (Units.isOpen.preimage (continuous_const.add continuous_id)).inter
    (isOpen_surjective_differential.preimage (continuous_adjointConjugationDifferential α))

theorem zero_mem_adjointConjugationDomain (α : R ≃ₐ[F] R)
    (hα : Module.End.IsSemisimple α.toLinearMap) : 0 ∈ adjointConjugationDomain α := by
  refine ⟨by simp, ?_⟩
  obtain ⟨q, _, hq, hqr, _⟩ := exists_semisimpleSliceChart α hα
  intro z
  obtain ⟨⟨b, c⟩, hbc⟩ := ((adjointFixedAlgebra α).toSubmodule.prodEquivOfIsCompl q hq).surjective z
  have hc : c.val ∈ LinearMap.range (LinearMap.id - α.toLinearMap) := by
    rw [← hqr]
    exact c.property
  obtain ⟨a, ha⟩ := hc
  change b.val + c.val = z at hbc
  change a - α a = c.val at ha
  refine ⟨(a, b), ?_⟩
  rw [adjointConjugationDifferential_apply]
  simp only [Subalgebra.coe_zero, add_zero, mul_one, one_mul]
  rw [add_sub_right_comm, ha, add_comm, hbc]

omit [CompleteSpace R] in
/-- Fixed-unit conjugation preserves the submersion domain. -/
theorem adjointConjugationDomain_conjugation (α : R ≃ₐ[F] R)
    (u : (adjointFixedAlgebra α)ˣ) {y : adjointFixedAlgebra α}
    (hy : y ∈ adjointConjugationDomain α) :
    HarmonicAnalysis.UnitConjugation.conjugationHomeomorph u y ∈ adjointConjugationDomain α := by
  let S := adjointFixedAlgebra α
  let v : Rˣ := Units.map S.val.toMonoidHom u
  rcases hy with ⟨hu, hs⟩
  let c := HarmonicAnalysis.UnitConjugation.conjugationHomeomorph u
  let C := HarmonicAnalysis.UnitConjugation.conjugationHomeomorph v
  have hOne : 1 + c y = (u : S) * (1 + y) * ↑u⁻¹ := by
    rw [show c y = (u : S) * y * ↑u⁻¹ from rfl, mul_add, mul_one, add_mul, Units.mul_inv]
  refine ⟨hOne ▸ ?_, ?_⟩
  · exact ((u.isUnit.mul hu).mul (u⁻¹).isUnit)
  · have hαv : α v.val = v.val := (u : S).property
    have hαvi : α ((v⁻¹ : Rˣ) : R) = (v⁻¹ : Rˣ).val := ((u⁻¹ : Sˣ) : S).property
    have hC (x : R) : α (C x) = C (α x) := by
      simp only [C, HarmonicAnalysis.UnitConjugation.conjugationHomeomorph_apply,
        map_mul, hαv, hαvi]
    have hmul (x x' : R) : C (x * x') = C x * C x' := by
      simp [C, HarmonicAnalysis.UnitConjugation.conjugationHomeomorph_apply, mul_assoc]
    have hadd (x x' : R) : C (x + x') = C x + C x' := by
      simp [C, HarmonicAnalysis.UnitConjugation.conjugationHomeomorph_apply, mul_add, add_mul]
    have hsub (x x' : R) : C (x - x') = C x - C x' := by
      simp [C, HarmonicAnalysis.UnitConjugation.conjugationHomeomorph_apply, mul_sub, sub_mul]
    have hx : 1 + (c y).val = C (1 + y.val) := congrArg Subtype.val hOne
    intro z
    obtain ⟨⟨a, b⟩, hab⟩ := hs (C.symm z)
    refine ⟨(C a, c b), ?_⟩
    change adjointConjugationDifferential α (c y) (C a, c b) = z
    rw [← C.apply_symm_apply z, ← hab, adjointConjugationDifferential_apply,
      adjointConjugationDifferential_apply]
    change C a * (1 + (c y).val) + (c b).val - (1 + (c y).val) * α (C a) =
      C (a * (1 + y.val) + b.val - (1 + y.val) * α a)
    rw [hsub, hadd (a * (1 + y.val)) b.val, hmul a (1 + y.val),
      hmul (1 + y.val) (α a), hx, hC]
    rfl

/-- The conjugation map is submersive on the full product of the unit locus and
its fixed-algebra submersion domain. -/
theorem adjointConjugationMap_submersive (α : R ≃ₐ[F] R) (g : Rˣ)
    {y : adjointFixedAlgebra α} (hy : y ∈ adjointConjugationDomain α) :
    ∃ d : R × adjointFixedAlgebra α →L[F] R,
      HasStrictFDerivAt (adjointConjugationMap α) d (g.val, y) ∧ Surjective d := by
  let S := adjointFixedAlgebra α
  let a := Units.map α.toMonoidHom g
  let L : R ≃L[F] R := (Units.mulLeftLinearEquiv F R g).toContinuousLinearEquiv
  let T : R ≃L[F] R := L.trans ((a⁻¹).mulRightLinearEquiv F).toContinuousLinearEquiv
  let E : (R × S) ≃L[F] (R × S) := L.prodCongr (ContinuousLinearEquiv.refl F S)
  have hE : E (1, y) = (g.val, y) := by
    ext <;> simp [E, L]
  have hMap (z : R × S) : adjointConjugationMap α (E z) = T (adjointConjugationMap α z) := by
    change (g.val * z.1) * (1 + z.2.val) * Ring.inverse (α (g.val * z.1)) =
      g.val * (z.1 * (1 + z.2.val) * Ring.inverse (α z.1)) * ((a⁻¹ : Rˣ) : R)
    rw [map_mul, show α g.val = a.val from rfl, Ring.inverse_mul (.inl a.isUnit), Ring.inverse_unit]
    simp only [mul_assoc]
  let d := adjointConjugationDifferential α y
  let d' := (T : R →L[F] R).comp (d.comp (E.symm : R × S →L[F] R × S))
  refine ⟨d', ?_, T.surjective.comp (hy.2.comp E.symm.surjective)⟩
  have hE' : E.symm (g.val, y) = (1, y) := by rw [← hE, E.symm_apply_apply]
  have hd : HasStrictFDerivAt (adjointConjugationMap α) d (E.symm (g.val, y)) :=
    hE'.symm ▸ hasStrictFDerivAt_adjointConjugationMap_one α y
  have h := ((T : R →L[F] R).hasStrictFDerivAt.comp (g.val, y)
    (hd.comp (g.val, y) (E.symm : R × S →L[F] R × S).hasStrictFDerivAt))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun z => by
    change T (adjointConjugationMap α (E.symm z)) = adjointConjugationMap α z
    rw [← hMap, E.apply_symm_apply]

end Langlands.BaseChange
