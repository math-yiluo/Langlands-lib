import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient

/-! # Scalar conjugation of a nilpotent in a semisimple algebra -/

namespace Langlands.HarmonicAnalysis.UnitConjugation

open LinearMap

universe u v

section SemisimpleModule

variable {R : Type u} [Ring R] (a : Rˣ) (ha : ∀ r : R, Commute (a : R) r)

private def centralUnitSMul (M : Type v) [AddCommGroup M] [Module R M] : M ≃ₗ[R] M where
  toFun x := (a : R) • x
  invFun x := (↑a⁻¹ : R) • x
  left_inv x := by
    change (↑a⁻¹ : R) • (a : R) • x = x
    rw [← mul_smul, Units.inv_mul, one_smul]
  right_inv x := by
    change (a : R) • (↑a⁻¹ : R) • x = x
    rw [← mul_smul, Units.mul_inv, one_smul]
  map_add' _ _ := smul_add _ _ _
  map_smul' r x := by
    change (a : R) • r • x = r • (a : R) • x
    rw [← mul_smul, ← mul_smul, (ha r).eq]

include ha in
/-- Construct a scaling conjugator by induction on the image filtration. The
conjugator fixes a complement of the image, which lets it extend from the next
image to the whole module. -/
private theorem exists_scaleEquiv_of_pow_eq_zero (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
      (T : Module.End R M), T ^ n = 0 →
      ∃ (U : Submodule R M) (e : M ≃ₗ[R] M),
        IsCompl U (range T) ∧ (∀ x ∈ U, e x = x) ∧
          ∀ x, e (T x) = (a : R) • T (e x) := by
  induction n with
  | zero =>
      intro M _ _ _ T hT
      have hzero : ∀ x : M, x = 0 := by
        intro x
        simpa using congrArg (fun f : Module.End R M => f x) hT
      have hT0 : T = 0 := LinearMap.ext fun x => hzero (T x)
      subst T
      exact ⟨⊤, LinearEquiv.refl R M, by simpa using (isCompl_top_bot :
        IsCompl (⊤ : Submodule R M) ⊥), fun _ _ => rfl, by simp⟩
  | succ n ih =>
      intro M _ _ _ T hT
      let P := range T
      have hmem (x : M) : T x ∈ P := ⟨x, rfl⟩
      let T' : Module.End R P := T.restrict (fun x _ => hmem x)
      have hT' : T' ^ n = 0 := by
        ext x
        obtain ⟨y, hy⟩ := x.property
        change (((T.restrict (fun x _ => hmem x)) ^ n) x : P).val = 0
        rw [Module.End.pow_restrict]
        change (T ^ n) (x : M) = 0
        rw [← hy, ← Module.End.mul_apply, ← pow_succ, hT, zero_apply]
      obtain ⟨W, eP, hW, hfixP, hscaleP⟩ := ih P T' hT'
      let Tc : M →ₗ[R] P := T.codRestrict P hmem
      let S := W.comap Tc
      obtain ⟨V, hV⟩ := exists_isCompl (P.comap S.subtype)
      let U := V.map S.subtype
      have hUS : U ≤ S := le_trans (Submodule.map_mono le_top) (by
        rw [Submodule.map_subtype_top])
      have hU : IsCompl U P := by
        constructor
        · rw [Submodule.disjoint_def]
          rintro x ⟨y, hy, rfl⟩ hx
          have hy0 : y = 0 := Submodule.disjoint_def.mp hV.disjoint.symm y hy hx
          simp [hy0]
        · rw [Submodule.codisjoint_iff_exists_add_eq]
          intro x
          obtain ⟨w, y, heq, _⟩ := Submodule.existsUnique_add_of_isCompl hW (Tc x)
          obtain ⟨z, hz⟩ := y.property
          change (w : P) + (y : P) = Tc x at heq
          rw [← hz] at heq
          have heq' := congrArg (fun q : P => (q : M)) heq
          change (w : M) + T (z : M) = T x at heq'
          have hsub : x - (z : M) ∈ S := by
            change Tc (x - (z : M)) ∈ W
            convert w.property using 1
            apply Subtype.ext
            change T (x - (z : M)) = (w : M)
            rw [map_sub, ← heq', add_sub_cancel_right]
          obtain ⟨p, v, hpv, _⟩ :=
            Submodule.existsUnique_add_of_isCompl hV ⟨_, hsub⟩
          have hpv' := congrArg (fun q : S => (q : M)) hpv
          change (p : S).val + (v : S).val = x - (z : M) at hpv'
          refine ⟨(v : S).val, (p : S).val + (z : M),
            ⟨v, v.property, rfl⟩, P.add_mem p.property z.property, ?_⟩
          rw [← add_assoc, add_comm (v : S).val, hpv', sub_add_cancel]
      let decomp := U.prodEquivOfIsCompl P hU
      let scaledP := eP.trans (centralUnitSMul a ha P)
      let e := decomp.symm.trans
        ((LinearEquiv.prodCongr (LinearEquiv.refl R U) scaledP).trans decomp)
      have hleft (x : U) : e (x : M) = x := by
        change decomp ((LinearEquiv.prodCongr (LinearEquiv.refl R U) scaledP)
          (decomp.symm x)) = (x : M)
        rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
        simp [decomp]
      have hright (x : P) : e (x : M) = (a : R) • (eP x : M) := by
        change decomp ((LinearEquiv.prodCongr (LinearEquiv.refl R U) scaledP)
          (decomp.symm x)) = (a : R) • (eP x : M)
        rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
        simp [decomp, scaledP, centralUnitSMul]
      refine ⟨U, e, hU, fun x hx => hleft ⟨x, hx⟩, fun x => ?_⟩
      obtain ⟨y, z, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl hU x
      have hscaleU : e (T (y : M)) = (a : R) • T (e (y : M)) := by
        rw [hleft y]
        change e (Tc y : M) = (a : R) • T (y : M)
        rw [hright, hfixP (Tc y) (hUS y.property)]
        rfl
      have hscaleZ : e (T (z : M)) = (a : R) • T (e (z : M)) := by
        change e (T' z : M) = (a : R) • T (e (z : M))
        rw [hright (T' z), hright z, map_smul]
        exact congrArg (fun q : P => (a : R) • (q : M)) (hscaleP z)
      simp only [map_add, hscaleU, hscaleZ, smul_add]

end SemisimpleModule

/-- Over a semisimple algebra, every nonzero scalar multiple of a nilpotent
element is conjugate to that element by a unit of the algebra. -/
def NilpotentScalarConjugationStatement.{u', v'} : Prop :=
  ∀ {F : Type u'} [Field F] {A : Type v'} [Ring A] [Algebra F A] [IsSemisimpleRing A]
    {N : A}, IsNilpotent N → ∀ t : Fˣ,
    ∃ u : Aˣ, (u : A) * N * (↑u⁻¹ : A) = (t : F) • N

/-- Apply the scaling equivalence to right multiplication on the regular left module. -/
theorem nilpotentScalarConjugation : NilpotentScalarConjugationStatement.{u, v} := by
  intro F _ A _ _ _ N hN t
  let a := Units.map (algebraMap F A).toMonoidHom t
  have ha (r : A) : Commute (a : A) r := Algebra.commutes _ _
  obtain ⟨n, hn⟩ := hN
  have hT : (mulRight A N) ^ n = 0 := by
    rw [LinearMap.pow_mulRight, hn]
    exact LinearMap.ext fun x => mul_zero x
  obtain ⟨_, e, _, _, he⟩ :=
    exists_scaleEquiv_of_pow_eq_zero a ha n A (mulRight A N) hT
  have rightMul (f : Module.End A A) (x : A) : f x = x * f 1 := by
    simpa [smul_eq_mul] using f.map_smul x (1 : A)
  let u : Aˣ :=
    { val := e.symm 1
      inv := e 1
      val_inv := (rightMul e.toLinearMap (e.symm 1)).symm.trans (e.apply_symm_apply 1)
      inv_val := (rightMul e.symm.toLinearMap (e 1)).symm.trans (e.symm_apply_apply 1) }
  refine ⟨u, ?_⟩
  have h := he 1
  change e (1 * N) = (a : A) * (e 1 * N) at h
  rw [one_mul, show e N = N * e 1 from rightMul e.toLinearMap N] at h
  change (u : A) * N * (↑u⁻¹ : A) = _
  rw [mul_assoc, show N * (↑u⁻¹ : A) = (a : A) * ((↑u⁻¹ : A) * N) from h,
    ← mul_assoc, (ha (u : A)).eq.symm, mul_assoc, ← mul_assoc (u : A),
    Units.mul_inv, one_mul]
  exact Algebra.smul_def _ _ |>.symm

end Langlands.HarmonicAnalysis.UnitConjugation
