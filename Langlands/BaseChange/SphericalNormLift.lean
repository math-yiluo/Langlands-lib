import Langlands.Algebra.MonogenicCyclicUnitProduct
import Langlands.BaseChange.SphericalCosetDescent
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A cyclic norm lift integral on every spherical conjugate of a given matrix. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix _root_.Polynomial Correspondence IsLocalRing PadicField.TopologicalData

universe u v

section Evaluation

variable {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]

/-- Evaluate the adjoined root at an element of a possibly noncommutative
algebra. The coefficients still act through the central scalar map. -/
def adjoinRootEval (f : R[X]) (m : A) (hm : aeval m f = 0) : AdjoinRoot f →+* A :=
  Ideal.Quotient.lift _ (aeval m).toRingHom fun q hq => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hq
    change aeval m (f * c) = 0
    rw [map_mul, hm, zero_mul]

@[simp] theorem adjoinRootEval_of (f : R[X]) (m : A) (hm : aeval m f = 0) (a : R) :
    adjoinRootEval f m hm (AdjoinRoot.of f a) = algebraMap R A a := by
  change aeval m (C a) = _
  simp

@[simp] theorem adjoinRootEval_root (f : R[X]) (m : A) (hm : aeval m f = 0) :
    adjoinRootEval f m hm (AdjoinRoot.root f) = m := by
  change aeval m X = m
  exact aeval_X m

end Evaluation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

local notation "T" => F.canonicalTopologicalData
local notation "S" => E.canonicalTopologicalData
local instance : Algebra (T).Integers (S).Integers := relativeIntegerAlgebra T S

/-- The cyclic norm of an element of the extension spherical subgroup again
belongs to that subgroup. -/
theorem cyclicNorm_mem_sphericalSubgroup (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    (l : ℕ) {r : ℕ} {g : GeneralLinear (r + 1) E.Carrier}
    (hg : g ∈ sphericalSubgroup E r) : cyclicNorm σ l g ∈ sphericalSubgroup E r := by
  induction l with
  | zero => simpa only [cyclicNorm_zero] using (sphericalSubgroup E r).one_mem
  | succ l ih =>
    rw [cyclicNorm_succ]
    exact (sphericalSubgroup E r).mul_mem ih (entrywiseAut_mem_sphericalSubgroup F E (σ ^ l) hg)

private theorem charpoly_map_of_integral_conj {r : ℕ}
    {g z : GeneralLinear (r + 1) E.Carrier} {k : GeneralLinear (r + 1) (S).Integers}
    (hk : GeneralLinearGroup.map (S).Integers.subtype k = z⁻¹ * g * z) :
    k.val.charpoly.map (S).Integers.subtype = g.val.charpoly := by
  rw [← Matrix.charpoly_map]
  change (GeneralLinearGroup.map (S).Integers.subtype k).val.charpoly = _
  rw [hk]
  change ((z⁻¹).val * g.val * z.val).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, show z.val * (z⁻¹).val = 1 from z.mul_inv, one_mul]

private theorem exists_integral_charpoly {r : ℕ} (γ : GeneralLinear (r + 1) F.Carrier)
    (hγ : ∃ z : GeneralLinear (r + 1) E.Carrier,
      z⁻¹ * baseChange F.Carrier E.Carrier (r + 1) γ * z ∈ sphericalSubgroup E r) :
    ∃ f : (T).Integers[X], f.Monic ∧ IsUnit (f.coeff 0) ∧
      f.map (T).Integers.subtype = γ.val.charpoly := by
  obtain ⟨z, hz⟩ := hγ
  change _ ∈ (GeneralLinearGroup.map (S).Integers.subtype).range at hz
  obtain ⟨k, hk⟩ := hz
  have hkpoly := charpoly_map_of_integral_conj E hk
  rw [show (baseChange F.Carrier E.Carrier (r + 1) γ).val.charpoly =
    γ.val.charpoly.map (algebraMap F.Carrier E.Carrier) from Matrix.charpoly_map _ _] at hkpoly
  have hcoeff (i : ℕ) :
      algebraMap F.Carrier E.Carrier (γ.val.charpoly.coeff i) =
        (S).Integers.subtype (k.val.charpoly.coeff i) := by
    simpa only [Polynomial.coeff_map] using
      (congrArg (fun f : E.Carrier[X] => f.coeff i) hkpoly).symm
  have hmem : γ.val.charpoly ∈ (Polynomial.mapRingHom (T).Integers.subtype).range :=
    (Polynomial.mem_map_range _).mpr fun i =>
      let hi := (relative_mem_integers_iff T S _).mp (by rw [hcoeff i]; exact (k.val.charpoly.coeff i).property)
      ⟨⟨γ.val.charpoly.coeff i, hi⟩, rfl⟩
  obtain ⟨f, hf⟩ := hmem
  change f.map (T).Integers.subtype = γ.val.charpoly at hf
  have hmap : (f.map (algebraMap (T).Integers (S).Integers)).map (S).Integers.subtype =
      k.val.charpoly.map (S).Integers.subtype := by
    have hcomm : (S).Integers.subtype.comp (algebraMap (T).Integers (S).Integers) =
        (algebraMap F.Carrier E.Carrier).comp (T).Integers.subtype := rfl
    rw [hkpoly, Polynomial.map_map, hcomm, ← Polynomial.map_map, hf]
  have hfk := Polynomial.map_injective _ Subtype.val_injective hmap
  have hk0 : IsUnit (k.val.charpoly.coeff 0) := by
    apply isUnit_of_mul_isUnit_right (x := (-1) ^ Fintype.card (Fin (r + 1)))
    rw [← Matrix.det_eq_sign_charpoly_coeff]
    exact (GeneralLinearGroup.det k).isUnit
  have hunit : IsUnit ((relativeIntegerMap T S) (f.coeff 0)) := by
    change IsUnit ((algebraMap (T).Integers (S).Integers) (f.coeff 0))
    rwa [← Polynomial.coeff_map, hfk]
  exact ⟨f, (Subtype.val_injective.monic_map_iff (f := (T).Integers.subtype)).mpr
    (hf.symm ▸ γ.val.charpoly_monic), isUnit_of_map_unit (relativeIntegerMap T S) _ hunit, hf⟩

/-- If the base-changed matrix has a spherical conjugate, it has a cyclic norm
lift that is integral after every conjugation making the norm integral. -/
theorem exists_spherical_cyclicNorm_lift {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier}
    {l r : ℕ} (hσ : IsCyclicAlgebra σ l) (he : (S).ramificationIndex = (T).ramificationIndex)
    (γ : GeneralLinear (r + 1) F.Carrier)
    (hγ : ∃ z : GeneralLinear (r + 1) E.Carrier,
      z⁻¹ * baseChange F.Carrier E.Carrier (r + 1) γ * z ∈ sphericalSubgroup E r) :
    ∃ u : GeneralLinear (r + 1) E.Carrier,
      cyclicNorm σ l u = baseChange F.Carrier E.Carrier (r + 1) γ ∧
      ∀ z : GeneralLinear (r + 1) E.Carrier,
        z⁻¹ * baseChange F.Carrier E.Carrier (r + 1) γ * z ∈ sphericalSubgroup E r →
        z⁻¹ * u * z ∈ sphericalSubgroup E r := by
  classical
  obtain ⟨f, hf, hf0, hfp⟩ := exists_integral_charpoly F E γ hγ
  let := (S).topology
  let := (S).valuativeRel
  let := (S).localField
  let := (S).moduleTopology
  let := (S).fieldT2
  let := (S).finite_residueField
  let σ₀ := canonicalIntegerAut F E σ
  have hperiod : σ₀ ^ l = 1 := by rw [← map_pow, hσ.pow_eq_one, map_one]
  have hcont : Continuous σ₀ := by
    have hfield : Continuous σ :=
      IsModuleTopology.continuous_of_linearMap (σ.toAlgHom.restrictScalars (Padic p)).toLinearMap
    exact continuous_induced_rng.mpr (hfield.comp continuous_subtype_val)
  obtain ⟨a, ha⟩ := exists_integer_distinct_conjugates F E hσ he
  have hsep : Pairwise fun i j : Fin l => IsUnit ((σ₀ ^ (i : ℕ)) a - (σ₀ ^ (j : ℕ)) a) := by
    intro i j hij
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_sub, sub_ne_zero]
    simpa only [σ₀, ← map_pow] using ha.ne hij
  obtain ⟨w, hw⟩ := exists_prod_adjoinRootCoefficientAut_eq_root f hf hf0 σ₀ hσ.pos hperiod hcont a hsep
  let g := f.map (algebraMap (T).Integers (S).Integers)
  let Γ := baseChange F.Carrier E.Carrier (r + 1) γ
  let M := Matrix (Fin (r + 1)) (Fin (r + 1)) E.Carrier
  have hchar : g.map (S).Integers.subtype = Γ.val.charpoly := by
    have hcomm : (S).Integers.subtype.comp (algebraMap (T).Integers (S).Integers) =
        (algebraMap F.Carrier E.Carrier).comp (T).Integers.subtype := rfl
    change (f.map _).map _ = _
    rw [Polynomial.map_map, hcomm, ← Polynomial.map_map, hfp]
    exact (Matrix.charpoly_map _ _).symm
  have hroot : aeval Γ.val g = 0 := by
    rw [Polynomial.aeval_eq_aeval_map (φ := (S).Integers.subtype) rfl, hchar]
    exact Matrix.aeval_self_charpoly _
  let ev := adjoinRootEval g Γ.val hroot
  let ρ (τ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) := adjoinRootCoefficientAut f (canonicalIntegerAut F E τ)
  have hact (τ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) :
      ev.comp (ρ τ).toRingHom = (RingHom.mapMatrix (τ : E.Carrier →+* E.Carrier)).comp ev := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro x
      change ev (ρ τ (AdjoinRoot.of g x)) =
        (RingHom.mapMatrix (τ : E.Carrier →+* E.Carrier)) (ev (AdjoinRoot.of g x))
      rw [show ρ τ (AdjoinRoot.of g x) = AdjoinRoot.of g (canonicalIntegerAut F E τ x) from
        adjoinRootCoefficientAut_of f _ x, adjoinRootEval_of, adjoinRootEval_of]
      ext i j
      change (if i = j then (canonicalIntegerAut F E τ x : E.Carrier) else 0) =
        τ (if i = j then (x : E.Carrier) else 0)
      rw [apply_ite τ, map_zero, canonicalIntegerAut_coe]
    · change ev (ρ τ (AdjoinRoot.root g)) = (RingHom.mapMatrix (τ : E.Carrier →+* E.Carrier))
        (ev (AdjoinRoot.root g))
      rw [show ρ τ (AdjoinRoot.root g) = AdjoinRoot.root g from adjoinRootCoefficientAut_root f _,
        adjoinRootEval_root]
      exact (congrArg Units.val (entrywiseAut_baseChange τ γ)).symm
  let u : GeneralLinear (r + 1) E.Carrier := Units.map ev.toMonoidHom w
  have hn (m : ℕ) : (cyclicNorm σ m u).val = ev (∏ i : Fin m, ((ρ σ) ^ (i : ℕ)) (w : AdjoinRoot g)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [cyclicNorm_succ, Units.val_mul, ih, Fin.prod_univ_castSucc, map_mul]
      congr 1
      change (RingHom.mapMatrix ((σ ^ m : E.Carrier ≃ₐ[F.Carrier] E.Carrier) : E.Carrier →+* E.Carrier))
        (ev (w : AdjoinRoot g)) = ev (((ρ σ) ^ m) (w : AdjoinRoot g))
      have hm : (ρ σ) ^ m = ρ (σ ^ m) := by simp only [ρ, map_pow]
      rw [hm]
      exact (DFunLike.congr_fun (hact (σ ^ m)) (w : AdjoinRoot g)).symm
  refine ⟨u, Units.ext ((hn l).trans ?_), ?_⟩
  · change ev (∏ i : Fin l, (adjoinRootCoefficientAut f σ₀ ^ (i : ℕ)) (w : AdjoinRoot g)) = Γ.val
    rw [hw, adjoinRootEval_root]
  · intro z hz
    change _ ∈ (GeneralLinearGroup.map (S).Integers.subtype).range at hz ⊢
    obtain ⟨k, hk⟩ := hz
    have hkchar : k.val.charpoly = g := Polynomial.map_injective _ Subtype.val_injective
      ((charpoly_map_of_integral_conj E hk).trans hchar.symm)
    have hkroot : aeval k.val g = 0 := hkchar ▸ Matrix.aeval_self_charpoly _
    let evk := adjoinRootEval g k.val hkroot
    let c : M →+* M := MulSemiringAction.toRingHom (ConjAct Mˣ) M (ConjAct.toConjAct z⁻¹)
    have hc (m : M) : c m = (z⁻¹).val * m * z.val := by
      change (z⁻¹).val * m * (z⁻¹)⁻¹.val = _
      rw [inv_inv]
    have hcmp : (RingHom.mapMatrix (S).Integers.subtype).comp evk = c.comp ev := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro x
        change (RingHom.mapMatrix (S).Integers.subtype) (evk (AdjoinRoot.of g x)) =
          c (ev (AdjoinRoot.of g x))
        rw [adjoinRootEval_of, adjoinRootEval_of, hc]
        have hscalar := Matrix.map_algebraMap (n := Fin (r + 1)) (R := (S).Integers) x (S).Integers.subtype
          (map_zero _) rfl
        change (algebraMap (S).Integers (Matrix (Fin (r + 1)) (Fin (r + 1)) (S).Integers) x).map
           (S).Integers.subtype = _
        rw [hscalar, (Algebra.commutes x (z⁻¹).val).symm, mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, mul_one]
      · change (RingHom.mapMatrix (S).Integers.subtype) (evk (AdjoinRoot.root g)) =
          c (ev (AdjoinRoot.root g))
        rw [adjoinRootEval_root, adjoinRootEval_root, hc]
        exact congrArg Units.val hk
    exact ⟨Units.map evk.toMonoidHom w, Units.ext (DFunLike.congr_fun hcmp (w : AdjoinRoot g))⟩

end Langlands.BaseChange
