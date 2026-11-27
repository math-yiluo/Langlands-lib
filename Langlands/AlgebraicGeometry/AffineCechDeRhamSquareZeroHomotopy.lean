import Langlands.AlgebraicGeometry.AffineCechDeRham

/-! # The affine homotopy between congruent pullbacks in degree one -/

universe u

open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham.RelativeForms

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {I : Ideal R}

private lemma extendedIdeal_mul_eq_zero (hI : I * I = ⊥)
    {x y : B} (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) :
    x * y = 0 := by
  have hxy := Ideal.mul_mem_mul hx hy
  rwa [← Ideal.map_mul, hI, Ideal.map_bot, Ideal.mem_bot] at hxy

private lemma smul_dZero_eq_zero (hI : I * I = ⊥)
    {x y : B} (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) :
    x • dZero R B y = 0 := by
  change x • KaehlerDifferential.D R B y = 0
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, _, rfl⟩ := hy
    rw [Derivation.map_algebraMap, smul_zero]
  | zero => rw [map_zero, smul_zero]
  | add y z _ _ hy hz => rw [map_add, smul_add, hy, hz, add_zero]
  | smul a y hy ih =>
    change x • KaehlerDifferential.D R B (a * y) = 0
    rw [Derivation.leibniz, smul_add, smul_comm x a, ih, smul_zero, zero_add,
      smul_smul, extendedIdeal_mul_eq_zero hI hx hy, zero_smul]

variable (f g : A →ₐ[R] B) (hI : I * I = ⊥)
  (hfg : ∀ a, f a - g a ∈ I.map (algebraMap R B))

private def differenceDerivation :
    letI := f.toRingHom.toAlgebra
    Derivation R A B := by
  letI := f.toRingHom.toAlgebra
  refine Derivation.mk' (f.toLinearMap - g.toLinearMap) fun a b => ?_
  change f (a * b) - g (a * b) = f a * (f b - g b) + f b * (f a - g a)
  have h := extendedIdeal_mul_eq_zero hI (hfg a) (hfg b)
  simp only [map_mul]
  linear_combination -h

/-- Contract a one-form against the derivation given by the difference of two
pullbacks congruent modulo an extended square-zero ideal. -/
def contractDifferenceOne : Ω[A⁄R] →ₛₗ[f.toRingHom] B := by
  letI := f.toRingHom.toAlgebra
  let F := (differenceDerivation f g hI hfg).liftKaehlerDifferential
  exact { F.toAddMonoidHom with map_smul' := F.map_smul }

@[simp]
lemma contractDifferenceOne_d (a : A) :
    contractDifferenceOne f g hI hfg (KaehlerDifferential.D R A a) = f a - g a := by
  let := f.toRingHom.toAlgebra
  exact (differenceDerivation f g hI hfg).liftKaehlerDifferential_comp_D a

@[simp]
lemma contractDifferenceOne_smul_d (a b : A) :
    contractDifferenceOne f g hI hfg (a • KaehlerDifferential.D R A b) =
      f a * (f b - g b) := by
  rw [(contractDifferenceOne f g hI hfg).map_smulₛₗ, contractDifferenceOne_d]
  rfl

private def contractionAlternating :
    letI : Module A Ω[B⁄R] := Module.compHom Ω[B⁄R] f.toRingHom
    Ω[A⁄R] [⋀^Fin 2]→ₗ[A] Ω[B⁄R] := by
  letI : Module A Ω[B⁄R] := Module.compHom Ω[B⁄R] f.toRingHom
  let c := contractDifferenceOne f g hI hfg
  let p := mapOne f
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 := Ne.symm h01
  have hcases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    rw [Fin.forall_fin_two]
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  refine
    { toFun := fun v => c (v 0) • p (v 1) - c (v 1) • p (v 0)
      map_update_add' := ?_
      map_update_smul' := ?_
      map_eq_zero_of_eq' := ?_ }
  · intro _ v i x y
    rcases hcases i with rfl | rfl <;>
      simp only [Function.update_self, Function.update_of_ne h01, Function.update_of_ne h10,
        c.map_add, p.map_add, add_smul, smul_add] <;> abel
  · intro _ v i a x
    change _ = f.toRingHom a • (c (Function.update v i x 0) • p (Function.update v i x 1) -
      c (Function.update v i x 1) • p (Function.update v i x 0))
    rcases hcases i with rfl | rfl
    · simp only [Function.update_self, Function.update_of_ne h10]
      rw [c.map_smulₛₗ, p.map_smulₛₗ, smul_eq_mul, mul_smul, smul_sub,
        smul_comm (c (v 1)) (f.toRingHom a)]
    · simp only [Function.update_self, Function.update_of_ne h01]
      rw [c.map_smulₛₗ, p.map_smulₛₗ, smul_eq_mul, mul_smul, smul_sub,
        smul_comm (c (v 0)) (f.toRingHom a)]
  · intro v i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all

/-- The degree-two contraction is the alternating extension of the two terms
obtained by contracting either one-form in a wedge. -/
def contractDifferenceTwo : Two R A →ₛₗ[f.toRingHom] Ω[B⁄R] := by
  letI : Module A Ω[B⁄R] := Module.compHom Ω[B⁄R] f.toRingHom
  let F := exteriorPower.alternatingMapLinearEquiv (contractionAlternating f g hI hfg)
  exact { F.toAddMonoidHom with map_smul' := F.map_smul }

@[simp]
lemma contractDifferenceTwo_wedge (x y : Ω[A⁄R]) :
    contractDifferenceTwo f g hI hfg (wedge x y) =
      contractDifferenceOne f g hI hfg x • mapOne f y -
        contractDifferenceOne f g hI hfg y • mapOne f x := by
  let : Module A Ω[B⁄R] := Module.compHom Ω[B⁄R] f.toRingHom
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (contractionAlternating f g hI hfg) ![x, y]

/-- The difference of pullbacks on one-forms is the sum of the differential of
contraction and the contraction of the exterior differential. -/
theorem mapOne_sub_eq_d_contract_add_contract_d (ω : Ω[A⁄R]) :
    mapOne f ω - mapOne g ω = dZero R B (contractDifferenceOne f g hI hfg ω) +
      contractDifferenceTwo f g hI hfg (dOne R A ω) := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, contractDifferenceOne_smul_d, dOne_smul_d,
      contractDifferenceTwo_wedge, contractDifferenceOne_d, contractDifferenceOne_d,
      (mapOne f).map_smulₛₗ, (mapOne g).map_smulₛₗ,
      mapOne_d, mapOne_d, mapOne_d]
    change f a • KaehlerDifferential.D R B (f b) - g a • KaehlerDifferential.D R B (g b) =
      KaehlerDifferential.D R B (f a * (f b - g b)) +
        ((f a - g a) • KaehlerDifferential.D R B (f b) -
          (f b - g b) • KaehlerDifferential.D R B (f a))
    rw [Derivation.leibniz]
    have h : (f a - g a) • KaehlerDifferential.D R B (f b) =
        (f a - g a) • KaehlerDifferential.D R B (g b) := by
      rw [← sub_eq_zero, ← smul_sub, ← map_sub]
      exact smul_dZero_eq_zero hI (hfg a) (hfg b)
    rw [map_sub, h]
    simp only [smul_sub, sub_smul]
    abel
  | add x y hx hy =>
    simp only [map_add]
    rw [add_sub_add_comm, hx, hy]
    abel

/-- On closed one-forms, the difference of the pullbacks is exact, with
primitive given by contracting against the difference derivation. -/
theorem mapOne_sub_eq_d_contract_of_closed {ω : Ω[A⁄R]} (hω : dOne R A ω = 0) :
    mapOne f ω - mapOne g ω = dZero R B (contractDifferenceOne f g hI hfg ω) := by
  rw [mapOne_sub_eq_d_contract_add_contract_d f g hI hfg, hω, map_zero, add_zero]

/-- The contraction is valued in the extension of the base ideal. -/
lemma contractDifferenceOne_mem (ω : Ω[A⁄R]) :
    contractDifferenceOne f g hI hfg ω ∈ I.map (algebraMap R B) := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, contractDifferenceOne_smul_d]
    exact Ideal.mul_mem_left _ _ (hfg b)
  | add x y hx hy =>
    simp only [map_add]
    exact Ideal.add_mem _ hx hy

/-- The value of the contraction respects equalities of the two pullback maps. -/
lemma contractDifferenceOne_congr (f' g' : A →ₐ[R] B)
    (hf'g' : ∀ a, f' a - g' a ∈ I.map (algebraMap R B))
    (hf : f = f') (hg : g = g') (ω : Ω[A⁄R]) :
    contractDifferenceOne f g hI hfg ω = contractDifferenceOne f' g' hI hf'g' ω := by
  subst f'
  subst g'
  rfl

/-- Difference contractions telescope for three lifts of the same algebra map. -/
lemma contractDifferenceOne_telescopes (h : A →ₐ[R] B)
    (hgh : ∀ a, g a - h a ∈ I.map (algebraMap R B))
    (hfh : ∀ a, f a - h a ∈ I.map (algebraMap R B)) (ω : Ω[A⁄R]) :
    contractDifferenceOne f g hI hfg ω + contractDifferenceOne g h hI hgh ω =
      contractDifferenceOne f h hI hfh ω := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul]
    simp only [contractDifferenceOne_smul_d]
    linear_combination -extendedIdeal_mul_eq_zero hI (hfg a) (hgh b)
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]

/-- The contraction of the difference of a map with itself is zero. -/
lemma contractDifferenceOne_self
    (hff : ∀ a, f a - f a ∈ I.map (algebraMap R B)) (ω : Ω[A⁄R]) :
    contractDifferenceOne f f hI hff ω = 0 := by
  have h := contractDifferenceOne_telescopes f f hI hff f hff hff ω
  exact add_right_cancel (h.trans (zero_add _).symm)

section Composition

variable {C : Type u} [CommRing C] [Algebra R C]

/-- Applying an algebra map to an element of the extended ideal preserves
membership in the extension of the same base ideal. -/
lemma map_mem_extendedIdeal (v : B →ₐ[R] C) {x : B} (hx : x ∈ I.map (algebraMap R B)) :
    v x ∈ I.map (algebraMap R C) := by
  have heq : v.toRingHom.comp (algebraMap R B) = algebraMap R C :=
    RingHom.ext (fun r => v.commutes r)
  have hm := Ideal.mem_map_of_mem v.toRingHom hx
  rwa [Ideal.map_map, heq] at hm

/-- Precomposition of a difference contraction pulls back the one-form. -/
lemma contractDifferenceOne_precomp (v : C →ₐ[R] A)
    (hcomp : ∀ a, (f.comp v) a - (g.comp v) a ∈ I.map (algebraMap R B)) (ω : Ω[C⁄R]) :
    contractDifferenceOne (f.comp v) (g.comp v) hI hcomp ω =
      contractDifferenceOne f g hI hfg (mapOne v ω) := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R C ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, contractDifferenceOne_smul_d,
      (mapOne v).map_smulₛₗ, mapOne_d, contractDifferenceOne_smul_d]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

/-- Postcomposition of a difference contraction applies the map to its value. -/
lemma contractDifferenceOne_postcomp (v : B →ₐ[R] C)
    (hcomp : ∀ a, (v.comp f) a - (v.comp g) a ∈ I.map (algebraMap R C)) (ω : Ω[A⁄R]) :
    contractDifferenceOne (v.comp f) (v.comp g) hI hcomp ω =
      v (contractDifferenceOne f g hI hfg ω) := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, contractDifferenceOne_smul_d,
      contractDifferenceOne_smul_d, map_mul, map_sub]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

end Composition

end Langlands.AlgebraicGeometry.AffineCechDeRham.RelativeForms
