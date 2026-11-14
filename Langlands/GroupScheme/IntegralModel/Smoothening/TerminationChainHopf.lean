import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationChain

/-! # Hopf algebra structure on the members of the smoothening sequence

A subalgebra `S` of `B = integralFunctions R K A` that contains the image of `A`, whose
comultiplication lands in the span of `S ⊗ S` and which is stable under the antipode, inherits a
Hopf algebra structure from `B`. The axioms are checked on the image of `A`, as for `B` itself in
`Smoothening.Hopf`. This applies to every member of the smoothening sequence. -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing Coalgebra Bialgebra TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {A : Type u} [CommRing A] [HopfAlgebra R A]

section SubHopf

variable (S : Subalgebra R (integralFunctions R K A))

instance subIsTorsionFree : Module.IsTorsionFree R S :=
  Subtype.val_injective.moduleIsTorsionFree _ fun _ _ => rfl

instance subFlat : Module.Flat R S := by
  have h : Module.Flat R S := (IsDedekindDomain.flat_iff_torsion_eq_bot (R := R) (M := S)).mpr
    ((Submodule.isTorsionFree_iff_torsion_eq_bot (R := R) (M := S)).mp (subIsTorsionFree S))
  exact h

/-- The inclusion of `A`. -/
def inclSub (hS : (incl R K A).range ≤ S) : A →ₐ[R] S :=
  (incl R K A).codRestrict S fun a => hS (AlgHom.mem_range_self _ a)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem val_inclSub (hS : (incl R K A).range ≤ S) (a : A) :
    ((inclSub S hS a : S) : integralFunctions R K A) = incl R K A a := rfl

omit [IsDiscreteValuationRing R] in
/-- Algebra maps from `S` to a flat algebra are determined on the image of `A`. -/
theorem algHom_ext_sub (hS : (incl R K A).range ≤ S) {D : Type u} [Semiring D] [Algebra R D]
    [Module.Flat R D] {g₁ g₂ : S →ₐ[R] D}
    (h : g₁.comp (inclSub S hS) = g₂.comp (inclSub S hS)) : g₁ = g₂ := by
  ext s
  obtain ⟨r, a, hr, hra⟩ :=
    exists_smul_eq_one_tmul K A (((s : integralFunctions R K A)) : K ⊗[R] A)
  have hs : r • s = inclSub S hS a := by
    apply Subtype.ext
    apply Subtype.ext
    rw [val_inclSub, coe_incl, ← hra]
    rfl
  have h1 : r • g₁ s = r • g₂ s := by
    rw [← map_smul, ← map_smul, hs, ← AlgHom.comp_apply, h, AlgHom.comp_apply]
  exact smul_right_injective D hr h1

/-- The inclusion `S ⊗ S → B ⊗ B`. -/
abbrev tensorVal : S ⊗[R] S →ₐ[R] integralFunctions R K A ⊗[R] integralFunctions R K A :=
  Algebra.TensorProduct.map S.val S.val

theorem tensorVal_injective : Function.Injective (tensorVal S) := by
  have : (tensorVal S).toLinearMap = TensorProduct.map S.val.toLinearMap S.val.toLinearMap := rfl
  intro x y hxy
  exact TensorProduct.map_injective_of_flat_flat S.val.toLinearMap S.val.toLinearMap
    Subtype.val_injective Subtype.val_injective hxy

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem pureSpan_le_range :
    pureSpan R K A S S ≤ (tensorVal S).toLinearMap.range := by
  rw [pureSpan, Submodule.span_le]
  rintro _ ⟨c, hc, c', hc', rfl⟩
  exact ⟨(⟨c, hc⟩ : S) ⊗ₜ (⟨c', hc'⟩ : S), rfl⟩

section Struct

variable (hS : (incl R K A).range ≤ S)
  (hcomul : ∀ s ∈ S, comulAlgHom R (integralFunctions R K A) s ∈ pureSpan R K A S S)
  (hanti : ∀ s ∈ S, antipodeInt s ∈ S)

/-- The comultiplication of `S`. -/
def comulSub : S →ₐ[R] S ⊗[R] S :=
  (AlgEquiv.ofInjective (tensorVal S) (tensorVal_injective S)).symm.toAlgHom.comp
    (((comulAlgHom R (integralFunctions R K A)).comp S.val).codRestrict (tensorVal S).range
      (fun s => by
        obtain ⟨x, hx⟩ := pureSpan_le_range S (hcomul s s.2)
        exact ⟨x, hx⟩))

theorem tensorVal_comulSub (s : S) :
    tensorVal S (comulSub S hcomul s) =
      comulAlgHom R (integralFunctions R K A) (s : integralFunctions R K A) := by
  have h := (AlgEquiv.ofInjective (tensorVal S) (tensorVal_injective S)).apply_symm_apply
    ⟨comulAlgHom R (integralFunctions R K A) (s : integralFunctions R K A), by
      obtain ⟨x, hx⟩ := pureSpan_le_range S (hcomul s s.2)
      exact ⟨x, hx⟩⟩
  exact congrArg Subtype.val h

/-- The counit of `S`. -/
def counitSub : S →ₐ[R] R := (counitAlgHom R (integralFunctions R K A)).comp S.val

/-- The antipode of `S`. -/
def antipodeSub : S →ₐ[R] S := (antipodeInt.comp S.val).codRestrict S fun s => hanti s s.2

theorem comulSub_comp_inclSub :
    (comulSub S hcomul).comp (inclSub S hS) =
      (Algebra.TensorProduct.map (inclSub S hS) (inclSub S hS)).comp (comulAlgHom R A) := by
  apply AlgHom.ext
  intro a
  apply tensorVal_injective S
  rw [AlgHom.comp_apply, tensorVal_comulSub, val_inclSub, comulAlgHom_int, comulInt_incl,
    AlgHom.comp_apply, ← AlgHom.comp_apply (tensorVal S), ← Algebra.TensorProduct.map_comp]
  rfl

theorem comulSub_comp_inclSub' :
    (comulSub S hcomul).toLinearMap ∘ₗ (inclSub S hS).toLinearMap =
      TensorProduct.map (inclSub S hS).toLinearMap (inclSub S hS).toLinearMap ∘ₗ comul :=
  congrArg AlgHom.toLinearMap (comulSub_comp_inclSub S hS hcomul)

theorem counitSub_comp_inclSub :
    (counitSub S).comp (inclSub S hS) = counitAlgHom R A := by
  rw [counitSub, AlgHom.comp_assoc, counitAlgHom_int]
  exact counitInt_comp_incl

theorem counitSub_comp_inclSub' :
    (counitSub S).toLinearMap ∘ₗ (inclSub S hS).toLinearMap = counit :=
  congrArg AlgHom.toLinearMap (counitSub_comp_inclSub S hS)

theorem antipodeSub_inclSub (a : A) :
    antipodeSub S hanti (inclSub S hS a) = inclSub S hS (HopfAlgebra.antipode R a) := by
  apply Subtype.ext
  change antipodeInt (incl R K A a) = _
  rw [antipodeInt_incl]
  rfl

/-- The bialgebra structure of `S`. -/
abbrev bialgSub : Bialgebra R S := by
  refine .ofAlgHom (comulSub S hcomul) (counitSub S) ?_ ?_ ?_
  · apply algHom_ext_sub S hS
    apply AlgHom.toLinearMap_injective
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comulSub_comp_inclSub' S hS hcomul]
    simp [coassoc_simps]
  · apply algHom_ext_sub S hS
    apply AlgHom.toLinearMap_injective
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comulSub_comp_inclSub' S hS hcomul, counitSub_comp_inclSub' S hS]
    rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · apply algHom_ext_sub S hS
    apply AlgHom.toLinearMap_injective
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comulSub_comp_inclSub' S hS hcomul, counitSub_comp_inclSub' S hS]
    rw [CoassocSimps.map_counit_comp_comul_right]; rfl

/-- The Hopf algebra structure of `S`. -/
abbrev hopfSub : HopfAlgebra R S := by
  letI := bialgSub S hS hcomul
  refine .ofAlgHom (antipodeSub S hanti) ?_ ?_
  · apply algHom_ext_sub S hS
    apply AlgHom.ext
    intro a
    have h := AlgHom.congr_fun (lift_antipodeAlgHom_comp_comul (R := R) (A := A)) a
    simp only [AlgHom.comp_apply] at h
    change Algebra.TensorProduct.lift (antipodeSub S hanti) (.id R S) (fun _ _ => .all _ _)
        (comulSub S hcomul (inclSub S hS a)) =
      (Algebra.ofId R S) (counitSub S (inclSub S hS a))
    rw [← AlgHom.comp_apply (comulSub S hcomul), comulSub_comp_inclSub, AlgHom.comp_apply,
      ← AlgHom.comp_apply (counitSub S), counitSub_comp_inclSub]
    have key : ∀ x : A ⊗[R] A,
        Algebra.TensorProduct.lift (antipodeSub S hanti) (.id R S) (fun _ _ => .all _ _)
          (Algebra.TensorProduct.map (inclSub S hS) (inclSub S hS) x) =
        inclSub S hS (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (.id R A)
          (fun _ _ => .all _ _) x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul x y => simp [antipodeSub_inclSub S hS hanti]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    rw [key, h]
    simp
  · apply algHom_ext_sub S hS
    apply AlgHom.ext
    intro a
    have h := AlgHom.congr_fun (lift_id_antipodeAlgHom_comp_comul (R := R) (A := A)) a
    simp only [AlgHom.comp_apply] at h
    change Algebra.TensorProduct.lift (.id R S) (antipodeSub S hanti) (fun _ _ => .all _ _)
        (comulSub S hcomul (inclSub S hS a)) =
      (Algebra.ofId R S) (counitSub S (inclSub S hS a))
    rw [← AlgHom.comp_apply (comulSub S hcomul), comulSub_comp_inclSub, AlgHom.comp_apply,
      ← AlgHom.comp_apply (counitSub S), counitSub_comp_inclSub]
    have key : ∀ x : A ⊗[R] A,
        Algebra.TensorProduct.lift (.id R S) (antipodeSub S hanti) (fun _ _ => .all _ _)
          (Algebra.TensorProduct.map (inclSub S hS) (inclSub S hS) x) =
        inclSub S hS (Algebra.TensorProduct.lift (.id R A) (HopfAlgebra.antipodeAlgHom R A)
          (fun _ _ => .all _ _) x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul x y => simp [antipodeSub_inclSub S hS hanti]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    rw [key, h]
    simp

end Struct

end SubHopf

/-- The Hopf algebra structure on a member of the smoothening sequence. -/
abbrev chainHopf {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) : HopfAlgebra R (chain R K A ϖ n) :=
  hopfSub (chain R K A ϖ n) (range_incl_le_chain ϖ n)
    (fun _ hs => comul_mem_pureSpan hϖ n hs) (fun _ hs => antipodeInt_mem n hs)


end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
