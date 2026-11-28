import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Langlands.LinearAlgebra.JordanChevalleyFunctoriality
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.RingTheory.Jacobson.Ideal

/-! # Semisimple centralizers in finite-dimensional algebras -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Algebra Module Polynomial

universe u v

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]
  [FiniteDimensional F A]

local notation "C(" S ")" => Subalgebra.centralizer F ({S} : Set A)

omit [FiniteDimensional F A] in
private theorem centralizer_toSubmodule_eq_ker (S : A) :
    (C(S)).toSubmodule = (adjointEndomorphism F S).ker := by
  ext X
  simp [Subalgebra.mem_centralizer_iff, sub_eq_zero]

/-- A noncentral element has a centralizer of strictly smaller dimension. -/
theorem finrank_centralizer_lt {S : A} (hS : S ∉ Subalgebra.center F A) :
    finrank F (C(S)) < finrank F A := by
  change finrank F (C(S)).toSubmodule < finrank F A
  apply Submodule.finrank_lt
  intro h
  apply hS
  refine Subalgebra.mem_center_iff.mpr fun X => ?_
  have hX : X ∈ (C(S)).toSubmodule := h.symm ▸ Submodule.mem_top
  exact ((Subalgebra.mem_centralizer_iff F).mp hX S (Set.mem_singleton _)).symm

variable [PerfectField F]

/-- The regular representation gives a semisimple part of `X` that is a polynomial in `X`. -/
theorem exists_semisimple_part (X : A) :
    ∃ S : A, S ∈ Algebra.adjoin F ({X} : Set A) ∧
      (Algebra.lmul F A S).IsSemisimple ∧ IsNilpotent (X - S) ∧ Commute S X := by
  let L := Algebra.lmul F A
  obtain ⟨hm, hn, hs, hc⟩ := Langlands.LinearAlgebra.jordanSemisimplePart_properties (L X)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨q, hq⟩ := hm
  let S := aeval X q
  have hS : L S = Langlands.LinearAlgebra.jordanSemisimplePart (L X) := by
    rw [show L S = aeval (L X) q from (aeval_algHom_apply L X q).symm]
    exact hq
  have hD : L (X - S) = Langlands.LinearAlgebra.jordanNilpotentPart (L X) := by
    rw [map_sub, hS, Langlands.LinearAlgebra.jordanNilpotentPart]
  refine ⟨S, ?_, hS.symm ▸ hs, ?_, ?_⟩
  · rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  · obtain ⟨n, hn⟩ := hn
    refine ⟨n, Algebra.lmul_injective (R := F) (A := A) ?_⟩
    change L ((X - S) ^ n) = L 0
    rw [map_pow, hD, hn, map_zero]
  · have hDX : Commute (X - S) S := by
      apply show (X - S) * S = S * (X - S) from ?_
      apply Algebra.lmul_injective (R := F) (A := A)
      change L ((X - S) * S) = L (S * (X - S))
      rw [map_mul, map_mul, hD, hS, hc.eq]
    have h := (hDX.add_left (Commute.refl S)).symm
    rwa [sub_add_cancel] at h

/-- The commutator with a semisimple element is a semisimple endomorphism. -/
theorem isSemisimple_adjointEndomorphism {S : A} (hS : (Algebra.lmul F A S).IsSemisimple) :
    Module.End.IsSemisimple (adjointEndomorphism F S) := by
  let p := minpoly F (Algebra.lmul F A S)
  have hp : aeval S p = 0 := by
    apply Algebra.lmul_injective (R := F) (A := A)
    rw [← aeval_algHom_apply, map_zero]
    exact minpoly.aeval F _
  let e : Aᵐᵒᵖ ≃ₗ[F] A := (MulOpposite.opLinearEquiv (R := F) (M := A)).symm
  let R := (e.conjAlgEquiv F).toAlgHom.comp (Algebra.lmul F Aᵐᵒᵖ)
  have hr : Module.End.IsSemisimple (LinearMap.mulRight F S) := by
    change (R (MulOpposite.op S)).IsSemisimple
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hS.minpoly_squarefree
    rw [aeval_algHom_apply, aeval_op_apply, hp, MulOpposite.op_zero, map_zero]
  have hc : Commute (LinearMap.mulLeft F S) (LinearMap.mulRight F S) := by
    apply LinearMap.ext
    intro X
    exact (mul_assoc S X S).symm
  exact Module.End.IsSemisimple.sub_of_commute hc hS hr

omit [PerfectField F] in
private theorem isCompl_ker_range {d : End F A} (hd : d.IsSemisimple) :
    IsCompl d.ker d.range := by
  have hk : d.ker ∈ Module.End.invtSubmodule d := by
    rw [Module.End.mem_invtSubmodule]
    intro X hX
    change d X ∈ d.ker
    rw [LinearMap.mem_ker.mp hX]
    exact Submodule.zero_mem _
  obtain ⟨Q, hQ, hc⟩ := Module.End.isSemisimple_iff.mp hd d.ker hk
  have hQ' := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem d).mp hQ
  let dQ : End F Q := d.restrict hQ'
  have hinj : Function.Injective dQ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _
      (congrArg Subtype.val (LinearMap.mem_ker.mp hx)) x.property)
  have hsurj : Function.Surjective dQ := LinearMap.injective_iff_surjective.mp hinj
  have hr : d.range = Q := by
    apply le_antisymm
    · rintro _ ⟨X, rfl⟩
      obtain ⟨⟨p, q⟩, hpq⟩ := (d.ker.prodEquivOfIsCompl Q hc).surjective X
      change (p : A) + (q : A) = X at hpq
      rw [← hpq, map_add, LinearMap.mem_ker.mp p.property, zero_add]
      exact (dQ q).property
    · intro X hX
      obtain ⟨q, hq⟩ := hsurj ⟨X, hX⟩
      exact ⟨q, congrArg Subtype.val hq⟩
  exact hr ▸ hc

/-- The semisimple centralizer and the image of the adjoint endomorphism are complementary. -/
theorem isCompl_centralizer_range_adjoint {S : A} (hS : (Algebra.lmul F A S).IsSemisimple) :
    IsCompl (C(S)).toSubmodule (adjointEndomorphism F S).range := by
  rw [centralizer_toSubmodule_eq_ker]
  exact isCompl_ker_range (isSemisimple_adjointEndomorphism hS)

omit [PerfectField F] in
private theorem isSemisimpleRing_of_mul_mul_eq_self {B : Type v} [Ring B] [IsArtinianRing B]
    (hB : ∀ x : B, ∃ y : B, x * y * x = x) : IsSemisimpleRing B := by
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, ← Ideal.jacobson_bot]
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Ideal.mem_bot.mpr
  obtain ⟨y, hy⟩ := hB x
  have hmem : (1 - x * y) - 1 ∈ (⊥ : Ideal B).jacobson := by
    rw [sub_right_comm, sub_self, zero_sub]
    exact (⊥ : Ideal B).jacobson.neg_mem ((⊥ : Ideal B).jacobson.mul_mem_right y hx)
  obtain ⟨z, hz⟩ := Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson _ hmem
  have hz' := sub_eq_zero.mp (Ideal.mem_bot.mp hz)
  calc
    x = (z * (1 - x * y)) * x := by rw [hz', one_mul]
    _ = 0 := by rw [mul_assoc, sub_mul, one_mul, hy, sub_self, mul_zero]

/-- The centralizer of a semisimple element of a finite-dimensional semisimple algebra is
semisimple. The adjoint range is stable under left and right centralizer multiplication, so
projecting an inner inverse to the centralizer preserves the inner-inverse identity. -/
theorem isSemisimpleRing_centralizer_of_isSemisimple [IsSemisimpleRing A] {S : A}
    (hS : (Algebra.lmul F A S).IsSemisimple) : IsSemisimpleRing (C(S)) := by
  let B := C(S)
  let d := adjointEndomorphism F S
  have hc := isCompl_centralizer_range_adjoint hS
  let _ : IsArtinianRing B := IsArtinianRing.of_finite F B
  apply isSemisimpleRing_of_mul_mul_eq_self
  intro x
  let X := (x : A)
  obtain ⟨e, he, heq⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {X})
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (heq ▸ Ideal.mem_span_singleton_self e)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (heq ▸ Ideal.mem_span_singleton_self X)
  have hXa : X * a * X = X := by
    rw [mul_assoc, ha, ← hb, mul_assoc, he.eq]
  obtain ⟨⟨y, z⟩, hyz⟩ := (B.toSubmodule.prodEquivOfIsCompl d.range hc).surjective a
  change (y : A) + (z : A) = a at hyz
  refine ⟨y, Subtype.ext ?_⟩
  change X * (y : A) * X = X
  have hE : X - X * (y : A) * X = X * (z : A) * X := by
    calc
      _ = X * a * X - X * (y : A) * X :=
        congrArg (fun w => w - X * (y : A) * X) hXa.symm
      _ = _ := by rw [← hyz]; noncomm_ring
  have hI : X - X * (y : A) * X ∈ B.toSubmodule :=
    B.sub_mem x.property (B.mul_mem (B.mul_mem x.property y.property) x.property)
  have hR : X * (z : A) * X ∈ d.range := by
    obtain ⟨w, hw⟩ := z.property
    have hSX : S * X = X * S := (Subalgebra.mem_centralizer_iff F).mp x.property S
      (Set.mem_singleton _)
    refine ⟨X * w * X, ?_⟩
    rw [← hw]
    change S * (X * w * X) - X * w * X * S = X * (S * w - w * S) * X
    calc
      _ = (S * X) * w * X - X * w * (X * S) := by noncomm_ring
      _ = (X * S) * w * X - X * w * (S * X) :=
        congrArg₂ (· - ·) (by rw [hSX]) (by rw [hSX])
      _ = _ := by noncomm_ring
  exact (sub_eq_zero.mp (Submodule.disjoint_def.mp hc.disjoint _ hI (hE.symm ▸ hR))).symm

/-- Algebraic centralizer properties used in semisimple descent. -/
def SemisimpleElementCentralizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [PerfectField F] (A : Type v) [Ring A] [Algebra F A]
    [FiniteDimensional F A] [IsSemisimpleRing A] (S : A) (_ : (Algebra.lmul F A S).IsSemisimple),
    IsSemisimpleRing (Subalgebra.centralizer F ({S} : Set A)) ∧
    IsCompl (Subalgebra.centralizer F ({S} : Set A)).toSubmodule (adjointEndomorphism F S).range ∧
    (S ∉ Subalgebra.center F A → finrank F (Subalgebra.centralizer F ({S} : Set A)) < finrank F A)

theorem semisimpleElementCentralizer : SemisimpleElementCentralizerStatement.{u, v} := by
  intro F _ _ A _ _ _ _ S hS
  exact ⟨isSemisimpleRing_centralizer_of_isSemisimple hS,
    isCompl_centralizer_range_adjoint hS, finrank_centralizer_lt⟩

end Langlands.HarmonicAnalysis.UnitConjugation
