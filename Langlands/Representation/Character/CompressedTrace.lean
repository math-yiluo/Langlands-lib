import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Simple modules distinguished by finite-dimensional compressions -/

noncomputable section

set_option autoImplicit false

namespace Langlands.CharacterSeparation

variable {k : Type*} [Field k] {M P : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup P] [Module k P]

/-- Take the trace of an endomorphism after insertion and projection through a
finite-dimensional vector space. -/
def compressedTrace [FiniteDimensional k P]
    (i : P →ₗ[k] M) (p : M →ₗ[k] P) (T : Module.End k M) : k :=
  LinearMap.trace k P (p.comp (T.comp i))

variable {A : Type*} [Ring A] [Algebra k A]
  [Module A M] [IsScalarTower k A M] [IsSimpleModule A M]
  {N Q : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [IsSimpleModule A N] [AddCommGroup Q] [Module k Q]

omit [Algebra k A] [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k A N] in
private theorem exists_smul_eq_on_finsets_of_not_equiv
    (hne : ¬ Nonempty (M ≃ₗ[A] N)) (s : Finset M) (t : Finset N) :
    ∃ a : A, (∀ m ∈ s, a • m = m) ∧ ∀ n ∈ t, a • n = 0 := by
  have hMN (f : M →ₗ[A] N) : f = 0 :=
    f.bijective_or_eq_zero.resolve_left fun hf => hne ⟨LinearEquiv.ofBijective f hf⟩
  have hNM (f : N →ₗ[A] M) : f = 0 :=
    f.bijective_or_eq_zero.resolve_left fun hf => hne ⟨(LinearEquiv.ofBijective f hf).symm⟩
  have hsemi : IsSemisimpleModule A (M × N) := by
    have hsup := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A M N))
      (IsSemisimpleModule.range (LinearMap.inr A M N))
    rw [LinearMap.sup_range_inl_inr] at hsup
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  have hfst (f : Module.End A (M × N)) (n : N) : (f (0, n)).1 = 0 :=
    LinearMap.congr_fun (hNM ((LinearMap.fst A M N).comp (f.comp (LinearMap.inr A M N)))) n
  have hsnd (f : Module.End A (M × N)) (m : M) : (f (m, 0)).2 = 0 :=
    LinearMap.congr_fun (hMN ((LinearMap.snd A M N).comp (f.comp (LinearMap.inl A M N)))) m
  let p : Module.End (Module.End A (M × N)) (M × N) :=
    { toFun := fun x => (x.1, 0)
      map_add' := fun _ _ => by simp
      map_smul' := fun f x => by
        change ((f x).1, (0 : N)) = f (x.1, 0)
        refine Prod.ext ?_ (hsnd f x.1).symm
        have hx : x = (x.1, 0) + (0, x.2) := by simp
        conv_lhs => rw [hx]
        rw [map_add, Prod.fst_add, hfst, add_zero] }
  classical
  obtain ⟨a, ha⟩ := jacobson_density p
    ((s.image fun m => ((m, 0) : M × N)) ∪ (t.image fun n => ((0, n) : M × N)))
  refine ⟨a, fun m hm => ?_, fun n hn => ?_⟩
  · exact (congrArg Prod.fst (ha (m, 0) (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ hm)))).symm
  · exact (congrArg Prod.snd (ha (0, n) (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ hn)))).symm

/-- Equality of all compressed traces on two simple modules forces equivalence
when the first finite-dimensional compression has nonzero trace on the identity. -/
theorem nonempty_linearEquiv_of_compressedTrace_eq
    [FiniteDimensional k P] [FiniteDimensional k Q]
    (i : P →ₗ[k] M) (p : M →ₗ[k] P) (j : Q →ₗ[k] N) (q : N →ₗ[k] Q)
    (hp : compressedTrace i p LinearMap.id ≠ 0)
    (h : ∀ a : A, compressedTrace i p (DistribSMul.toLinearMap k M a) =
      compressedTrace j q (DistribSMul.toLinearMap k N a)) : Nonempty (M ≃ₗ[A] N) := by
  by_contra hne
  classical
  let b := Module.finBasis k P
  let c := Module.finBasis k Q
  obtain ⟨a, ha, hc⟩ := exists_smul_eq_on_finsets_of_not_equiv hne
    (Finset.univ.image fun k => i (b k)) (Finset.univ.image fun k => j (c k))
  have hb' : (DistribSMul.toLinearMap k M a).comp i = i :=
    b.ext fun k => ha _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have hc' : (DistribSMul.toLinearMap k N a).comp j = 0 :=
    c.ext fun k => hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  apply hp
  simpa only [compressedTrace, hb', hc', LinearMap.comp_zero, map_zero, LinearMap.id_comp]
    using h a

end Langlands.CharacterSeparation
