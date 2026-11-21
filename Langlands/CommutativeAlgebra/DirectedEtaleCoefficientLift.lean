import Mathlib.RingTheory.Etale.Basic

/-! # Infinitesimal lifts from a directed union of formally étale subalgebras -/

noncomputable section

namespace Langlands.CommutativeAlgebra

open Algebra

variable {R C A : Type*} [CommRing R] [CommRing C] [CommRing A] [Algebra R C] [Algebra R A]
variable {ι : Type*} (S : ι → Subalgebra R C) (hS : Directed (· ≤ ·) S)
variable (hC : ∀ x : C, ∃ i, x ∈ S i) (hE : ∀ i, FormallyEtale R (S i))
variable (I : Ideal A) (hI : IsNilpotent I) (g : C →ₐ[R] A ⧸ I)

private def stageLift (i : ι) : S i →ₐ[R] A :=
  let := hE i
  FormallySmooth.lift I hI (g.comp (S i).val)

private theorem stageLift_reduces (i : ι) :
    (Ideal.Quotient.mkₐ R I).comp (stageLift S hE I hI g i) = g.comp (S i).val :=
  let := hE i
  FormallySmooth.comp_lift I hI _

private theorem stageLift_inclusion {i j : ι} (hij : S i ≤ S j) :
    (stageLift S hE I hI g j).comp (Subalgebra.inclusion hij) = stageLift S hE I hI g i := by
  let := hE i
  apply FormallyUnramified.lift_unique I hI
  rw [← AlgHom.comp_assoc, stageLift_reduces, stageLift_reduces]
  rfl

private def unionLift (x : C) : A :=
  stageLift S hE I hI g (hC x).choose ⟨x, (hC x).choose_spec⟩

include hS in
private theorem unionLift_stage (i : ι) (x : S i) :
    unionLift S hC hE I hI g x = stageLift S hE I hI g i x := by
  obtain ⟨j, hi, hchosen⟩ := hS i (hC (x : C)).choose
  have h₁ := AlgHom.congr_fun (stageLift_inclusion S hE I hI g hi) x
  have h₂ := AlgHom.congr_fun (stageLift_inclusion S hE I hI g hchosen)
    (⟨x, (hC (x : C)).choose_spec⟩ : S (hC (x : C)).choose)
  exact h₂.symm.trans h₁

/-- The stage lifts glue to a map out of the whole algebra. -/
def directedEtaleLift : C →ₐ[R] A where
  toFun := unionLift S hC hE I hI g
  map_zero' := by
    obtain ⟨i, -⟩ := hC 0
    exact (unionLift_stage S hS hC hE I hI g i 0).trans (map_zero _)
  map_one' := by
    obtain ⟨i, -⟩ := hC 1
    exact (unionLift_stage S hS hC hE I hI g i 1).trans (map_one _)
  map_add' a b := by
    obtain ⟨i, hi⟩ := hC a
    obtain ⟨j, hj⟩ := hC b
    obtain ⟨k, hik, hjk⟩ := hS i j
    let a' : S k := ⟨a, hik hi⟩
    let b' : S k := ⟨b, hjk hj⟩
    exact (unionLift_stage S hS hC hE I hI g k (a' + b')).trans
      ((map_add _ a' b').trans (congrArg₂ (· + ·)
        (unionLift_stage S hS hC hE I hI g k a').symm
        (unionLift_stage S hS hC hE I hI g k b').symm))
  map_mul' a b := by
    obtain ⟨i, hi⟩ := hC a
    obtain ⟨j, hj⟩ := hC b
    obtain ⟨k, hik, hjk⟩ := hS i j
    let a' : S k := ⟨a, hik hi⟩
    let b' : S k := ⟨b, hjk hj⟩
    exact (unionLift_stage S hS hC hE I hI g k (a' * b')).trans
      ((map_mul _ a' b').trans (congrArg₂ (· * ·)
        (unionLift_stage S hS hC hE I hI g k a').symm
        (unionLift_stage S hS hC hE I hI g k b').symm))
  commutes' r := by
    obtain ⟨i, -⟩ := hC (algebraMap R C r)
    exact (unionLift_stage S hS hC hE I hI g i (algebraMap R (S i) r)).trans
      (AlgHom.commutes _ r)

/-- The glued map reduces to the given map on the actual quotient. -/
theorem directedEtaleLift_reduces :
    (Ideal.Quotient.mkₐ R I).comp (directedEtaleLift S hS hC hE I hI g) = g := by
  apply AlgHom.ext
  intro x
  obtain ⟨i, hi⟩ := hC x
  change Ideal.Quotient.mkₐ R I _ = g x
  change Ideal.Quotient.mkₐ R I (unionLift S hC hE I hI g x) = g x
  rw [unionLift_stage S hS hC hE I hI g i (⟨x, hi⟩ : S i)]
  exact AlgHom.congr_fun (stageLift_reduces S hE I hI g i) ⟨x, hi⟩

include hS hC hE in
/-- An algebra exhausted by a directed family of formally étale subalgebras
is formally étale. -/
theorem formallyEtale_of_directed_subalgebras : FormallyEtale R C := by
  apply FormallyEtale.iff_comp_bijective.mpr
  intro B _ _ J hJ
  refine ⟨?_, ?_⟩
  · intro f f' h
    apply AlgHom.ext
    intro x
    obtain ⟨i, hi⟩ := hC x
    let := hE i
    have he : f.comp (S i).val = f'.comp (S i).val := by
      apply FormallyUnramified.lift_unique J ⟨2, hJ⟩
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
    exact AlgHom.congr_fun he (⟨x, hi⟩ : S i)
  · intro f
    exact ⟨directedEtaleLift S hS hC hE J ⟨2, hJ⟩ f,
      directedEtaleLift_reduces S hS hC hE J ⟨2, hJ⟩ f⟩

end Langlands.CommutativeAlgebra
