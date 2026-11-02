import Langlands.AlgebraicGeometry.GroupoidCoactionCounit
import Langlands.AlgebraicGeometry.GroupoidCoactionUnit

/-! # The invariant counit under detection of zero comodules -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable (hE : RingEtaleEquivalenceRelation t)
variable (hacyclic : ∀ (K : Type (max u v)) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), θK.IsAcyclic)
variable (hdetect : ∀ (K : Type (max u v)) [AddCommGroup K] [Module B K]
  (θK : GroupoidCoaction t K), Subsingleton θK.invariantSubmodule → Subsingleton K)
variable {M : Type (max u v)} [AddCommGroup M] [Module B M]
variable (θ : GroupoidCoaction t M)

include hE hacyclic hdetect in
/-- Detection of zero comodules and unit surjectivity kill the counit's kernel. -/
lemma invariantCounit_injective_of_acyclic_of_detects_zero :
    Function.Injective (invariantCounit θ) := by
  let θS := induced t θ.invariantSubmodule
  let f := invariantCounit θ
  let hf : θS.IsHom θ f := invariantCounit_isHom θ
  let θK := kernel hE θS θ f hf
  have hs := kernel_subtype_isHom hE θS θ f hf
  have hinv := invariantCounit_invariantsMap_injective θ
    (inducedUnit_surjective_of_acyclic hE hacyclic θ.invariantSubmodule)
  have hzero : ∀ k : θK.invariantSubmodule, k = 0 := by
    intro k
    let x : θS.invariantSubmodule :=
      ⟨(k : LinearMap.ker f), hs.mapsTo_invariants k.property⟩
    have hx : θS.invariantsMap θ f hf x = 0 := by
      apply Subtype.ext
      exact (k : LinearMap.ker f).property
    have hxzero : x = 0 := hinv (hx.trans (map_zero _).symm)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : θS.invariantSubmodule =>
      (a : B ⊗[invariantRing t] θ.invariantSubmodule)) hxzero
  have hKinv : Subsingleton θK.invariantSubmodule :=
    ⟨fun k l => (hzero k).trans (hzero l).symm⟩
  let : Subsingleton (LinearMap.ker f) := hdetect _ θK hKinv
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker f) 0)

include hE hacyclic hdetect in
/-- Acyclicity and detection of zero comodules kill the counit's cokernel. -/
lemma invariantCounit_surjective_of_acyclic_of_detects_zero :
    Function.Surjective (invariantCounit θ) := by
  let θS := induced t θ.invariantSubmodule
  let f := invariantCounit θ
  let hf : θS.IsHom θ f := invariantCounit_isHom θ
  let θQ := cokernel θS θ f hf
  let q : M →ₗ[B] M ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  have hq : θ.IsHom θQ q := cokernel_mkQ_isHom θS θ f hf
  have hqinv := invariantsMap_surjective hE hacyclic θ θQ q hq
    (LinearMap.range f).mkQ_surjective
  have hzero : ∀ k : θQ.invariantSubmodule, k = 0 := by
    intro k
    obtain ⟨m, hm⟩ := hqinv k
    obtain ⟨s, hs⟩ := invariantCounit_invariantsMap_surjective θ m
    apply Subtype.ext
    have hms : f (s : B ⊗[invariantRing t] θ.invariantSubmodule) = (m : M) :=
      congrArg Subtype.val hs
    calc
      (k : M ⧸ LinearMap.range f) = q (m : M) := (congrArg Subtype.val hm).symm
      _ = q (f (s : B ⊗[invariantRing t] θ.invariantSubmodule)) := congrArg q hms.symm
      _ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f s)
  have hQinv : Subsingleton θQ.invariantSubmodule :=
    ⟨fun k l => (hzero k).trans (hzero l).symm⟩
  let : Subsingleton (M ⧸ LinearMap.range f) := hdetect _ θQ hQinv
  intro m
  have hm : m ∈ LinearMap.range f :=
    (Submodule.Quotient.mk_eq_zero _).mp
      (Subsingleton.elim ((LinearMap.range f).mkQ m) 0)
  exact LinearMap.mem_range.mp hm

include hE hacyclic hdetect in
/-- Under exactness and detection of zero comodules, the canonical counit is bijective. -/
lemma invariantCounit_bijective_of_acyclic_of_detects_zero :
    Function.Bijective (invariantCounit θ) :=
  ⟨invariantCounit_injective_of_acyclic_of_detects_zero hE hacyclic hdetect θ,
    invariantCounit_surjective_of_acyclic_of_detects_zero hE hacyclic hdetect θ⟩

/-- The counit equivalence, conditional on acyclicity and detection of zero comodules. -/
noncomputable def invariantCounitLinearEquiv :
    B ⊗[invariantRing t] θ.invariantSubmodule ≃ₗ[B] M :=
  LinearEquiv.ofBijective (invariantCounit θ)
    (invariantCounit_bijective_of_acyclic_of_detects_zero hE hacyclic hdetect θ)

@[simp]
lemma invariantCounitLinearEquiv_apply
    (x : B ⊗[invariantRing t] θ.invariantSubmodule) :
    invariantCounitLinearEquiv hE hacyclic hdetect θ x = invariantCounit θ x :=
  rfl

end Langlands.AlgebraicGeometry.GroupoidCoaction
