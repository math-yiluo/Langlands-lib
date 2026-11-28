import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Base change in a degree whose outgoing differential has split image -/

noncomputable section

universe u

open TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Algebra

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

variable (g : N →ₗ[R] P) (r : P →ₗ[R] g.range) (hr : r.comp g.range.subtype = .id)

include hr in
private lemma baseChange_range_subtype_injective :
    Function.Injective (g.range.subtype.baseChange S) := by
  have h : (r.baseChange S).comp (g.range.subtype.baseChange S) = .id := by
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  exact Function.LeftInverse.injective (LinearMap.congr_fun h)

private def cyclesMap : S ⊗[R] g.ker →ₗ[S] (g.baseChange S).ker :=
  ((g.ker.subtype).baseChange S).codRestrict _ (fun x => by
    change ((g.baseChange S).comp (g.ker.subtype.baseChange S)) x = 0
    rw [← LinearMap.baseChange_comp, g.comp_ker_subtype, LinearMap.baseChange_zero,
      LinearMap.zero_apply])

/-- Scalar extension commutes with cycles when the outgoing differential
has split image and the codomain is flat. -/
def splitCyclesBaseChange [Module.Flat R P] :
    S ⊗[R] g.ker ≃ₗ[S] (g.baseChange S).ker := by
  let : Module.Flat R g.range := Module.Flat.of_retract g.range.subtype r hr
  have h : Function.Exact g.ker.subtype g.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have hi : Function.Injective (g.ker.subtype.baseChange S) :=
    LinearMap.lTensor_injective_of_exact_of_flat g.rangeRestrict
      g.surjective_rangeRestrict g.ker.subtype g.ker.injective_subtype h S
  have he : Function.Exact (g.ker.subtype.baseChange S) (g.rangeRestrict.baseChange S) :=
    lTensor_exact S h g.surjective_rangeRestrict
  let e := cyclesMap S g
  refine LinearEquiv.ofBijective e ⟨fun x y heq => hi (congrArg Subtype.val heq), ?_⟩
  intro y
  have hy : g.rangeRestrict.baseChange S y.val = 0 := by
    apply baseChange_range_subtype_injective S g r hr
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    exact y.property
  obtain ⟨x, hx⟩ := (he y.val).mp hy
  exact ⟨x, Subtype.ext hx⟩

@[simp]
lemma splitCyclesBaseChange_tmul [Module.Flat R P] (s : S) (x : g.ker) :
    (splitCyclesBaseChange S g r hr (s ⊗ₜ[R] x)).val = s ⊗ₜ[R] x.val := rfl

variable (f : M →ₗ[R] N) (hfg : g.comp f = 0)

private abbrev boundariesMap :=
  f.codRestrict g.ker (fun x => LinearMap.congr_fun hfg x)

private abbrev afterBaseChangeBoundariesMap :=
  (f.baseChange S).codRestrict (g.baseChange S).ker (fun x => by
    change ((g.baseChange S).comp (f.baseChange S)) x = 0
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero, LinearMap.zero_apply])

private abbrev cycleQuotient {A : Type u} [CommRing A] {M' N' : Type u}
    [AddCommMonoid M'] [Module A M'] [AddCommGroup N'] [Module A N']
    (d : M' →ₗ[A] N') := N' ⧸ d.range

/-- Extending scalars commutes with the quotient of cycles by boundaries
when the outgoing differential has split image in a flat module. -/
def splitCohomologyBaseChange [Module.Flat R P] :
    S ⊗[R] cycleQuotient (boundariesMap g f hfg) ≃ₗ[S]
      cycleQuotient (A := S) (M' := S ⊗[R] M) (N' := ((g.baseChange S).ker : Type u))
        (afterBaseChangeBoundariesMap S g f hfg) := by
  let u := boundariesMap g f hfg
  let v := afterBaseChangeBoundariesMap S g f hfg
  let e := splitCyclesBaseChange S g r hr
  have hmap : e.toLinearMap.comp (u.baseChange S) = v := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((g.ker.subtype.baseChange S).comp (u.baseChange S)) x = f.baseChange S x
    rw [← LinearMap.baseChange_comp]
    rfl
  have hrange : (u.range.subtype.baseChange S).range = (u.baseChange S).range := by
    let x := u.range.subtype.baseChange S
    let y := u.rangeRestrict.baseChange S
    have hxy : x.comp y = u.baseChange S := by
      dsimp only [x, y]
      rw [← LinearMap.baseChange_comp]
      rfl
    rw [← hxy]
    exact (LinearMap.range_comp_of_range_eq_top x
      (LinearMap.range_eq_top.mpr (LinearMap.baseChange_surjective S u.surjective_rangeRestrict))).symm
  have hq : ((u.range.subtype.baseChange S).range).map e.toLinearMap = v.range := by
    rw [hrange, ← LinearMap.range_comp, hmap]
  exact (AlgebraTensorModule.tensorQuotientEquiv S R S u.range).trans
    (Submodule.Quotient.equiv _ _ e hq)

section Transport

variable {M' N' P' : Type u} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  [AddCommGroup P'] [Module R P']
  (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P') (hfg' : g'.comp f' = 0)
  (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N') (c : P ≃ₗ[R] P')
  (hab : b.toLinearMap.comp f = f'.comp a.toLinearMap)
  (hbc : c.toLinearMap.comp g = g'.comp b.toLinearMap)

private def cyclesEquivOfIsos : g.ker ≃ₗ[R] g'.ker := by
  have h : g.ker = g'.ker.comap b.toLinearMap := by
    ext x
    change g x = 0 ↔ g' (b x) = 0
    rw [← show c (g x) = g' (b x) from LinearMap.congr_fun hbc x]
    exact (LinearEquiv.map_eq_zero_iff c).symm
  exact (LinearEquiv.ofEq _ _ h).trans (b.ofSubmodule' g'.ker)

/-- Isomorphisms of the terms intertwining both differentials identify their
quotients of cycles by boundaries. -/
def cohomologyEquivOfIsos :
    cycleQuotient (boundariesMap g f hfg) ≃ₗ[R] cycleQuotient (boundariesMap g' f' hfg') := by
  let e := cyclesEquivOfIsos g g' b c hbc
  let u := boundariesMap g f hfg
  let v := boundariesMap g' f' hfg'
  have h : e.toLinearMap.comp u = v.comp a.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hab x
  have he : u.range.map e.toLinearMap = v.range := by
    rw [← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top _ a.range]
  exact Submodule.Quotient.equiv _ _ e he

end Transport

end Langlands.Algebra
