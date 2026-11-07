import Langlands.GroupTheory.CocycleSplittingClass
import Langlands.Cohomology.Tate.NormCoinvariants

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

variable {G A : Type u} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A]

local instance invariantsAdditiveModule : Module Scalars.{u} (Additive A) := ULift.module

local instance invariantsActionModule :
    Module Scalars.{u} (Rep.ofMulDistribMulAction G A) := ULift.module

/-- A translation-invariant integral augmentation vector is zero. -/
lemma ideal_invariant_eq_zero (f : Ideal G)
    (hf : ∀ g : G, (ideal G).ρ g f = f) : f = 0 := by
  have hx (x : G) : f.val x = f.val 1 := by
    have h := congrArg (fun y : Ideal G => y.val 1) (hf x)
    simpa only [ideal_apply, one_mul] using h
  have hs : coordinateSum G f.val = 0 := f.property
  have hn : (Fintype.card G : Scalars.{u}) * f.val 1 = 0 := by
    simpa only [coordinateSum_apply, hx, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using hs
  have hn' : (Fintype.card G : ℤ) * (f.val 1).down = 0 :=
    congrArg ULift.down hn
  have hc : (Fintype.card G : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hz : f.val 1 = 0 := ULift.ext _ _ ((mul_eq_zero.mp hn').resolve_left hc)
  apply Subtype.ext
  funext x
  change f.val x = 0
  rw [hx, hz]

variable (c : NormalizedTwoCocycle G A)

lemma splitting_invariant_snd_eq_zero (x : (splitting c).ρ.invariants) :
    x.val.2 = 0 := by
  apply ideal_invariant_eq_zero
  intro g
  exact congrArg Prod.snd (x.property g)

lemma splitting_invariant_fst (x : (splitting c).ρ.invariants) (g : G) :
    coefficientAction g x.val.1 = x.val.1 := by
  have h := congrArg Prod.fst (x.property g)
  change coefficientAction g x.val.1 + twist c g x.val.2.val = x.val.1 at h
  rw [splitting_invariant_snd_eq_zero c x, Submodule.coe_zero, map_zero, add_zero] at h
  exact h

/-- The actual invariant vectors of the splitting representation are precisely
the coefficient invariants, via the first coordinate. -/
def splittingInvariantsEquiv :
    (splitting c).ρ.invariants ≃ₗ[Scalars.{u}]
      (coefficientRepresentation G A).ρ.invariants where
  toFun x := ⟨x.val.1, splitting_invariant_fst c x⟩
  invFun a := ⟨(a.val, 0), by
    intro g
    change (coefficientAction (A := A) g (show Additive A from a.val) + twist c g 0,
      (ideal G).ρ g 0) = ((show Additive A from a.val), 0)
    rw [map_zero, map_zero, add_zero]
    exact Prod.ext (a.property g) rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (splitting_invariant_snd_eq_zero c x).symm
  right_inv a := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] lemma splittingInvariantsEquiv_val (x : (splitting c).ρ.invariants) :
    (splittingInvariantsEquiv c x).val = x.val.1 := rfl

/-- The norm of the splitting module, with codomain its actual coefficient
invariants. -/
def splittingNorm :
    (splitting c).ρ.Coinvariants →ₗ[Scalars.{u}]
      (coefficientRepresentation G A).ρ.invariants :=
  (splittingInvariantsEquiv c).toLinearMap.comp (Tate.coinvariantNorm (splitting c))

@[simp] lemma splittingNorm_mk_val (x : splitting c) :
    (splittingNorm c (Representation.Coinvariants.mk (splitting c).ρ x)).val =
      ((splitting c).ρ.norm x).1 := rfl

/-- Cup bijectivity makes the norm from splitting coinvariants to coefficient
invariants bijective. -/
lemma splittingNorm_bijective
    (hcup : ∀ n : ℤ, Function.Bijective
      (Tate.integralH2Cup (coefficientRepresentation G A) n (cohomologyClass c))) :
    Function.Bijective (splittingNorm c) :=
  (splittingInvariantsEquiv c).bijective.comp
    (Tate.coinvariantNorm_bijective (splitting c)
      (splitting_tate_isZero c hcup (-1)) (splitting_tate_isZero c hcup 0))

end Langlands.NormalizedTwoCocycle.SplittingModule
