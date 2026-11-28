import Langlands.Representation.Smooth.RenardTensorHomAdjunctionProof
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RepresentationTheory.Invariants

/-! # The multiplicity space of a representation extending a normal-subgroup type -/

noncomputable section

open Representation

namespace Langlands.BushnellKutzko.SplitTypeJacquet

variable {R : Type*} [CommRing R]
variable {G D P Q : Type*} [Group G] [Group D] [Group P] [Group Q]
variable {W V A : Type*} [AddCommGroup W] [Module R W] [AddCommGroup V] [Module R V]
  [AddCommGroup A] [Module R A]
variable (κ : Representation R G W) (π : Representation R G V) (q : G →* D)

/-- The intertwiners between the restrictions of `κ` and `π` to `ker q`, represented as the
fixed submodule for the conjugation action on `Hom_R(W,V)`. -/
abbrev MultiplicitySpace := Representation.invariants
  ((Representation.linHom κ π).comp q.ker.subtype)

/-- Identification of the fixed-submodule model with normal-subgroup intertwiners. -/
def multiplicitySpaceEquiv : MultiplicitySpace κ π q ≃ₗ[R]
    IntertwiningMap (κ.comp q.ker.subtype) (π.comp q.ker.subtype) :=
  Representation.invariantsEquivIntertwiningMap (κ.comp q.ker.subtype) (π.comp q.ker.subtype)

/-- The conjugation action on the multiplicity space, descended through the surjection `q`. -/
def multiplicityRep (hq : Function.Surjective q) : Representation R D (MultiplicitySpace κ π q) :=
  ((Representation.linHom κ π).quotientToInvariants q.ker).comp
    (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom

theorem multiplicityRep_apply (hq : Function.Surjective q) (g : G)
    (f : MultiplicitySpace κ π q) :
    (multiplicityRep κ π q hq (q g) f).val = Representation.linHom κ π g f.val := by
  have hg : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q g) =
      (g : G ⧸ q.ker) := by
    apply (QuotientGroup.quotientKerEquivOfSurjective q hq).injective
    simp only [MulEquiv.apply_symm_apply]
    rfl
  change (((Representation.linHom κ π).quotientToInvariants q.ker)
    ((QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q g)) f).val = _
  rw [hg, Representation.ofQuotient_coe_apply]
  rfl

/-- Currying for the pullback of a representation from the quotient of an intermediate group.
Here `i` has image containing the kernel of `q` and the square with `s` and `j` commutes.
The resulting intertwiner is equivariant under `Q` because `s` is surjective. -/
def multiplicityCurry (hq : Function.Surjective q) (i : P →* G) (s : P →* Q)
    (hs : Function.Surjective s) (j : Q →* D) (hj : Function.Injective j) (hsq : j.comp s = q.comp i)
    (hker : q.ker ≤ i.range) (ξ : Representation R Q A) :
    IntertwiningMap (Representation.tprod (κ.comp i) (ξ.comp s)) (π.comp i) ≃ₗ[R]
      ξ.IntertwiningMap ((multiplicityRep κ π q hq).comp j) := by
  have hsq' (p : P) : j (s p) = q (i p) := DFunLike.congr_fun hsq p
  have hsk (p : P) (hp : q (i p) = 1) : s p = 1 := by
    apply hj
    rw [hsq' p, hp, map_one]
  have hhom (p : P) (f : W →ₗ[R] V) :
      Representation.linHom (κ.comp i) (π.comp i) p f =
        Representation.linHom κ π (i p) f := by
    simp only [Representation.linHom_apply, MonoidHom.comp_apply, map_inv]
  let curry := Langlands.Renard.Smooth.TensorHom.intertwinerCurry (ξ.comp s) (κ.comp i) (π.comp i)
  let swap := Representation.TensorProduct.comm (ξ.comp s) (κ.comp i)
  let swapHom :
      IntertwiningMap (Representation.tprod (κ.comp i) (ξ.comp s)) (π.comp i) ≃ₗ[R]
        IntertwiningMap (Representation.tprod (ξ.comp s) (κ.comp i)) (π.comp i) :=
    { toFun := fun f => f.comp swap.toIntertwiningMap
      invFun := fun f => f.comp swap.symm.toIntertwiningMap
      left_inv := by
        intro f
        apply IntertwiningMap.ext
        exact LinearMap.ext fun x => congrArg f (swap.apply_symm_apply x)
      right_inv := by
        intro f
        apply IntertwiningMap.ext
        exact LinearMap.ext fun x => congrArg f (swap.symm_apply_apply x)
      map_add' := by intros; apply IntertwiningMap.ext; rfl
      map_smul' := by intros; apply IntertwiningMap.ext; rfl }
  let descend : IntertwiningMap (ξ.comp s) (Representation.linHom (κ.comp i) (π.comp i)) ≃ₗ[R]
      ξ.IntertwiningMap ((multiplicityRep κ π q hq).comp j) :=
    { toFun := fun f =>
        { toLinearMap := f.toLinearMap.codRestrict _ fun a n => by
            obtain ⟨p, hp⟩ := hker n.property
            have hpq : q (i p) = 1 := by rw [hp]; exact n.property
            have hf := (f.isIntertwining _ _ p a).trans (hhom p (f a))
            change Representation.linHom κ π n.val (f a) = f a
            simpa only [MonoidHom.comp_apply, hsk p hpq, map_one, Module.End.one_apply, hp]
              using hf.symm
          isIntertwining' := fun b => by
            obtain ⟨p, rfl⟩ := hs b
            apply LinearMap.ext
            intro a
            apply Subtype.ext
            change f (ξ (s p) a) = (multiplicityRep κ π q hq (j (s p)) _).val
            rw [hsq' p, multiplicityRep_apply]
            exact (f.isIntertwining _ _ p a).trans (hhom p (f a)) }
      invFun := fun f =>
        { toLinearMap := ((MultiplicitySpace κ π q).subtype).comp f.toLinearMap
          isIntertwining' := fun p => by
            apply LinearMap.ext
            intro a
            have hf := congrArg Subtype.val (f.isIntertwining _ _ (s p) a)
            change (f (ξ (s p) a)).val = (multiplicityRep κ π q hq (j (s p)) (f a)).val at hf
            rw [hsq' p, multiplicityRep_apply] at hf
            exact hf.trans (hhom p (f a).val).symm }
      left_inv := by intro f; apply IntertwiningMap.ext; rfl
      right_inv := by intro f; apply IntertwiningMap.ext; exact LinearMap.ext fun _ => Subtype.ext rfl
      map_add' := by intros; apply IntertwiningMap.ext; exact LinearMap.ext fun _ => Subtype.ext rfl
      map_smul' := by intros; apply IntertwiningMap.ext; exact LinearMap.ext fun _ => Subtype.ext rfl }
  exact swapHom.trans (curry.trans descend)

end Langlands.BushnellKutzko.SplitTypeJacquet
