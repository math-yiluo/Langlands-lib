import Langlands.Representation.Induction.QuotientAdjunction

/-! # Inflation and invariants along an identified quotient

Renard VI.9.7, Hom calculation after the completion theorem, printed p. 206 /
PDF p. 212. Inflation along the Levi projection is left adjoint to the
unipotent-radical invariants with their induced Levi action.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uP uM uV

variable {R : Type uR} [CommRing R]

private def restrictionEquivalence {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Rep.{uV} R B ≌ Rep.{uV} R A :=
  CategoryTheory.Equivalence.mk (Rep.resFunctor e.toMonoidHom)
    (Rep.resFunctor e.symm.toMonoidHom)
    (NatIso.ofComponents (fun W => Rep.mkIso
      { toLinearEquiv := LinearEquiv.refl R W
        isIntertwining' := fun b => by
          apply LinearMap.ext
          intro v
          change W.ρ b v = W.ρ (e (e.symm b)) v
          rw [e.apply_symm_apply] }) (fun _ => rfl))
    (NatIso.ofComponents (fun W => Rep.mkIso
      { toLinearEquiv := LinearEquiv.refl R W
        isIntertwining' := fun a => by
          apply LinearMap.ext
          intro v
          change W.ρ (e.symm (e a)) v = W.ρ a v
          rw [e.symm_apply_apply] }) (fun _ => rfl))

variable {P : Type uP} {M : Type uM} [Group P] [Group M]
  (N : Subgroup P) [N.Normal] (e : P ⧸ N ≃* M)

/-- Inflation along the quotient followed by `e` is left adjoint to the
actual `N`-invariants with their action transported along `e.symm`. -/
def quotientInflationInvariantsAdjunction :
    Rep.resFunctor.{uV} (k := R) (e.toMonoidHom.comp (QuotientGroup.mk' N)) ⊣
      Rep.quotientToInvariantsFunctor R N ⋙ Rep.resFunctor e.symm.toMonoidHom :=
  (restrictionEquivalence (R := R) e).toAdjunction.comp (inflationInvariantsAdjunction R N)

/-- The counit is the inclusion of invariant vectors. -/
theorem quotientInflationInvariantsAdjunction_counit_app_apply
    (W : Rep.{uV} R P) (v : Representation.invariants (W.ρ.comp N.subtype)) :
    ((quotientInflationInvariantsAdjunction N e).counit.app W).hom v = v.val := by
  unfold quotientInflationInvariantsAdjunction
  rw [Adjunction.comp_counit_app]
  rfl

end Langlands.Induction
