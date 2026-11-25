import Langlands.Sheaf.Equivariant.TwistedFreeRepresentableDiscrete

/-! # Lifted representables with monomorphic structure maps -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift

open CategoryTheory

universe u v z

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type z} [Group G] [TopologicalSpace G] {ρ : G →* Aut X}
variable (L : GlobalLift (P := P) (ρ := ρ))
variable (S : LocalActionSystem (TwistedOver P ρ) G)

/-- A monomorphic structure map forces intertwining on the entire source
subgroup, since both composites have the same twist and lie over the base. -/
theorem eventuallyEquivariant_of_mono [Mono L.obj.hom] (hS : S.IsLiftSystem) :
    L.EventuallyEquivariant S := by
  intro V H a ha k
  refine ⟨H, le_rfl, fun h _ => ?_⟩
  have ht : Hom.twist ((a h).unop.asHom ≫ (ι P ρ).map k) =
      Hom.twist ((ι P ρ).map k ≫ (L.action (h : G)).unop.asHom) := by
    simp only [comp_twist, homMk_twist, hS V H a ha h, L.twist, one_mul, mul_one]
  apply hom_ext ht
  apply (cancel_mono L.obj.hom).1
  exact (Hom.w _).trans ((congrArg (fun g => V.hom ≫ (ρ g).asIso.hom) ht).trans (Hom.w _).symm)

end Langlands.Sheaf.Equivariant.TwistedOver.GlobalLift
