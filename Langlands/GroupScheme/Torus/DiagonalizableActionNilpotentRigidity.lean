import Langlands.GroupScheme.Torus.SchemeActionNilpotentRigidity

/-! # Nilpotent rigidity of diagonalizable actions on arbitrary schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SchemeAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {X : Over (Spec R)} (a : SchemeAction (Diagonalizable.groupScheme R M).toGrp X)
  (I : Ideal R) (hI : IsNilpotent I)
  (h : ∀ C : CommAlgCat.{u} R,
    (∀ r : R, r ∈ I → algebraMap R C r = 0) →
    ∀ (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
      (x : (algSpec R).obj (op C) ⟶ X), a.act t x = x)

include hI h

/-- Any point whose image lies in an affine open is fixed by the action. -/
theorem act_eq_of_range_subset_affine
    {T : Over (Spec R)} (t : T ⟶ (Diagonalizable.groupScheme R M).X)
    (x : T ⟶ X) (V : X.left.Opens) [IsAffine V]
    (hx : Set.range x.left ⊆ V) : a.act t x = x := by
  let hV := a.isInvariantOpen_of_nilpotent_quotient I hI h V
  have he : (a.onInvariantOpen hV).hom = snd _ _ := by
    apply hom_eq_snd_of_nilpotent_quotient_of_isAffine _ I hI
    intro C hC t x
    apply (cancel_mono (openSubschemeι V)).mp
    rw [a.onInvariantOpen_act_comp hV]
    exact h C hC t (x ≫ openSubschemeι V)
  let xV := liftToOpen V x hx
  have ht : (a.onInvariantOpen hV).act t xV = xV := by
    rw [act, he, lift_snd]
  have ht' := congrArg (fun q => q ≫ openSubschemeι V) ht
  rw [a.onInvariantOpen_act_comp hV, liftToOpen_comp] at ht'
  exact ht'

/-- An action of a diagonalizable group on any scheme that is trivial over a
nilpotent quotient is already trivial. -/
theorem hom_eq_snd_of_nilpotent_quotient : a.hom = snd _ _ := by
  let H := (Diagonalizable.groupScheme R M).toGrp
  let P := H.X ⊗ X
  let 𝒰 := X.left.affineCover
  let 𝒱 := 𝒰.pullback₁ (snd H.X X).left
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext 𝒱 _ _ fun i => ?_
  let T : Over (Spec R) := Over.mk (𝒱.f i ≫ P.hom)
  let b : T ⟶ P := Over.homMk (𝒱.f i)
  let V : X.left.Opens := (𝒰.f i).opensRange
  let : IsAffine V := isAffineOpen_opensRange (𝒰.f i)
  have hx : Set.range (b ≫ snd H.X X).left ⊆ V := by
    rintro _ ⟨z, rfl⟩
    change (𝒱.f i ≫ (snd H.X X).left) z ∈ (𝒰.f i).opensRange
    rw [← 𝒰.pullbackHom_map (snd H.X X).left i]
    exact ⟨𝒰.pullbackHom (snd H.X X).left i z, rfl⟩
  have hb := a.act_eq_of_range_subset_affine I hI h
    (b ≫ fst H.X X) (b ≫ snd H.X X) V hx
  rw [act, lift_comp_fst_snd] at hb
  exact congrArg CommaMorphism.left hb

/-- The resulting triviality holds on points of every test scheme. -/
theorem act_eq_of_nilpotent_quotient
    {T : Over (Spec R)} (t : T ⟶ (Diagonalizable.groupScheme R M).X)
    (x : T ⟶ X) : a.act t x = x := by
  rw [act, a.hom_eq_snd_of_nilpotent_quotient I hI h, lift_snd]

end Langlands.GroupScheme.SchemeAction
