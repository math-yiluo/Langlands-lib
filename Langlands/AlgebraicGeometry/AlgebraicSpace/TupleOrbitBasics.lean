import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageClasses
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPointBound
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibrePowerCoordinates

/-! # Basic facts for tuples of points of a finite cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : Presheaf S}

section Relative

/-- Finiteness of scheme morphisms over `S` is stable under base change in `Over S`. -/
instance finite_inverseImage_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S)).IsStableUnderBaseChange :=
  { of_isPullback := fun sq hg ↦
      MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsFinite.{u})
        (sq.map (Over.forget S)) hg }

/-- Surjectivity of scheme morphisms over `S` is stable under base change in `Over S`. -/
instance surjective_inverseImage_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderBaseChange :=
  { of_isPullback := fun sq hg ↦
      MorphismProperty.of_isPullback (P := @Surjective.{u}) (sq.map (Over.forget S)) hg }

instance finite_inverseImage_isStableUnderComposition :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S)).IsStableUnderComposition :=
  { comp_mem := fun f g hf hg => by
      change _root_.AlgebraicGeometry.IsFinite (f ≫ g).left
      rw [Over.comp_left]
      exact MorphismProperty.comp_mem _ _ _ hf hg }

instance surjective_inverseImage_isStableUnderComposition :
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderComposition :=
  { comp_mem := fun f g hf hg => by
      change Surjective (f ≫ g).left
      rw [Over.comp_left]
      have : Surjective f.left := hf
      have : Surjective g.left := hg
      infer_instance }

/-- A finite morphism of schemes followed by a finite map to a presheaf is finite. -/
theorem IsFinite.map_comp {U' U : Over S} (φ : U' ⟶ U)
    (hφ : _root_.AlgebraicGeometry.IsFinite φ.left) {f : (schemeYoneda S).obj U ⟶ X}
    (hf : IsFinite f) : IsFinite ((schemeYoneda S).map φ ≫ f) :=
  MorphismProperty.comp_mem ((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u}) (Over.forget S)).relative (schemeYoneda S)) _ _
    (MorphismProperty.relative_map (F := schemeYoneda S)
      (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget S)) hφ) hf

/-- A surjective morphism of schemes followed by a surjective map to a presheaf is surjective. -/
theorem IsSurjective.map_comp {U' U : Over S} (φ : U' ⟶ U) (hφ : Surjective φ.left)
    {f : (schemeYoneda S).obj U ⟶ X} (hf : IsSurjective f) :
    IsSurjective ((schemeYoneda S).map φ ≫ f) :=
  MorphismProperty.comp_mem ((MorphismProperty.inverseImage
      (@Surjective.{u}) (Over.forget S)).relative (schemeYoneda S)) _ _
    (MorphismProperty.relative_map (F := schemeYoneda S)
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hφ) hf

end Relative

namespace ChartFibrePower

variable {U : Over S} {f : (schemeYoneda S).obj U ⟶ X} {ι : Type*}

/-- Two coordinates of a point of a fibre power have the same image. -/
theorem sameImage_pr (P : ChartFibrePower f ι) (p : P.obj.left) (i j : ι) :
    SameImage f ((P.pr i).left p) ((P.pr j).left p) :=
  ⟨P.obj, P.pr i, P.pr j, p, P.w i j, rfl, rfl⟩

/-- The last projection of the standard fibre powers is a finite morphism. -/
theorem fin_pr_last_isFinite (hf : IsFinite f) (ha : (schemeYoneda S).relativelyRepresentable f) :
    ∀ n : ℕ, _root_.AlgebraicGeometry.IsFinite ((fin ha n).pr (Fin.last n)).left
  | 0 => by
    change _root_.AlgebraicGeometry.IsFinite (Over.Hom.left (𝟙 U))
    rw [Over.id_left]
    infer_instance
  | n + 1 => by
    have ih := fin_pr_last_isFinite hf ha n
    have hsnd : _root_.AlgebraicGeometry.IsFinite (succSnd ha (fin ha n)).left :=
      hf.projection _ _ _ (succ_isPullback ha (fin ha n))
    change _root_.AlgebraicGeometry.IsFinite
      (succPr ha (fin ha n) (Fin.last n).succ).left
    rw [succPr_succ, Over.comp_left]
    infer_instance

end ChartFibrePower

set_option backward.isDefEq.respectTransparency.types false in
/-- A bound on the length of tuples of pairwise distinct points through a fixed point. -/
theorem exists_bound_isDistinct {U : Over S} {f : (schemeYoneda S).obj U ⟶ X}
    (hf : IsFinite f) (γ : U.left) :
    ∃ N : ℕ, ∀ (m : ℕ) (Q : ChartFibrePower f (Fin m)) (q : Q.obj.left), Q.IsDistinct q →
      (∃ k, (Q.pr k).left q = γ) → m ≤ N := by
  have ha : (schemeYoneda S).relativelyRepresentable f := hf.representable
  let R := ChartFibrePower.fin ha 1
  have hR : _root_.AlgebraicGeometry.IsFinite (R.pr 1).left :=
    ChartFibrePower.fin_pr_last_isFinite hf ha 1
  obtain ⟨N, hN⟩ := exists_card_le_of_isFinite (R.pr 1).left γ
  refine ⟨N, fun m Q q hq ⟨k, hk⟩ => ?_⟩
  let K := Q.obj.left.residueField q
  let x : Spec K ⟶ U.left := Q.coord q k
  obtain ⟨⟨y, α⟩, hxe⟩ := (Scheme.SpecToEquivOfField K U.left).symm.surjective x
  have hy : y = γ := by
    have h1 := congrArg (fun g => (Scheme.SpecToEquivOfField K U.left g).1) hxe
    simp only [Equiv.apply_symm_apply] at h1
    rw [h1]
    simp only [x, ChartFibrePower.coord, Scheme.SpecToEquivOfField_apply_fst,
      Scheme.Hom.comp_apply]
    erw [Scheme.fromSpecResidueField_apply]
    exact hk
  subst hy
  let fam : Fin m → Fin 2 → (Q.pointTest q ⟶ U) := fun j => ![Q.pointHom q ≫ Q.pr j,
    Q.pointHom q ≫ Q.pr k]
  have hfam : ∀ j, ∀ a b, (schemeYoneda S).map (fam j a) ≫ f =
      (schemeYoneda S).map (fam j b) ≫ f := by
    intro j a b
    have key : ∀ c, (schemeYoneda S).map (fam j c) ≫ f =
        (schemeYoneda S).map (Q.pointHom q) ≫ (schemeYoneda S).map (Q.pr k) ≫ f := by
      intro c
      fin_cases c <;> simp [fam, Q.w j k]
    rw [key a, key b]
  let r : Fin m → (Spec K ⟶ R.obj.left) := fun j => (R.lift (fam j) (hfam j)).left
  have hr1 : ∀ j, r j ≫ (R.pr 1).left = Spec.map α ≫ U.left.fromSpecResidueField y := by
    intro j
    have hx' : Spec.map α ≫ U.left.fromSpecResidueField y = x := hxe
    rw [hx']
    exact congrArg Over.Hom.left (R.lift_pr (fam j) (hfam j) 1)
  have hrinj : Function.Injective r := by
    intro j j' hjj'
    apply hq
    have h0 : (R.lift (fam j) (hfam j) ≫ R.pr 0).left =
        (R.lift (fam j') (hfam j') ≫ R.pr 0).left := by
      rw [Over.comp_left, Over.comp_left]
      exact congrArg (· ≫ (R.pr 0).left) hjj'
    rw [R.lift_pr, R.lift_pr] at h0
    exact h0
  exact hN K α m r hrinj hr1

end Langlands.AlgebraicGeometry.AlgebraicSpace
