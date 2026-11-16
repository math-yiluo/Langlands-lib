import Langlands.GroupScheme.Reductive.RelativeCommutatorDescent
import Langlands.GroupScheme.Reductive.CorootCommutator
import Langlands.GroupScheme.ReducedBaseSmooth.Translation
import Langlands.GroupScheme.Reductive.Basic

/-! # Fppf generation by an open unit neighbourhood -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeDerived

variable {S : Scheme.{u}} {G : GroupScheme S} {P : Over S}

/-- If an open unit neighbourhood has fppf-local commutator values, every
point of a reductive group has fppf-local commutator membership. -/
theorem locallyCommutator_of_open_unit_cell (hG : IsReductive G) (Ω : P ⟶ G.X)
    [IsOpenImmersion Ω.left]
    (he : Set.range η[G.X].left ⊆ Set.range Ω.left)
    (hΩ : ∀ (Z : Over S) (p : Z ⟶ P), LocallyCommutator (p ≫ Ω))
    (Z : Over S) (x : Z ⟶ G.X) : LocallyCommutator x := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth P.hom := by
    rw [← Over.w Ω]
    infer_instance
  let q : P ⊗ P ⟶ G.X := (Ω ⊗ₘ Ω) ≫ μ[G.X]
  have : Smooth q.left := ReducedBaseSmooth.smooth_tensorHom_comp_mul G Ω
  have : Surjective q.left := by
    rw [surjective_iff, ← Set.range_eq_univ]
    exact ReducedBaseSmooth.range_tensorHom_comp_mul_eq_univ G Ω
      (fun s => (hG.isConnectedReductive_residueFiber s).smooth)
      (fun s => (hG.isConnectedReductive_residueFiber s).connectedSpace) he
  let b := pullback.fst x.left q.left
  let W : Over S := Over.mk (b ≫ Z.hom)
  let w : W ⟶ Z := Over.homMk b rfl
  have : Flat w.left := inferInstanceAs (Flat b)
  have : Surjective w.left := inferInstanceAs (Surjective b)
  have : LocallyOfFinitePresentation w.left := inferInstanceAs (LocallyOfFinitePresentation b)
  let a : W ⟶ P ⊗ P := Over.homMk (pullback.snd x.left q.left) (by
    change pullback.snd x.left q.left ≫ (P ⊗ P).hom = b ≫ Z.hom
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, x.w])
  have ha : w ≫ x = a ≫ q := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hq : a ≫ q = (a ≫ fst P P ≫ Ω) * (a ≫ snd P P ≫ Ω) := by
    simp only [q, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  apply LocallyCommutator.of_surjective w
  rw [ha, hq]
  exact (hΩ W (a ≫ fst P P)).mul (hΩ W (a ≫ snd P P))

end Langlands.GroupScheme.RelativeDerived

namespace Langlands.GroupScheme.RelativeDerived

/-- A chosen fppf commutator cover supplied by the open-unit-cell reduction. -/
def openCellCommutatorCover {S : Scheme.{u}} {G : GroupScheme S} {P : Over S}
    (hG : IsReductive G) (Ω : P ⟶ G.X) [IsOpenImmersion Ω.left]
    (he : Set.range η[G.X].left ⊆ Set.range Ω.left)
    (hΩ : ∀ (Z : Over S) (p : Z ⟶ P), LocallyCommutator (p ≫ Ω))
    (Z : Over S) (x : Z ⟶ G.X) :
    Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Z.left :=
  (locallyCommutator_of_open_unit_cell hG Ω he hΩ Z x).choose

/-- The chosen cover witnesses abstract commutator membership on every member. -/
theorem openCellCommutatorCover_mem {S : Scheme.{u}} {G : GroupScheme S} {P : Over S}
    (hG : IsReductive G) (Ω : P ⟶ G.X) [IsOpenImmersion Ω.left]
    (he : Set.range η[G.X].left ⊆ Set.range Ω.left)
    (hΩ : ∀ (Z : Over S) (p : Z ⟶ P), LocallyCommutator (p ≫ Ω))
    (Z : Over S) (x : Z ⟶ G.X) (j : (openCellCommutatorCover hG Ω he hΩ Z x).I₀) :
    (Over.homMk ((openCellCommutatorCover hG Ω he hΩ Z x).f j) rfl :
      Over.mk ((openCellCommutatorCover hG Ω he hΩ Z x).f j ≫ Z.hom) ⟶ Z) ≫ x ∈
        _root_.commutator _ :=
  (locallyCommutator_of_open_unit_cell hG Ω he hΩ Z x).choose_spec j

end Langlands.GroupScheme.RelativeDerived
