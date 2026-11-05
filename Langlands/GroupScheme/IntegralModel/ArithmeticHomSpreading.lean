import Langlands.Global.AdelicLevelModelTransition
import Langlands.GroupScheme.IntegralModel.ArithmeticSpreading
import Langlands.GroupScheme.IntegralModel.BaseChangeHom
import Langlands.GroupScheme.Descent.FiniteCoefficientHom

/-! # Spreading supplied homomorphisms over enlarged finite S-integer rings -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Global Langlands.GroupScheme.Descent
open scoped NumberField CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.ArithmeticSpreading

variable (F : Type u) [Field F] [NumberField F]

/-- The enlarged integer ring has exactly the original generic inclusion. -/
theorem integerInclusion_generic {S T : Finset (FinitePlace F)} (hST : S ⊆ T) :
    Spec.algebraMap ((T : Set (FinitePlace F)).integer F) F ≫
        Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F hST)) =
      Spec.algebraMap ((S : Set (FinitePlace F)).integer F) F := by
  dsimp [numberFieldSIntegersMap, Spec.algebraMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Finitely many extra generators over a prescribed S-integer base fit inside
one enlarged actual finite S-integer ring. -/
theorem exists_integer_contains_fg_over (S : Finset (FinitePlace F))
    (T : Subalgebra ((S : Set (FinitePlace F)).integer F) F) (hT : T.FG) :
    ∃ U : Finset (FinitePlace F), S ⊆ U ∧
      T.toSubring ≤ ((U : Set (FinitePlace F)).integer F).toSubring := by
  classical
  obtain ⟨s, hs⟩ := hT
  obtain ⟨U, hU⟩ := exists_integer_contains_finset F s
  let Q : Subalgebra ((S : Set (FinitePlace F)).integer F) F :=
    { ((S ∪ U : Finset (FinitePlace F)) : Set (FinitePlace F)).integer F |>.toSubring with
      algebraMap_mem' := fun r =>
        numberFieldSIntegers_mono F Finset.subset_union_left r.property }
  have hTQ : T ≤ Q := by
    rw [← hs]
    exact Algebra.adjoin_le (fun x hx =>
      numberFieldSIntegers_mono F Finset.subset_union_right (hU hx))
  exact ⟨S ∪ U, Finset.subset_union_left, hTQ⟩

@[reassoc] private theorem baseChange_map_fst {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left := by
  exact pullback.lift_fst _ _ _

private theorem comparison_assoc {S₀ S₁ S₂ S₃ : Scheme.{u}}
    (b : S₁ ⟶ S₀) (a : S₂ ⟶ S₁) (q : S₃ ⟶ S₂)
    (c : S₂ ⟶ S₀) (d : S₃ ⟶ S₁) (e : S₃ ⟶ S₀)
    (hac : a ≫ b = c) (hqd : q ≫ a = d) (hqe : q ≫ c = e) (hde : d ≫ b = e)
    (G : GroupScheme S₀) :
    (baseChange q).map (pullbackComparison b a c hac G).hom ≫
        (pullbackComparison c q e hqe G).hom =
      (pullbackComparison a q d hqd ((baseChange b).obj G)).hom ≫
        (pullbackComparison b d e hde G).hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst, baseChange_map_fst_assoc]
    rw [pullbackComparison_hom_fst_assoc]
  · exact (Over.w ((baseChange q).map (pullbackComparison b a c hac G).hom ≫
      (pullbackComparison c q e hqe G).hom).hom.hom).trans
      (Over.w ((pullbackComparison a q d hqd ((baseChange b).obj G)).hom ≫
        (pullbackComparison b d e hde G).hom).hom.hom).symm

/-- Enlarge an actual arithmetic integral model along the canonical inclusion. -/
def enlargeModel {S T : Finset (FinitePlace F)}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G) (hST : S ⊆ T) :
    IntegralModel ((T : Set (FinitePlace F)).integer F) F G :=
  M.baseChangeModel (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F hST))) (integerInclusion_generic F hST)

/-- Canonical finite enlargement preserves smoothness of the model. -/
theorem smooth_enlargeModel {S T : Finset (FinitePlace F)}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G) (hST : S ⊆ T)
    [Smooth M.group.X.hom] : Smooth (enlargeModel F M hST).group.X.hom :=
  M.smooth_baseChangeModel _ _

/-- Every supplied generic homomorphism extends between the canonical
finite enlargements of the prescribed actual integral models. -/
theorem exists_enlarged_hom (S : Finset (FinitePlace F))
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)
    (N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H)
    [LocallyOfFinitePresentation N.group.X.hom] (f : G ⟶ H) :
    ∃ (U : Finset (FinitePlace F)) (hSU : S ⊆ U),
      Nonempty ((enlargeModel F M hSU).Hom (enlargeModel F N hSU) f) := by
  let f₀ := M.genericIso.hom ≫ f ≫ N.genericIso.inv
  let D := Descent.FiniteCoefficient.homModel M.group N.group f₀
  let C := D.coefficients
  obtain ⟨U, hSU, hCU⟩ := exists_integer_contains_fg_over F S C D.finite
  let A : Type u := (U : Set (FinitePlace F)).integer F
  let i : CommRingCat.of C ⟶ CommRingCat.of A := CommRingCat.ofHom
    { toFun := fun x => ⟨x.val, hCU x.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let b := Spec.algebraMap ((S : Set (FinitePlace F)).integer F) C
  let a := Spec.map i
  let c := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F hSU))
  let q := Spec.algebraMap A F
  let d := Spec.algebraMap C F
  let e := Spec.algebraMap ((S : Set (FinitePlace F)).integer F) F
  have hac : a ≫ b = c := by
    dsimp [a, b, c, i, numberFieldSIntegersMap, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hqd : q ≫ a = d := by
    dsimp [q, a, d, i, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hqe : q ≫ c = e := integerInclusion_generic F hSU
  have hde : d ≫ b = e := by
    dsimp [d, b, e, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let E₁ := pullbackComparison b a c hac M.group
  let E₂ := pullbackComparison b a c hac N.group
  let g := E₁.inv ≫ (baseChange a).map D.hom ≫ E₂.hom
  have hrec : (baseChange q).map g ≫ (pullbackComparison c q e hqe N.group).hom =
      (pullbackComparison c q e hqe M.group).hom ≫ f₀ := by
    simp only [g, Functor.map_comp, Category.assoc]
    rw [comparison_assoc b a q c d e hac hqd hqe hde N.group,
      pullbackComparison_naturality_assoc]
    rw [D.recovery]
    rw [← Category.assoc (pullbackComparison a q d hqd ((baseChange b).obj M.group)).hom,
      ← comparison_assoc b a q c d e hac hqd hqe hde M.group]
    simp only [E₁, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [(baseChange q).map_id, Category.id_comp]
  refine ⟨U, hSU, ⟨{ hom := g, generic_comm := ?_ }⟩⟩
  change (baseChange q).map g ≫
      ((pullbackComparison c q e hqe N.group).hom ≫ N.genericIso.hom) =
    ((pullbackComparison c q e hqe M.group).hom ≫ M.genericIso.hom) ≫ f
  rw [← Category.assoc, hrec]
  simp [f₀, Category.assoc]

/-- A finite canonical enlargement and a generic-compatible homomorphism. -/
structure EnlargedHomData (S : Finset (FinitePlace F))
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)
    (N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H)
    (f : G ⟶ H) where
  places : Finset (FinitePlace F)
  contains : S ⊆ places
  hom : (enlargeModel F M contains).Hom (enlargeModel F N contains) f

/-- Choose a finite canonical enlargement and an actual extension of the
supplied generic homomorphism. -/
def enlargedHomData (S : Finset (FinitePlace F))
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)
    (N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H)
    [LocallyOfFinitePresentation N.group.X.hom] (f : G ⟶ H) :
    EnlargedHomData F S M N f :=
  let h := exists_enlarged_hom F S M N f
  { places := Classical.choose h
    contains := Classical.choose (Classical.choose_spec h)
    hom := Classical.choice (Classical.choose_spec (Classical.choose_spec h)) }

end Langlands.GroupScheme.IntegralModel.ArithmeticSpreading
