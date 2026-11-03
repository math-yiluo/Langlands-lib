import Langlands.GroupScheme.Absolute.SolvableFieldExtensionStatement
import Langlands.GroupScheme.DerivedTerm
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

/-! # Solvability after arbitrary field extension -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace SolvableFieldExtensionProof

variable {k : Type u} [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Solvability in the chosen closure, expressed as points over the original base. -/
theorem geometricPoints_isSolvable (hG : IsSolvableGroupScheme G) :
    Group.IsSolvable
      ((Over.map (toAlgebraicClosure k)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) ⟶ G.X) := by
  let : Group.IsSolvable
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X) := hG
  let e := baseChangePointsEquiv (toAlgebraicClosure k) G
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

/-- A term vanishing on all chosen geometric points is the unit morphism. -/
theorem evaluation_eq_one [IsAffineHom G.X.hom] (hG : Smooth G.X.hom)
    (n : ℕ)
    (hn : derivedSeries
      ((Over.map (toAlgebraicClosure k)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) ⟶ G.X) n = ⊥)
    (t : DerivedTerm n) : DerivedTerm.evaluation G t = 1 := by
  let : Smooth (DerivedTerm.domain G t).hom := DerivedTerm.smooth_domain G t hG
  let : IsReduced (DerivedTerm.domain G t).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k (DerivedTerm.domain G t).left (DerivedTerm.domain G t).hom
  apply Over.OverMorphism.ext
  let φ : SchemeHomOver (DerivedTerm.domain G t).hom G.X.hom :=
    ⟨(DerivedTerm.evaluation G t).left, (DerivedTerm.evaluation G t).w⟩
  let ψ : SchemeHomOver (DerivedTerm.domain G t).hom G.X.hom :=
    ⟨(1 : DerivedTerm.domain G t ⟶ G.X).left,
      (1 : DerivedTerm.domain G t ⟶ G.X).w⟩
  have hφψ : φ = ψ := by
    apply SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      k (AlgebraicClosure k)
    intro x
    let a : (Over.map (toAlgebraicClosure k)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) ⟶ DerivedTerm.domain G t :=
      Over.homMk x.val (x.property.trans (Category.id_comp _).symm)
    have ha := DerivedTerm.evaluation_mem G t a
    rw [hn, Subgroup.mem_bot] at ha
    have hae : a ≫ DerivedTerm.evaluation G t =
        a ≫ (1 : DerivedTerm.domain G t ⟶ G.X) := by
      simpa only [MonObj.comp_one] using ha
    exact congrArg (fun f => f.left) hae
  exact congrArg Subtype.val hφψ

/-- The geometric bound for a smooth affine group works on every test scheme. -/
theorem exists_uniform_derivedSeries_eq_bot [IsAffineHom G.X.hom]
    (hG : Smooth G.X.hom) (hsol : IsSolvableGroupScheme G) :
    ∃ n : ℕ, ∀ T : Over (Spec (CommRingCat.of k)),
      derivedSeries (T ⟶ G.X) n = ⊥ := by
  let := geometricPoints_isSolvable G hsol
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable
    (G := (Over.map (toAlgebraicClosure k)).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))) ⟶ G.X)
  refine ⟨n, fun T => le_bot_iff.mp ?_⟩
  intro x hx
  obtain ⟨t, a, rfl⟩ := DerivedTerm.exists_evaluation G n x hx
  rw [evaluation_eq_one G hG n hn t, MonObj.comp_one]
  exact (⊥ : Subgroup (T ⟶ G.X)).one_mem

/-- Every test-scheme point group is solvable under these hypotheses. -/
theorem allPoints_isSolvable [IsAffineHom G.X.hom]
    (hG : Smooth G.X.hom) (hsol : IsSolvableGroupScheme G)
    (T : Over (Spec (CommRingCat.of k))) : Group.IsSolvable (T ⟶ G.X) := by
  obtain ⟨n, hn⟩ := exists_uniform_derivedSeries_eq_bot G hG hsol
  exact ⟨n, hn T⟩

end SolvableFieldExtensionProof

/-- Smooth affine solvable group schemes stay solvable under every field extension. -/
theorem solvableFieldExtensionStatement : SolvableFieldExtensionStatement.{u} := by
  intro k K _ _ b G _ hG hsol
  let H := (GroupScheme.baseChange b).obj G
  let T := Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure K))))
  let T' := (Over.map (toAlgebraicClosure K)).obj T
  let e := baseChangePointsEquiv (toAlgebraicClosure K) H T
  let e' := baseChangePointsEquiv b G T'
  let := SolvableFieldExtensionProof.allPoints_isSolvable G hG hsol ((Over.map b).obj T')
  let : Group.IsSolvable (T' ⟶ H.X) :=
    Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Langlands.GroupScheme
