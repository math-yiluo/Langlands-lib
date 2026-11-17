import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.Torus.FieldCocycleDescent
import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract

/-! # Field cocycles of split-solvable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace SplitSolvable

variable {k : Type u} [Field k]

/-- Elementary Ga/Gm groups have no nontrivial affine faithfully flat cocycles over a field. -/
theorem isTrivial_of_elementary {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : IsElementaryQuotient V)
    (U : Over (Spec (CommRingCat.of k))) [IsAffine U.left] [Flat U.hom]
    [Surjective U.hom] (ξ : Cocycle V U) : ξ.IsTrivial := by
  change RelativeRoot.IsVectorGroupOfDimension V 1 ∨ Nonempty (V ≅ (Gm _).toGrp) at hV
  rcases hV with hV | hV
  · let T : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
    let : IsAffine T.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
    apply Cocycle.IsTrivial.of_map_retract (baseChangeIdIso V).inv
      (baseChangeIdIso V).hom (Iso.inv_hom_id _)
    exact Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV T U _
  · obtain ⟨e⟩ := hV
    exact Cocycle.isTrivial_of_isSplitTorus_overField
      (IsSplitTorus.of_iso e isSplitTorus_gm) ξ

/-- Induction over a split series, using an fpqc refinement to lift each quotient cochain. -/
theorem isTrivial_of_hasSeries :
    ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))), HasSeries n H →
      IsAffineHom H.X.hom →
      ∀ (U : Over (Spec (CommRingCat.of k))) [IsAffine U.left] [Flat U.hom]
        [Surjective U.hom] (ξ : Cocycle H U), ξ.IsTrivial := by
  intro n
  induction n with
  | zero =>
      intro H hH _ U _ _ _ ξ
      have hpt : ∀ {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ H.X), x = 1 := by
        intro Z x
        have hx : x ∈ (SubgroupFunctor.range (𝟙 H)).carrier Z :=
          SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id _⟩
        rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
        exact hx
      exact ⟨1, fun a b => (hpt _).trans (hpt _).symm⟩
  | succ n ih =>
      intro H hH ha U _ _ _ ξ
      let : IsAffineHom H.X.hom := ha
      obtain ⟨N, V, j, q, hj, _, _, _, hq, hV, hN⟩ := hH
      let : IsClosedImmersion j.hom.hom.left := hj
      let : Mono j.hom.hom := Over.mono_of_mono_left _
      have hNa : IsAffineHom N.X.hom := by
        rw [← Over.w j.hom.hom]
        infer_instance
      obtain ⟨f, hf⟩ := isTrivial_of_elementary hV U (ξ.map q)
      let : Flat q.hom.hom.left := hq.1
      let : Surjective q.hom.hom.left := hq.2.1
      let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
      have hVa : IsAffineHom V.X.hom := by
        change RelativeRoot.IsVectorGroupOfDimension V 1 ∨ Nonempty (V ≅ (Gm _).toGrp) at hV
        rcases hV with hV | hV
        · exact hV.isAffineHom_overRing
        · obtain ⟨e⟩ := hV
          exact (IsSplitTorus.of_iso e isSplitTorus_gm).isAffineHom
      let : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
      let W : Over (Spec (CommRingCat.of k)) :=
        Over.mk (pullback.snd q.hom.hom.left f.left ≫ U.hom)
      let r : W ⟶ U := Over.homMk (pullback.snd _ _) rfl
      let F : W ⟶ H.X := Over.homMk (pullback.fst _ _) (by
        rw [← Over.w q.hom.hom, ← Category.assoc, pullback.condition,
          Category.assoc, Over.w f]
        rfl)
      have hF : F ≫ q.hom.hom = r ≫ f :=
        Over.OverMorphism.ext pullback.condition
      let : IsAffine W.left := inferInstanceAs (IsAffine (pullback q.hom.hom.left f.left))
      let : Flat W.hom := inferInstanceAs (Flat (pullback.snd q.hom.hom.left f.left ≫ U.hom))
      let : Surjective W.hom :=
        inferInstanceAs (Surjective (pullback.snd q.hom.hom.left f.left ≫ U.hom))
      have hval : ∀ {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ W),
          ∃ z : Z ⟶ N.X, z ≫ j.hom.hom = ((ξ.refine r).twist F).toFun a b := by
        intro Z a b
        apply SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hq.2.2.2
        change ((a ≫ F)⁻¹ * ξ.toFun (a ≫ r) (b ≫ r) * (b ≫ F)) ≫ q.hom.hom = 1
        simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hF]
        rw [show ξ.toFun (a ≫ r) (b ≫ r) ≫ q.hom.hom =
          ((a ≫ r) ≫ f) * ((b ≫ r) ≫ f)⁻¹ from hf (a ≫ r) (b ≫ r)]
        simp only [Category.assoc]
        group
      exact (Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_lift
        (ih N hN hNa W (((ξ.refine r).twist F).lift j hval)))).of_refine_fpqcCover r

/-- Every cocycle under a split-solvable group on an fppf cover of a field is trivial. -/
theorem isTrivial_of_isSplitSolvable
    {H : GroupScheme (Spec (CommRingCat.of k))} (hH : IsSplitSolvableGroupScheme H)
    (U : Over (Spec (CommRingCat.of k))) [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] (ξ : Cocycle H U) : ξ.IsTrivial := by
  obtain ⟨n, hn⟩ := hH.hasSeries
  exact ξ.isTrivial_of_affine_fppf fun W _ _ _ _ ζ =>
    isTrivial_of_hasSeries n H hn hH.isAffineHom W ζ

end SplitSolvable
end Langlands.GroupScheme
