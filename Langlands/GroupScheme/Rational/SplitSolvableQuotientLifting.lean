import Langlands.GroupScheme.Rational.SplitSolvableFieldCocycle
import Langlands.GroupScheme.HomogeneousQuotientStatement
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Rational lifting for quotients by split-solvable groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every rational coset of a split-solvable subgroup has a rational representative. -/
theorem exists_rationalLift_of_splitSolvable
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (hb : IsClosedSubgroup b) (hB : IsSplitSolvableGroupScheme B)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, g ≫ q = x := by
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let U : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.snd q.left x.left)
  let v : U ⟶ G.X := Over.homMk (pullback.fst q.left x.left) (by
    rw [← Over.w q, ← Category.assoc, pullback.condition, Category.assoc, Over.w x]
    exact Category.comp_id _)
  let r : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.homMk U.hom (by simp)
  have hvq : v ≫ q = r ≫ x := Over.OverMorphism.ext pullback.condition
  let : Smooth U.hom := inferInstanceAs (Smooth (pullback.snd q.left x.left))
  let : Surjective U.hom := inferInstanceAs (Surjective (pullback.snd q.left x.left))
  let : QuasiCompact U.hom := inferInstanceAs (QuasiCompact (pullback.snd q.left x.left))
  have hval : ∀ {Z : Over (Spec (CommRingCat.of k))} (a c : Z ⟶ U),
      ∃ h : Z ⟶ B.X, h ≫ b.hom.hom = (Cocycle.coboundary v⁻¹).toFun a c := by
    intro Z a c
    apply SubgroupFunctor.mem_range.mp
    simp only [Cocycle.coboundary, GrpObj.comp_inv, inv_inv]
    apply (hfib Z _ _).mp
    simp only [Category.assoc, hvq]
    have hr : a ≫ r = c ≫ r := Over.OverMorphism.ext
      ((Over.w a).trans (Over.w c).symm)
    exact congrArg (fun t => t ≫ x) hr
  let ξ := (Cocycle.coboundary v⁻¹).lift b hval
  obtain ⟨f, hf⟩ := SplitSolvable.isTrivial_of_isSplitSolvable hB U ξ
  let J : U ⟶ G.X := f ≫ b.hom.hom
  have hJ : ∀ {Z : Over (Spec (CommRingCat.of k))} (a c : Z ⟶ U),
      (a ≫ J) * (c ≫ J)⁻¹ = (a ≫ v)⁻¹ * (c ≫ v) := by
    intro Z a c
    have h := (Cocycle.coboundary v⁻¹).lift_toFun b hval a c
    rw [show (Cocycle.coboundary v⁻¹).lift b hval = ξ from rfl,
      hf, MonObj.mul_comp, GrpObj.inv_comp] at h
    simpa only [Cocycle.coboundary, GrpObj.comp_inv, inv_inv, J, Category.assoc] using h
  let P : U ⟶ G.X := v * J
  obtain ⟨s, hs, hsbase⟩ := exists_section_of_forall_eq P (by
    intro Z a c
    simp only [P, MonObj.comp_mul]
    calc
      (a ≫ v) * (a ≫ J) =
          (a ≫ v) * ((a ≫ J) * (c ≫ J)⁻¹) * (c ≫ J) := by group
      _ = (a ≫ v) * ((a ≫ v)⁻¹ * (c ≫ v)) * (c ≫ J) := by rw [hJ]
      _ = (c ≫ v) * (c ≫ J) := by group)
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk s hsbase
  refine ⟨g, ?_⟩
  have hPg : P = r ≫ g := Over.OverMorphism.ext hs.symm
  have hPq : P ≫ q = v ≫ q := by
    apply ((hfib U v P).mpr ?_).symm
    have hmem : J ∈ (SubgroupFunctor.range b).carrier U :=
      SubgroupFunctor.mem_range.mpr ⟨f, rfl⟩
    simpa only [P, inv_mul_cancel_left] using hmem
  apply Over.OverMorphism.ext
  apply (cancel_epi U.hom).mp
  have he : r ≫ (g ≫ q) = r ≫ x := by
    rw [← Category.assoc, ← hPg, hPq, hvq]
  exact congrArg (fun a : U ⟶ Q => a.left) he

end Langlands.GroupScheme
