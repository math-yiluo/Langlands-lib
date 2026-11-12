import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # The fibre product of two charts over a common target chart -/

noncomputable section

universe v w

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.TripleChartPullback

variable {C : Type w} [Category.{v} C]
  {A B R T U V D Z : C}
  {aD : A ⟶ D} {aU : A ⟶ U} {bD : B ⟶ D} {bV : B ⟶ V}
  {rA : R ⟶ A} {rB : R ⟶ B} {tU : T ⟶ U} {tV : T ⟶ V}
  {d : D ⟶ Z} {u : U ⟶ Z} {v : V ⟶ Z}
  (hA : IsPullback aD aU d u) (hB : IsPullback bD bV d v)
  (hR : IsPullback rA rB aD bD) (hT : IsPullback tU tV u v)

/-- The canonical map `(D ×_Z U) ×_D (D ×_Z V) → U ×_Z V`. -/
def map : R ⟶ T := hT.lift (rA ≫ aU) (rB ≫ bV) (by
  rw [Category.assoc, ← hA.w, ← Category.assoc, hR.w, Category.assoc, hB.w]
  simp only [Category.assoc])

@[reassoc (attr := simp)]
theorem map_fst : map hA hB hR hT ≫ tU = rA ≫ aU := hT.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_snd : map hA hB hR hT ≫ tV = rB ≫ bV := hT.lift_snd _ _ _

/-- The canonical map is the base change of the common chart `D → Z`. -/
theorem isPullback : IsPullback (map hA hB hR hT) (rA ≫ aD) (tU ≫ u) d := by
  have hw : map hA hB hR hT ≫ (tU ≫ u) = (rA ≫ aD) ≫ d := by
    rw [← Category.assoc, map_fst, Category.assoc, ← hA.w, Category.assoc]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  let la := fun (s : PullbackCone (tU ≫ u) d) =>
    hA.lift s.snd (s.fst ≫ tU) (by simpa only [Category.assoc] using s.condition.symm)
  let lb := fun (s : PullbackCone (tU ≫ u) d) =>
    hB.lift s.snd (s.fst ≫ tV) (by
      rw [Category.assoc, ← hT.w]
      exact s.condition.symm)
  refine PullbackCone.IsLimit.mk _
    (fun s => hR.lift (la s) (lb s) (by simp [la, lb])) ?_ ?_ ?_
  · intro s
    apply hT.hom_ext <;> simp [la, lb]
  · intro s
    simp [la]
  · intro s m hm₁ hm₂
    apply hR.hom_ext
    · apply hA.hom_ext
      · simpa [la] using hm₂
      · simpa [la] using congrArg (fun k => k ≫ tU) hm₁
    · apply hB.hom_ext
      · simpa [lb, ← hR.w] using hm₂
      · simpa [lb] using congrArg (fun k => k ≫ tV) hm₁

end Langlands.AlgebraicGeometry.AlgebraicSpace.TripleChartPullback
