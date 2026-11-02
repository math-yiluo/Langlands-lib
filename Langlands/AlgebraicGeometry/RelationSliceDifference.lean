import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocusInvariant

/-! # Difference of two arrows in a relation slice -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.RelationSlice

open AlgebraicSpace.AtlasRelation

variable {U R V : Scheme.{u}} {t s : R ⟶ U} (hr : IsEquivRel t s) (g : V ⟶ U)

include hr in
private theorem exists_difference :
    ∃ d : pullback (pullback.fst g t) (pullback.fst g t) ⟶ R,
      d ≫ t = pullback.fst _ _ ≫ pullback.snd g t ≫ s ∧
      d ≫ s = pullback.snd _ _ ≫ pullback.snd g t ≫ s := by
  let D := pullback (pullback.fst g t) (pullback.fst g t)
  let a : D ⟶ R := pullback.fst _ _ ≫ pullback.snd g t
  let b : D ⟶ R := pullback.snd _ _ ≫ pullback.snd g t
  obtain ⟨a', ha't, ha's⟩ := hr.symm D a
  have hab : a' ≫ s = b ≫ t := by
    rw [ha's]
    dsimp [a, b]
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using congrArg (· ≫ g)
      (pullback.condition (f := pullback.fst g t) (g := pullback.fst g t))
  obtain ⟨d, hdt, hds⟩ := hr.trans D a' b hab
  exact ⟨d, hdt.trans ha't, hds⟩

/-- The arrow from the target of the first arrow to the target of the second, for two
arrows in a slice with the same point of the slicing scheme. -/
def difference : pullback (pullback.fst g t) (pullback.fst g t) ⟶ R :=
  (exists_difference hr g).choose

@[reassoc (attr := simp)]
theorem difference_t : difference hr g ≫ t =
    pullback.fst _ _ ≫ pullback.snd g t ≫ s :=
  (exists_difference hr g).choose_spec.1

@[reassoc (attr := simp)]
theorem difference_s : difference hr g ≫ s =
    pullback.snd _ _ ≫ pullback.snd g t ≫ s :=
  (exists_difference hr g).choose_spec.2

set_option backward.isDefEq.respectTransparency false in
/-- The difference map is the base change of the associated slice map along `t`. -/
theorem isPullback_difference_t :
    IsPullback (pullback.fst (pullback.fst g t) (pullback.fst g t))
      (difference hr g) (pullback.snd g t ≫ s) t := by
  refine IsPullback.mk' (difference_t hr g).symm ?_ ?_
  · intro T f f' hf hd
    apply pullback.hom_ext
    · exact hf
    · have hp : f ≫ pullback.snd _ _ ≫ pullback.fst g t =
          f' ≫ pullback.snd _ _ ≫ pullback.fst g t := by
        simpa only [Category.assoc, ← pullback.condition] using
          congrArg (· ≫ pullback.fst g t) hf
      apply pullback.hom_ext
      · exact hp
      · apply hr.hom_ext
        · simpa only [Category.assoc, ← pullback.condition (f := g) (g := t)] using
            congrArg (· ≫ g) hp
        · simpa only [Category.assoc, difference_s] using congrArg (· ≫ s) hd
  · intro T a b hab
    obtain ⟨c, hct, hcs⟩ := hr.trans T (a ≫ pullback.snd g t) b
      (by simpa only [Category.assoc] using hab)
    have hc : (a ≫ pullback.fst g t) ≫ g = c ≫ t := by
      rw [hct]
      simp only [Category.assoc, pullback.condition]
    let a' : T ⟶ pullback g t := pullback.lift (a ≫ pullback.fst g t) c hc
    let l : T ⟶ pullback (pullback.fst g t) (pullback.fst g t) :=
      pullback.lift a a' (by simp [a'])
    refine ⟨l, by simp [l], ?_⟩
    apply hr.hom_ext
    · simpa only [Category.assoc, difference_t, l, pullback.lift_fst_assoc] using hab
    · simp only [Category.assoc, difference_s, l, pullback.lift_snd_assoc,
        a', pullback.lift_snd_assoc, hcs]

set_option backward.isDefEq.respectTransparency false in
/-- The same difference map is also the base change of the slice map along `s`. -/
theorem isPullback_difference_s :
    IsPullback (pullback.snd (pullback.fst g t) (pullback.fst g t))
      (difference hr g) (pullback.snd g t ≫ s) s := by
  refine IsPullback.mk' (difference_s hr g).symm ?_ ?_
  · intro T f f' hf hd
    apply pullback.hom_ext
    · have hp : f ≫ pullback.fst _ _ ≫ pullback.fst g t =
          f' ≫ pullback.fst _ _ ≫ pullback.fst g t := by
        simpa only [Category.assoc, pullback.condition] using
          congrArg (· ≫ pullback.fst g t) hf
      apply pullback.hom_ext
      · exact hp
      · apply hr.hom_ext
        · simpa only [Category.assoc, ← pullback.condition (f := g) (g := t)] using
            congrArg (· ≫ g) hp
        · simpa only [Category.assoc, difference_t] using congrArg (· ≫ t) hd
    · exact hf
  · intro T a b hab
    obtain ⟨b', hb't, hb's⟩ := hr.symm T b
    obtain ⟨c, hct, hcs⟩ := hr.trans T (a ≫ pullback.snd g t) b'
      (by simpa only [Category.assoc] using hab.trans hb't.symm)
    have hc : (a ≫ pullback.fst g t) ≫ g = c ≫ t := by
      rw [hct]
      simp only [Category.assoc, pullback.condition]
    let a' : T ⟶ pullback g t := pullback.lift (a ≫ pullback.fst g t) c hc
    let l : T ⟶ pullback (pullback.fst g t) (pullback.fst g t) :=
      pullback.lift a' a (by simp [a'])
    refine ⟨l, by simp [l], ?_⟩
    apply hr.hom_ext
    · simp only [Category.assoc, difference_t, l, pullback.lift_fst_assoc,
        a', pullback.lift_snd_assoc, hcs, hb's]
    · simpa only [Category.assoc, difference_s, l, pullback.lift_snd_assoc] using hab

end Langlands.AlgebraicGeometry.RelationSlice
