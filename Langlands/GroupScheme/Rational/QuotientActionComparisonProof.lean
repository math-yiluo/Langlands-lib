import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # The relative root functor is the image of the descended identity-limit functor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- Restricting the torus orbit to one torus point is the conjugation action. -/
theorem lift_orbit {T V : Over B} (b : V ⟶ T) (s : V ⟶ S.X) (g : T ⟶ G.X) :
    lift b s ≫ orbit i g = (AutomorphicAction.conjugation i).act s (b ≫ g) := by
  rw [orbit, AutomorphicAction.naturality, lift_snd, lift_fst_assoc]

/-- A point whose torus orbit extends through the character centralizes the actual
character kernel: on the kernel the extension is evaluated at `1`. -/
theorem mem_kernelCentralizer_of_isOrbitExtension {T : Over B} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme B ⟶ G.X} (he : IsOrbitExtension i a g e) :
    g ∈ (kernelCentralizer i a).carrier T := by
  rw [kernelCentralizer, AutomorphicAction.mem_fixedSubgroup]
  intro V b k
  have hk : (k ≫ (characterKernelι a).hom.hom) ≫ (CommGroupScheme.groupHom a).hom.hom = 1 :=
    (kernelPointsEquiv (CommGroupScheme.groupHom a) V k).property
  have hval : ∀ s : V ⟶ S.X, s ≫ (CommGroupScheme.groupHom a).hom.hom = 1 →
      (AutomorphicAction.conjugation i).act s (b ≫ g) =
        lift b (1 ≫ AffineLine.unitInclusion B) ≫ e := fun s hs => by
    rw [← lift_orbit, ← he, lift_whiskerLeft_assoc, ← Category.assoc s, hs]
  rw [AutomorphicAction.restrict_act, hval _ hk, ← hval 1 (MonObj.one_comp _),
    AutomorphicAction.act_one_left]

section RepresentedCentralizer

variable {C : GroupScheme B} (j : C ⟶ G) (hj : (kernelCentralizer i a).IsRepresentedBy j)

/-- The torus action on the represented centralizer is the restricted conjugation action. -/
theorem centralizerAction_act_comp {T : Over B} (h : T ⟶ S.X) (c : T ⟶ C.X) :
    (centralizerAction i a j hj).act h c ≫ j.hom.hom =
      (AutomorphicAction.conjugation i).act h (c ≫ j.hom.hom) :=
  AutomorphicAction.onRepresentedFixedSubgroup_act_comp _ _ _ hj h c

variable [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- Along the character, the descended orbit of a centralizer point maps to the
torus orbit of its image. -/
theorem whiskerLeft_quotientAction_orbit_comp {T : Over B} (c : T ⟶ C.X) :
    T ◁ (CommGroupScheme.groupHom a).hom.hom ≫
        (quotientAction i a j hj).orbit c ≫ j.hom.hom = orbit i (c ≫ j.hom.hom) := by
  rw [AutomorphicAction.orbit, ← Category.assoc, AutomorphicAction.naturality,
    whiskerLeft_snd, whiskerLeft_fst_assoc, quotientAction,
    AutomorphicAction.quotientAction_act_lift, centralizerAction_act_comp, orbit,
    Category.assoc]

/-- Every point of the root functor is the image of an identity-limit point of the
descended action. -/
theorem subgroup_le_map (hjc : IsClosedSubgroup j) :
    subgroup i a ≤ (quotientAction i a j hj).unipotent.map j := by
  rintro T g ⟨e, he, he0⟩
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom := hj.1
  obtain ⟨c, rfl⟩ : ∃ c, c ≫ j.hom.hom = g := by
    have hg := mem_kernelCentralizer_of_isOrbitExtension i a he
    rw [← hj.2] at hg
    exact hg
  have hk : (quotientAction i a j hj).orbit c ≫ j.hom.hom =
      T ◁ AffineLine.unitInclusion B ≫ e := by
    apply AutomorphicAction.hom_ext_of_local_quotient_lift (CommGroupScheme.groupHom a)
      (snd T (Gm B).X)
    intro V b s hb
    have hb' : ∀ {Y : Over B} (f : T ⊗ (Gm B).X ⟶ Y),
        b ≫ f = lift (b ≫ fst T (Gm B).X) s ≫
          T ◁ (CommGroupScheme.groupHom a).hom.hom ≫ f := by
      intro Y f
      rw [← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [hb]
    rw [hb' ((quotientAction i a j hj).orbit c ≫ j.hom.hom),
      hb' (T ◁ AffineLine.unitInclusion B ≫ e), whiskerLeft_quotientAction_orbit_comp, ← Category.assoc (T ◁ _),
      ← whiskerLeft_comp, he]
  obtain ⟨e', he'⟩ := AffineLine.exists_lift_of_unitInclusion j.hom.hom e _ hk
  refine ⟨c, ⟨e', (cancel_mono j.hom.hom).mp ?_, ?_⟩, rfl⟩
  · rw [Category.assoc, he', hk]
  · rw [← cancel_mono j.hom.hom, ← Dynamic.evalZero_comp, he', he0, MonObj.one_comp]

/-- The image of every identity-limit point of the descended action lies in the
root functor. -/
theorem map_le_subgroup :
    (quotientAction i a j hj).unipotent.map j ≤ subgroup i a := by
  intro T x hx
  obtain ⟨c, ⟨e', he', he0'⟩, rfl⟩ := SubgroupFunctor.mem_map.mp hx
  refine ⟨e' ≫ j.hom.hom, ?_, ?_⟩
  · rw [IsOrbitExtension, whiskerLeft_comp, Category.assoc,
      ← Category.assoc (T ◁ AffineLine.unitInclusion B), he',
      whiskerLeft_quotientAction_orbit_comp]
  · rw [Dynamic.evalZero_comp, he0', MonObj.one_comp]

end RepresentedCentralizer

/-- The intrinsic relative root functor is the image of the identity-limit functor of
the descended multiplicative-group action, on every test scheme. -/
theorem quotientActionComparison : QuotientActionComparisonStatement.{u} := by
  intro B S G C i a j hj hjc _ _ _
  exact le_antisymm (subgroup_le_map i a j hj hjc) (map_le_subgroup i a j hj)

end Langlands.GroupScheme.RelativeRoot
