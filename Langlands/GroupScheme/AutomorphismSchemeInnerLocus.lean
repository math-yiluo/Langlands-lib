import Langlands.GroupScheme.AutomorphismScheme
import Langlands.GroupScheme.SubgroupIntersection
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Inner-action loci from a supplied automorphism group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.GroupAutomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupAutomorphismScheme G)

/-- The inverse image of an acting subgroup in a supplied full automorphism
group. It is defined for any two automorphic actions. -/
def innerLocus (a : AutomorphicAction H G) (c : AutomorphicAction A G) :
    GroupScheme S :=
  pullback (I.classifyAction a) (I.classifyAction c)

/-- Projection of the inner-action locus to the original acting group. -/
def innerLocusInclusion (a : AutomorphicAction H G) (c : AutomorphicAction A G) :
    I.innerLocus a c ⟶ H :=
  pullback.fst _ _

/-- The action on the inner locus factors through the second acting group. -/
def innerLocusInnerHom (a : AutomorphicAction H G) (c : AutomorphicAction A G) :
    I.innerLocus a c ⟶ A :=
  pullback.snd _ _

/-- The two restricted actions agree on the pullback. -/
theorem innerLocus_compatibility (a : AutomorphicAction H G)
    (c : AutomorphicAction A G) :
    c.restrict (I.innerLocusInnerHom a c) =
      a.restrict (I.innerLocusInclusion a c) := by
  apply (I.classifyAction_eq_iff _ _).mp
  rw [I.classifyAction_restrict, I.classifyAction_restrict]
  exact pullback.condition.symm

/-- The projection is open if the second action defines an open subgroup
of the supplied full automorphism group. -/
theorem innerLocusInclusion_isOpenImmersion (a : AutomorphicAction H G)
    (c : AutomorphicAction A G)
    (hc : IsOpenImmersion (I.classifyAction c).hom.hom.left) :
    IsOpenImmersion (I.innerLocusInclusion a c).hom.hom.left :=
  MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme
      (I.classifyAction a) (I.classifyAction c)).flip hc

/-- The projection is closed if the second action defines a closed subgroup
of the supplied full automorphism group. -/
theorem innerLocusInclusion_isClosedImmersion (a : AutomorphicAction H G)
    (c : AutomorphicAction A G)
    (hc : IsClosedImmersion (I.classifyAction c).hom.hom.left) :
    IsClosedImmersion (I.innerLocusInclusion a c).hom.hom.left :=
  MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme
      (I.classifyAction a) (I.classifyAction c)).flip hc

/-- Every compatible pair of acting homomorphisms has a unique lift to the
inner-action locus. No hypotheses on the test group scheme are needed. -/
theorem innerLocus_universal (a : AutomorphicAction H G)
    (c : AutomorphicAction A G) (L : GroupScheme S)
    (h : L ⟶ H) (x : L ⟶ A)
    (hx : c.restrict x = a.restrict h) :
    ∃! f : L ⟶ I.innerLocus a c,
      f ≫ I.innerLocusInclusion a c = h ∧
        f ≫ I.innerLocusInnerHom a c = x := by
  have he : h ≫ I.classifyAction a = x ≫ I.classifyAction c := by
    simpa only [I.classifyAction_restrict] using
      congrArg I.classifyAction hx.symm
  refine ⟨pullback.lift h x he, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩,
    ?_⟩
  intro f hf
  apply pullback.hom_ext
  · exact hf.1.trans (pullback.lift_fst _ _ _).symm
  · exact hf.2.trans (pullback.lift_snd _ _ _).symm

/-- A supplied full automorphism group with a clopen second acting subgroup
gives the clopen universal inner restriction of every action. -/
theorem exists_innerActionLocus (a : AutomorphicAction H G)
    (c : AutomorphicAction A G)
    (hco : IsOpenImmersion (I.classifyAction c).hom.hom.left)
    (hcc : IsClosedImmersion (I.classifyAction c).hom.hom.left) :
    ∃ (K : GroupScheme S) (j : K ⟶ H) (φ : K ⟶ A),
      IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left ∧
      c.restrict φ = a.restrict j ∧
      ∀ (L : GroupScheme S) (h : L ⟶ H) (x : L ⟶ A),
        c.restrict x = a.restrict h →
        ∃! f : L ⟶ K, f ≫ j = h ∧ f ≫ φ = x := by
  exact ⟨I.innerLocus a c, I.innerLocusInclusion a c, I.innerLocusInnerHom a c,
    I.innerLocusInclusion_isOpenImmersion a c hco,
    I.innerLocusInclusion_isClosedImmersion a c hcc,
    I.innerLocus_compatibility a c, I.innerLocus_universal a c⟩

end Langlands.GroupScheme.GroupAutomorphismScheme
