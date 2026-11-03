import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Rational.RootSubgroupStability

/-! # Stability of dynamic subgroup functors under a commutative acting group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Act on an affine-line family by a point pulled back from its test scheme. -/
def actOnAffineLine (a : AutomorphicAction H G) {T : Over S}
    (h : T ⟶ H.X) (e : T ⊗ AffineLine.scheme S ⟶ G.X) :
    T ⊗ AffineLine.scheme S ⟶ G.X :=
  a.act (fst T (AffineLine.scheme S) ≫ h) e

section CommutativeSource

variable {A : CommGroupScheme S} (a : AutomorphicAction A.toGrp G)
    (j : (Gm S).toGrp ⟶ A.toGrp)

/-- The whole commutative acting group commutes with the restricted orbit. -/
theorem restrict_orbit_act {T : Over S} (h : T ⟶ A.X) (g : T ⟶ G.X) :
    (a.restrict j).orbit (a.act h g) =
      a.act (fst T (Gm S).X ≫ h) ((a.restrict j).orbit g) := by
  simp only [orbit, a.naturality, restrict_act]
  rw [← a.act_mul_left, ← a.act_mul_left, mul_comm]

/-- Acting on an extension by a constant point of the whole commutative group
extends the orbit of the acted-on point. -/
theorem restrict_isOrbitExtension_act {T : Over S}
    (h : T ⟶ A.X) {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : (a.restrict j).IsOrbitExtension g e) :
    (a.restrict j).IsOrbitExtension (a.act h g)
      (a.actOnAffineLine h e) := by
  change T ◁ AffineLine.unitInclusion S ≫
    a.act (fst T (AffineLine.scheme S) ≫ h) e = _
  rw [a.naturality, whiskerLeft_fst_assoc, he, restrict_orbit_act]

/-- The whole commutative group acts simultaneously on points and their limits. -/
theorem restrict_hasLimit_act {T : Over S} (h : T ⟶ A.X)
    {g l : T ⟶ G.X} (hg : (a.restrict j).HasLimit g l) :
    (a.restrict j).HasLimit (a.act h g) (a.act h l) := by
  obtain ⟨e, he, he0⟩ := hg
  exact ⟨a.actOnAffineLine h e,
    restrict_isOrbitExtension_act a j h he, by rw [actOnAffineLine, evalZero_act, he0]⟩

/-- Dynamic parabolic functors for a restriction are stable under the whole
commutative acting group, on every test scheme. -/
theorem parabolic_restrict_isStable : a.IsStable (a.restrict j).parabolic := by
  intro T h g hg
  obtain ⟨e, he⟩ := hg
  exact ⟨_, restrict_isOrbitExtension_act a j h he⟩

/-- Dynamic centralizer functors for a restriction are stable under the whole
commutative acting group. -/
theorem centralizer_restrict_isStable : a.IsStable (a.restrict j).centralizer :=
  fixed_restrict_isStable a j

/-- Dynamic identity-limit functors for a restriction are stable under the whole
commutative acting group. -/
theorem unipotent_restrict_isStable : a.IsStable (a.restrict j).unipotent := by
  intro T h g hg
  change (a.restrict j).HasLimit (a.act h g) 1
  simpa only [a.act_one] using restrict_hasLimit_act a j h hg

end CommutativeSource

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {A : CommGroupScheme S} {G : GroupScheme S}
    (i : A.toGrp ⟶ G) (j : (Gm S).toGrp ⟶ A.toGrp)

/-- The cocharacter parabolic is stable under conjugation by its commutative
acting group, without a torus or smoothness assumption. -/
theorem parabolic_isStable_conjugation :
    (AutomorphicAction.conjugation i).IsStable (parabolic (j ≫ i)) := by
  have h := AutomorphicAction.parabolic_restrict_isStable
    (AutomorphicAction.conjugation i) j
  rw [AutomorphicAction.restrict_conjugation,
    ← AutomorphicAction.cocharacterAction_eq_conjugation,
    AutomorphicAction.cocharacterAction_parabolic] at h
  exact h

/-- The cocharacter centralizer is stable under conjugation by the commutative
acting group, on every test scheme. -/
theorem centralizer_isStable_conjugation :
    (AutomorphicAction.conjugation i).IsStable (centralizer (j ≫ i)) := by
  have h := AutomorphicAction.centralizer_restrict_isStable
    (AutomorphicAction.conjugation i) j
  rw [AutomorphicAction.restrict_conjugation,
    ← AutomorphicAction.cocharacterAction_eq_conjugation,
    AutomorphicAction.cocharacterAction_centralizer] at h
  exact h

/-- The cocharacter identity-limit functor is stable under conjugation by the
commutative acting group, on every test scheme. -/
theorem unipotent_isStable_conjugation :
    (AutomorphicAction.conjugation i).IsStable (unipotent (j ≫ i)) := by
  have h := AutomorphicAction.unipotent_restrict_isStable
    (AutomorphicAction.conjugation i) j
  rw [AutomorphicAction.restrict_conjugation,
    ← AutomorphicAction.cocharacterAction_eq_conjugation,
    AutomorphicAction.cocharacterAction_unipotent] at h
  exact h

end Langlands.GroupScheme.Dynamic
