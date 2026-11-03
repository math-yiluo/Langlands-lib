import Langlands.GroupScheme.Rational.RootSubgroup

/-! # Torus stability of intrinsic relative root subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- Commutativity of the acting group makes the relative-root orbit equivariant. -/
theorem orbit_conjugation {T : Over B} (s : T ⟶ S.X) (g : T ⟶ G.X) :
    orbit i ((AutomorphicAction.conjugation i).act s g) =
      (AutomorphicAction.conjugation i).act (fst T S.X ≫ s) (orbit i g) := by
  unfold orbit
  rw [AutomorphicAction.naturality, ← AutomorphicAction.act_mul_left,
    mul_comm, AutomorphicAction.act_mul_left]

/-- Conjugate an affine-line extension by the constant pullback of a torus point. -/
def conjugateExtension {T : Over B} (s : T ⟶ S.X)
    (e : T ⊗ AffineLine.scheme B ⟶ G.X) :
    T ⊗ AffineLine.scheme B ⟶ G.X :=
  (AutomorphicAction.conjugation i).act (fst T (AffineLine.scheme B) ≫ s) e

/-- Conjugation preserves an actual extension through the same character. -/
theorem IsOrbitExtension.conjugate {T : Over B} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme B ⟶ G.X}
    (he : IsOrbitExtension i a g e) (s : T ⟶ S.X) :
    IsOrbitExtension i a ((AutomorphicAction.conjugation i).act s g)
      (conjugateExtension i s e) := by
  rw [IsOrbitExtension, conjugateExtension, AutomorphicAction.naturality,
    whiskerLeft_fst_assoc, he, orbit_conjugation]

/-- Zero evaluation of the conjugated extension is conjugation of its zero value. -/
theorem evalZero_conjugateExtension {T : Over B} (s : T ⟶ S.X)
    (e : T ⊗ AffineLine.scheme B ⟶ G.X) :
    Dynamic.evalZero (conjugateExtension i s e) =
      (AutomorphicAction.conjugation i).act s (Dynamic.evalZero e) := by
  unfold Dynamic.evalZero conjugateExtension
  rw [AutomorphicAction.naturality, lift_fst_assoc]
  simp only [Category.id_comp]

/-- The intrinsic root functor is stable under its whole torus on every test.
No realization, smoothness, field, or root hypothesis is required. -/
theorem subgroup_isStable :
    (AutomorphicAction.conjugation i).IsStable (subgroup i a) := by
  intro T s g hg
  obtain ⟨e, he, he0⟩ := hg
  refine ⟨conjugateExtension i s e, he.conjugate i a s, ?_⟩
  rw [evalZero_conjugateExtension, he0, AutomorphicAction.act_one]

end Langlands.GroupScheme.RelativeRoot
