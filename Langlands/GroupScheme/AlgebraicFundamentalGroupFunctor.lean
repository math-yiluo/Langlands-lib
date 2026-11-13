import Langlands.GroupScheme.AlgebraicFundamentalGroup

/-! # Maps on algebraic fundamental groups from actual torus factorizations -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Choice

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k H) (E : Type u) [Field E] [Algebra k E]

/-- The geometric restriction of `f` to the chosen source torus factors through
an actual maximal torus `b` of the target. -/
def IsTorusFactorization (b : Choice k G) (f : H ⟶ G)
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus) : Prop :=
  (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map f =
    CommGroupScheme.groupHom e ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion

/-- The induced quotient map is determined by every geometric torus factorization.
Existence of a factorization is part of the predicate, to prevent vacuity. -/
def IsInducedMap (c : Choice k G) (f : H ⟶ G)
    (m : a.atChoice E →ₗ[ℤ] c.atChoice E) : Prop :=
  (∃ (b : Choice k G)
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
    a.IsTorusFactorization E b f e) ∧
  ∀ (b : Choice k G)
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
    a.IsTorusFactorization E b f e →
      ∀ ν : a.lattice E,
        m (a.projection E ν) = b.comparison E c (b.projection E (ν ≫ e))

/-- The map selected by the actual geometric restriction law. Its unconditional
existence, uniqueness and functoriality are separate statement obligations. -/
def mapTo (c : Choice k G) (f : H ⟶ G) : a.atChoice E →ₗ[ℤ] c.atChoice E :=
  Classical.epsilon (a.IsInducedMap E c f)

/-- The selection law follows from existence alone. -/
theorem mapTo_spec (c : Choice k G) (f : H ⟶ G)
    (h : ∃ m, a.IsInducedMap E c f m) :
    a.IsInducedMap E c f (a.mapTo E c f) := Classical.epsilon_spec h

end Choice

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  (H G : GroupScheme (Spec (CommRingCat.of k)))
  (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)

/-- The homomorphism on the chosen presentations of algebraic fundamental groups. -/
def fundamentalGroupMap (f : H ⟶ G) :
    fundamentalGroup k H E hH →ₗ[ℤ] fundamentalGroup k G E hG :=
  (chosenChoice k H hH).mapTo E (chosenChoice k G hG) f

end Langlands.GroupScheme.AlgebraicFundamentalGroup
