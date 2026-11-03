import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Mathlib.GroupTheory.Complement

/-! # Actual Levi, radical and product interfaces for semistandard intersections -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A closed smooth connected unipotent normal subgroup whose base change is
the largest such subgroup over an algebraic closure of the ground field. -/
def IsGeometricUnipotentRadical
    {R H : GroupScheme (Spec (CommRingCat.of k))} (r : R ⟶ H) : Prop :=
  IsClosedSubgroup r ∧ Smooth R.X.hom ∧ ConnectedSpace R.X.left ∧ IsUnipotent R ∧
    (SubgroupFunctor.range r).IsNormal ∧
    let B := GroupScheme.baseChange (toAlgebraicClosure k)
    ConnectedSpace (B.obj R).X.left ∧ IsUnipotent (B.obj R) ∧
      (SubgroupFunctor.range (B.map r)).IsNormal ∧
      ∀ (V : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
        (v : V ⟶ B.obj H),
        IsClosedSubgroup v → Smooth V.X.hom → ConnectedSpace V.X.left →
          IsUnipotent V → (SubgroupFunctor.range v).IsNormal →
            SubgroupFunctor.range v ≤ SubgroupFunctor.range (B.map r)

namespace SubgroupFunctor

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual parabolic, reductive Levi and geometric radical representatives,
with their unique all-test Levi decomposition and the displayed ordered product. -/
def IsParabolicWithLeviAndRadical (P L U : SubgroupFunctor G) : Prop :=
  ∃ (H K R : GroupScheme (Spec (CommRingCat.of k)))
    (j : H ⟶ G) (l : K ⟶ H) (r : R ⟶ H),
    P.IsRepresentedBy j ∧ IsParabolicSubgroup j ∧
      IsClosedSubgroup l ∧ IsConnectedReductive K ∧ range (l ≫ j) = L ∧
      IsGeometricUnipotentRadical r ∧ range (r ≫ j) = U ∧
      ∀ X : Over (Spec (CommRingCat.of k)),
        let Hx := P.carrier X
        let Lx := L.carrier X
        let Ux := U.carrier X
        Ux ≤ Hx ∧ Lx ≤ Hx ∧ (Ux.subgroupOf Hx).Normal ∧
          (Ux.subgroupOf Hx).IsComplement' (Lx.subgroupOf Hx) ∧
          (↑Hx : Set (X ⟶ G.X)) =
            (↑Lx : Set (X ⟶ G.X)) * (↑Ux : Set (X ⟶ G.X))

theorem IsParabolicWithLeviAndRadical.isParabolicFunctor
    {P L U : SubgroupFunctor G} (h : IsParabolicWithLeviAndRadical P L U) :
    IsParabolicFunctor P := by
  obtain ⟨H, K, R, j, l, r, hj, hjP, _⟩ := h
  exact ⟨H, j, hjP, hj.2⟩

/-- The two explicit all-test products in Renard V.3.10. -/
def SemistandardIntersectionProducts (M N Q L U : SubgroupFunctor G) : Prop :=
  ∀ X : Over (Spec (CommRingCat.of k)),
    (↑((M ⊓ Q).carrier X) : Set (X ⟶ G.X)) =
        (↑((M ⊓ L).carrier X) : Set (X ⟶ G.X)) *
          (↑((M ⊓ U).carrier X) : Set (X ⟶ G.X)) ∧
      (↑((N ⊓ Q).carrier X) : Set (X ⟶ G.X)) =
        (↑((N ⊓ L).carrier X) : Set (X ⟶ G.X)) *
          (↑((N ⊓ U).carrier X) : Set (X ⟶ G.X))

/-- The actual rational-point formulas are the identity-test specialization. -/
theorem SemistandardIntersectionProducts.identityTest
    {M N Q L U : SubgroupFunctor G} (h : SemistandardIntersectionProducts M N Q L U) :
    let X := Over.mk (𝟙 (Spec (CommRingCat.of k)))
    (↑((M ⊓ Q).carrier X) : Set (X ⟶ G.X)) =
        (↑((M ⊓ L).carrier X) : Set (X ⟶ G.X)) *
          (↑((M ⊓ U).carrier X) : Set (X ⟶ G.X)) ∧
      (↑((N ⊓ Q).carrier X) : Set (X ⟶ G.X)) =
        (↑((N ⊓ L).carrier X) : Set (X ⟶ G.X)) *
          (↑((N ⊓ U).carrier X) : Set (X ⟶ G.X)) :=
  h (Over.mk (𝟙 _))

end SubgroupFunctor

end Langlands.GroupScheme
