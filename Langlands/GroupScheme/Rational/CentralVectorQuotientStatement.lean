import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.Characters
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Central equivariant vector subgroups and smooth unipotent quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Coordinates

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))}

/-- Natural vector coordinates in which the actual action is linear over every
test's ring of global functions. Several distinct weights, including zero,
are allowed. -/
def IsLinearVectorCoordinates (a : AutomorphicAction H V) {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))) : Prop :=
  IsNaturalVectorCoordinates e ∧
    ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (c : Γ(T.left, ⊤)) (v : T ⟶ V.X),
      (e T (a.act h ((e T).symm
        (Multiplicative.ofAdd (c • (e T v).toAdd))))).toAdd =
        c • (e T (a.act h v)).toAdd

end Coordinates

/-- The central vector-subgroup step in CGP 3.3.11, after passing to an
algebraically closed field. The subgroup and action are actual scheme data. -/
def CentralStableVectorSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    IsUnipotent G → SubgroupFunctor.range (𝟙 G) ≠ ⊥ →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
      ∃ (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G)
        (bZ : AutomorphicAction S.toGrp Z) (n : ℕ)
        (e : ∀ T : Over (Spec (CommRingCat.of k)),
          (T ⟶ Z.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))),
        IsClosedSubgroup z ∧ Smooth Z.X.hom ∧ IsAffineHom Z.X.hom ∧
        ConnectedSpace Z.X.left ∧ IsUnipotent Z ∧ IsCentral z ∧
        b.IsStable (SubgroupFunctor.range z) ∧ SubgroupFunctor.range z ≠ ⊥ ∧
        0 < n ∧ SmoothOfRelativeDimension n Z.X.hom ∧
        IsLinearVectorCoordinates bZ e ∧
        ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ Z.X),
          bZ.act s v ≫ z.hom.hom = b.act s (v ≫ z.hom.hom)

/-- A given smooth positive-dimensional central stable subgroup has an actual
equivariant smooth fppf quotient, with the dimension decrease needed for
induction. This quotient target is over every field. -/
def CentralSmoothQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    IsUnipotent G → IsClosedSubgroup z → Smooth Z.X.hom →
    ConnectedSpace Z.X.left → IsCentral z →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (b : AutomorphicAction S.toGrp G) (bZ : AutomorphicAction S.toGrp Z),
    (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ Z.X),
      bZ.act s v ≫ z.hom.hom = b.act s (v ≫ z.hom.hom)) →
    ∀ (d n : ℕ), SmoothOfRelativeDimension d G.X.hom →
    SmoothOfRelativeDimension n Z.X.hom → 0 < n →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
        (bQ : AutomorphicAction S.toGrp Q) (m : ℕ),
        IsAffineHom Q.X.hom ∧ Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
        IsUnipotent Q ∧ IsFppfQuotient (SubgroupFunctor.range z) q ∧
        Smooth q.hom.hom.left ∧ SmoothOfRelativeDimension n q.hom.hom.left ∧
        SmoothOfRelativeDimension m Q.X.hom ∧ d = n + m ∧ m < d ∧
        ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
          bQ.act s (g ≫ q.hom.hom) = b.act s g ≫ q.hom.hom

/-- Geometric prerequisites for the central-subgroup dimension induction in
CGP 3.3.11. These are proposition targets, not proofs of their assertions. -/
def CentralVectorQuotientStatement : Prop :=
  CentralStableVectorSubgroupStatement.{u} ∧ CentralSmoothQuotientStatement.{u}

end Langlands.GroupScheme.RelativeRoot
