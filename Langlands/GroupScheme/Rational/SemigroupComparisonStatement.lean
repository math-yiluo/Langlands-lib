import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # Equivariant semigroup functoriality, smooth quotients and intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Equivariant homomorphisms carry the actual semigroup subgroup functor
into the corresponding semigroup subgroup functor, on every test scheme. -/
def SemigroupFunctorialityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (_hH : Smooth H.X.hom) (_hG : Smooth G.X.hom)
    (hAffH : IsAffineHom H.X.hom) (hAffG : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (c : AutomorphicAction S.toGrp H) (b : AutomorphicAction S.toGrp G)
      (f : H ⟶ G),
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
        c.act s h ≫ f.hom.hom = b.act s (h ≫ f.hom.hom)) →
      letI := hAffH
      letI := hAffG
      ∀ A : AddSubsemigroup (characterLattice S),
        (semigroupSubgroup c A).map f ≤ semigroupSubgroup b A

/-- A smooth equivariant surjection induces an actual smooth surjection
between any representatives of the two semigroup subgroup functors. -/
def SemigroupSmoothQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (_hH : Smooth H.X.hom) (_hG : Smooth G.X.hom)
    (hAffH : IsAffineHom H.X.hom) (hAffG : IsAffineHom G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (c : AutomorphicAction S.toGrp H) (b : AutomorphicAction S.toGrp G)
      (f : H ⟶ G),
      Smooth f.hom.hom.left → Surjective f.hom.hom.left →
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
        c.act s h ≫ f.hom.hom = b.act s (h ≫ f.hom.hom)) →
      letI := hAffH
      letI := hAffG
      ∀ (A : AddSubsemigroup (characterLattice S))
        (Hₐ Gₐ : GroupScheme (Spec (CommRingCat.of k)))
        (j : Hₐ ⟶ H) (l : Gₐ ⟶ G),
        (semigroupSubgroup c A).IsRepresentedBy j →
        (semigroupSubgroup b A).IsRepresentedBy l →
        ∃ p : Hₐ ⟶ Gₐ,
          j ≫ f = p ≫ l ∧ Smooth p.hom.hom.left ∧ Surjective p.hom.hom.left

/-- CGP 3.3.10: intersection with an invariant smooth connected closed
subgroup is the same semigroup subgroup when zero is excluded, or when the
subgroup is solvable, or when it is normal. -/
def SemigroupIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : Smooth G.X.hom) (_hH : Smooth H.X.hom)
    (hAffG : IsAffineHom G.X.hom) (hAffH : IsAffineHom H.X.hom)
    (_hConnH : ConnectedSpace H.X.left)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
      (j : H ⟶ G),
      IsClosedSubgroup j →
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
        c.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) →
      letI := hAffG
      letI := hAffH
      ∀ A : AddSubsemigroup (characterLattice S),
        (0 ∉ A ∨ IsSolvableScheme H ∨ (SubgroupFunctor.range j).IsNormal) →
        (semigroupSubgroup b A).comap j = semigroupSubgroup c A

/-- The three source comparison properties for the actual semigroup functors. -/
def SemigroupComparisonStatement : Prop :=
  SemigroupFunctorialityStatement.{u} ∧ SemigroupSmoothQuotientStatement.{u} ∧
    SemigroupIntersectionStatement.{u}

end Langlands.GroupScheme.RelativeRoot
