import Langlands.GroupScheme.Chevalley.UnipotentAffineQuotient
import Langlands.GroupScheme.HomogeneousQuotientGroup

/-! # Equivariant normal unipotent quotients from closed vector orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

/-- Over an algebraically closed field, the exact closed-orbit proposition
supplies the affine normal quotient with equivariance and strict dimension
decrease. Closed-subgroup unipotence is an explicit hypothesis. -/
theorem exists_unipotentNormalQuotient
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G Z A : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsUnipotent G) (i : Z ⟶ G)
    (hi : IsClosedSubgroup i) (hZ : IsUnipotent Z)
    (hnormal : (SubgroupFunctor.range i).IsNormal)
    (a : AutomorphicAction A G) (hstable : a.IsStable (SubgroupFunctor.range i))
    {d n : ℕ} (hd : SmoothOfRelativeDimension d G.X.hom)
    (hn : SmoothOfRelativeDimension n Z.X.hom) (hpos : 0 < n) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
      (b : AutomorphicAction A Q) (m : ℕ),
      IsAffineHom Q.X.hom ∧ Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      IsUnipotent Q ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
      Smooth q.hom.hom.left ∧ SmoothOfRelativeDimension n q.hom.hom.left ∧
      SmoothOfRelativeDimension m Q.X.hom ∧ d = n + m ∧ m < d ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ A.X) (g : T ⟶ G.X),
        b.act s (g ≫ q.hom.hom) = a.act s g ≫ q.hom.hom := by
  let : SmoothOfRelativeDimension d G.X.hom := hd
  let : SmoothOfRelativeDimension n Z.X.hom := hn
  let : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let D := unipotentAffineQuotient hclosed k G hG Z i hi
    (SmoothOfRelativeDimension.smooth n Z.X.hom) hZ
  exact D.quotient.exists_action_relativeDimension D.affine hnormal hG a hstable hd hn hpos

end Langlands.GroupScheme.Chevalley
