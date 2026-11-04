import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.SubgroupFunctor.FppfImage

/-! # Semigroup images under possibly nonsmooth adjoint quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The actual semigroup restriction of an equivariant adjoint quotient is
fppf over an algebraically closed field when zero belongs to the semigroup.
No smoothness of the quotient map or its full central kernel is assumed. -/
def SemigroupAdjointImageStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    (hAffG : IsAffineHom G.X.hom) (hAffQ : IsAffineHom Q.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp →
    ∀ (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp Q)
      (q : G ⟶ Q), IsAdjointQuotient q →
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
        b.act s g ≫ q.hom.hom = c.act s (g ≫ q.hom.hom)) →
      letI := hAffG
      letI := hAffQ
      ∀ A : AddSubsemigroup (characterLattice S), 0 ∈ A →
        SubgroupFunctor.IsFppfImage (semigroupSubgroup b A) (semigroupSubgroup c A) q

section FullPreimage

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The adjoint image statement and full-centre containment give the all-test
inverse-image identity without assuming that the centre is smooth. -/
theorem semigroupSubgroup_comap_eq_of_adjointImage
    (hImage : SemigroupAdjointImageStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp Q)
    (q : G ⟶ Q) (hq : IsAdjointQuotient q)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
      b.act s g ≫ q.hom.hom = c.act s (g ≫ q.hom.hom))
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A)
    (hcenter : center G ≤ semigroupSubgroup b A) :
    (semigroupSubgroup c A).comap q = semigroupSubgroup b A := by
  have himage := hImage k G Q inferInstance inferInstance S hS b c q hq heq A hzero
  apply himage.comap_eq_of_kernel_le
  rwa [hq.kernel_range_eq_center]

end FullPreimage

end Langlands.GroupScheme.RelativeRoot
