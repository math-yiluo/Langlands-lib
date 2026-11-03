import Langlands.GroupScheme.SubgroupFunctor.FppfImage
import Langlands.GroupScheme.Rational.SemigroupComparisonStatement

/-! # Full-kernel quotient transport for actual semigroup subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The two independent geometric inputs used for semigroup quotient transport. -/
def SemigroupQuotientTransportPrerequisites : Prop :=
  SemigroupRealizationStatement.{u} ∧ SemigroupSmoothQuotientStatement.{u}

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth Q.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp Q)
    (q : G ⟶ Q)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
      b.act s g ≫ q.hom.hom = c.act s (g ≫ q.hom.hom))
    (hReal : SemigroupRealizationStatement.{u})
    (hQuot : SemigroupSmoothQuotientStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)

include heq hReal hQuot hS hqs hqsurj

/-- The exact smooth quotient statement and realization provide an actual
fppf image for the two semigroup subgroup functors. -/
theorem isFppfImage_semigroupSubgroup (A : AddSubsemigroup (characterLattice S)) :
    SubgroupFunctor.IsFppfImage (semigroupSubgroup b A) (semigroupSubgroup c A) q := by
  obtain ⟨H, i, hi, _⟩ := (hReal k G inferInstance inferInstance S hS b A).1
  obtain ⟨K, j, hj, _⟩ := (hReal k Q inferInstance inferInstance S hS c A).1
  obtain ⟨p, hp, hps, hpsurj⟩ := hQuot k G Q inferInstance inferInstance
    inferInstance inferInstance S hS b c q hqs hqsurj heq A H K i j hi hj
  let : Smooth p.hom.hom.left := hps
  exact ⟨H, K, i, j, p, hi, hj, hp, inferInstance, hpsurj, inferInstance⟩

/-- A semigroup subgroup containing the full quotient kernel is exactly the
inverse image of its quotient semigroup subgroup, on every test scheme. -/
theorem semigroupSubgroup_comap_eq_of_kernel_le
    (A : AddSubsemigroup (characterLattice S))
    (hker : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A) :
    (semigroupSubgroup c A).comap q = semigroupSubgroup b A :=
  (isFppfImage_semigroupSubgroup b c q heq hReal hQuot hS hqs hqsurj A).comap_eq_of_kernel_le
    hker

section Square

variable {H H' : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [Smooth H'.X.hom]
    [IsAffineHom H.X.hom] [IsAffineHom H'.X.hom]
    (d : AutomorphicAction S.toGrp H) (e : AutomorphicAction S.toGrp H')
    (j : H ⟶ G) (p : H ⟶ H') (j' : H' ⟶ Q)

/-- An intersection identity descends through an equivariant commuting
smooth quotient square if each semigroup subgroup contains its full kernel. -/
theorem semigroup_comap_eq_of_smooth_quotient_square
    (hsq : j ≫ q = p ≫ j')
    (heqp : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      d.act s h ≫ p.hom.hom = e.act s (h ≫ p.hom.hom))
    (hps : Smooth p.hom.hom.left) (hpsurj : Surjective p.hom.hom.left)
    (A : AddSubsemigroup (characterLattice S))
    (hkerG : SubgroupFunctor.range (kernelι q) ≤ semigroupSubgroup b A)
    (hkerH : SubgroupFunctor.range (kernelι p) ≤ semigroupSubgroup d A)
    (hcomp : (semigroupSubgroup c A).comap j' = semigroupSubgroup e A) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup d A :=
  SubgroupFunctor.comap_eq_of_quotient_square j q p j' hsq
    (semigroupSubgroup_comap_eq_of_kernel_le b c q heq hReal hQuot hS hqs hqsurj
      A hkerG)
    (semigroupSubgroup_comap_eq_of_kernel_le d e p heqp hReal hQuot hS hps hpsurj
      A hkerH) hcomp

end Square

end Langlands.GroupScheme.RelativeRoot
