import Langlands.GroupScheme.SubgroupFunctor.FppfImage
import Langlands.GroupScheme.SubgroupFunctor.KernelIntersectionDescent
import Langlands.GroupScheme.Rational.SemigroupComparisonStatement
import Langlands.GroupScheme.Rational.SemigroupFunctorialityProof
import Langlands.GroupScheme.Rational.SemigroupSolvableIntersection

/-! # Quotient and kernel transport for actual semigroup subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The two independent geometric inputs used for semigroup quotient transport. -/
def SemigroupQuotientTransportPrerequisites : Prop :=
  SemigroupRealizationStatement.{u} ∧ SemigroupSmoothQuotientStatement.{u}

section FullKernel

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

end FullKernel

section KernelComparison

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H G' H' U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom] [Smooth G'.X.hom]
    [Smooth U.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [IsAffineHom G'.X.hom] [IsAffineHom H'.X.hom] [IsAffineHom U.X.hom]
    (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (b' : AutomorphicAction S.toGrp G') (c' : AutomorphicAction S.toGrp H')
    (d : AutomorphicAction S.toGrp U)
    (j : H ⟶ G) (q : G ⟶ G') (p : H ⟶ H') (j' : H' ⟶ G') (r : U ⟶ H)
    (heqj : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom))
    (heqq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
      b.act s g ≫ q.hom.hom = b'.act s (g ≫ q.hom.hom))
    (heqr : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ U.X),
      d.act s x ≫ r.hom.hom = c.act s (x ≫ r.hom.hom))

include hS heqj heqq heqr

/-- Quotient comparison and comparison on a representative of the full kernel
give semigroup intersection, using only the subgroup's actual fppf image. -/
theorem semigroup_comap_eq_of_fppfImage_of_kernel_comparison
    (hsq : j ≫ q = p ≫ j')
    (hk : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range r)
    (A : AddSubsemigroup (characterLattice S))
    (hImage : SubgroupFunctor.IsFppfImage
      (semigroupSubgroup c A) (semigroupSubgroup c' A) p)
    (hquot : (semigroupSubgroup b' A).comap j' = semigroupSubgroup c' A)
    (hker : (semigroupSubgroup b A).comap (r ≫ j) = semigroupSubgroup d A) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  apply SubgroupFunctor.comap_eq_of_fppfImage_of_kernelIntersection_le j q p j' hsq
    hImage
  · exact semigroupFunctoriality k H G inferInstance inferInstance
      inferInstance inferInstance S hS c b j heqj A
  · exact semigroupFunctoriality k G G' inferInstance inferInstance
      inferInstance inferInstance S hS b b' q heqq A
  · exact hquot
  · apply SubgroupFunctor.kernelIntersection_le_of_comap_le p r hk
    rw [← SubgroupFunctor.comap_comp, hker]
    exact SubgroupFunctor.map_le_iff_le_comap.mp
      (semigroupFunctoriality k U H inferInstance inferInstance
        inferInstance inferInstance S hS d c r heqr A)

variable [Smooth H'.X.hom]

/-- A smooth surjective subgroup quotient supplies the fppf image needed to
lift comparison from its quotient and full represented kernel. The ambient
vertical map need only be equivariant. -/
theorem semigroup_comap_eq_of_smooth_quotient_of_kernel_comparison
    (hReal : SemigroupRealizationStatement.{u})
    (hQuot : SemigroupSmoothQuotientStatement.{u})
    (hsq : j ≫ q = p ≫ j')
    (heqp : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ p.hom.hom = c'.act s (h ≫ p.hom.hom))
    (hps : Smooth p.hom.hom.left) (hpsurj : Surjective p.hom.hom.left)
    (hk : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range r)
    (A : AddSubsemigroup (characterLattice S))
    (hquot : (semigroupSubgroup b' A).comap j' = semigroupSubgroup c' A)
    (hker : (semigroupSubgroup b A).comap (r ≫ j) = semigroupSubgroup d A) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A :=
  semigroup_comap_eq_of_fppfImage_of_kernel_comparison hS b c b' c' d j q p j' r
    heqj heqq heqr hsq hk A
    (isFppfImage_semigroupSubgroup c c' p heqp hReal hQuot hS hps hpsurj A)
    hquot hker

/-- A smooth connected solvable full kernel supplies the kernel comparison
from the independent solvable connectedness input when zero is present. -/
theorem semigroup_comap_eq_of_smooth_quotient_of_solvable_kernel
    [ConnectedSpace U.X.left]
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hsolv : IsSolvableScheme U)
    (hReal : SemigroupRealizationStatement.{u})
    (hQuot : SemigroupSmoothQuotientStatement.{u})
    (hj : IsClosedSubgroup j) (hr : IsClosedSubgroup r)
    (hsq : j ≫ q = p ≫ j')
    (heqp : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ p.hom.hom = c'.act s (h ≫ p.hom.hom))
    (hps : Smooth p.hom.hom.left) (hpsurj : Surjective p.hom.hom.left)
    (hk : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range r)
    (A : AddSubsemigroup (characterLattice S)) (h0 : 0 ∈ A)
    (hquot : (semigroupSubgroup b' A).comap j' = semigroupSubgroup c' A) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  apply semigroup_comap_eq_of_smooth_quotient_of_kernel_comparison
    hS b c b' c' d j q p j' r heqj heqq heqr hReal hQuot
    hsq heqp hps hpsurj hk A hquot
  have hclosed : IsClosedSubgroup (r ≫ j) := by
    let : IsClosedImmersion j.hom.hom.left := hj
    let : IsClosedImmersion r.hom.hom.left := hr
    change IsClosedImmersion (r.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  have heqcomp : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ U.X),
      d.act s x ≫ (r ≫ j).hom.hom = b.act s (x ≫ (r ≫ j).hom.hom) := by
    intro T s x
    change d.act s x ≫ (r.hom.hom ≫ j.hom.hom) =
      b.act s (x ≫ (r.hom.hom ≫ j.hom.hom))
    rw [← Category.assoc, heqr, heqj, Category.assoc]
  exact semigroup_comap_eq_of_solvable_of_zero_mem d hS hConn hsolv b (r ≫ j)
    heqcomp hReal hclosed A h0

end KernelComparison

end Langlands.GroupScheme.RelativeRoot
