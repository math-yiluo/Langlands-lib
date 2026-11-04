import Langlands.GroupScheme.CentralIsogeny.FrobeniusKernel
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient

/-! # Central isogenies killing exactly the tangent space of the full centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section KernelTangent

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

/-- The actual tangent submodule of the actual kernel is the kernel of the
actual linear differential, including on nonreduced coefficient algebras. -/
theorem lie_range_kernelι_eq_ker_targetMapLinear :
    (SubgroupFunctor.range (kernelι q)).lie A =
      LinearMap.ker (Lie.targetMapLinear q A) := by
  apply Submodule.ext
  intro X
  rw [SubgroupFunctor.mem_lie, mem_range_kernelι_iff, LinearMap.mem_ker]
  constructor
  · intro h
    apply Additive.toMul.injective
    exact Subtype.ext h
  · intro h
    exact congrArg (fun Y : Additive (lieKernel H A) => Y.toMul.val) h

end KernelTangent

/-- In positive characteristic, a smooth affine group admits a central
isogeny whose differential kernel on every algebra is precisely the tangent
submodule of its full scheme-theoretic centre. -/
theorem exists_centralIsogeny_ker_targetMapLinear_eq_center_lie
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (hp : 1 < p)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
      (_ : Smooth Q.X.hom) (ha : IsAffineHom Q.X.hom),
      letI : IsAffineHom Q.X.hom := ha
      IsCentralIsogeny q ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A],
          LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A := by
  obtain ⟨N, i, hi, hfin, hc, hn, ht⟩ :=
    CentralFrobeniusKernel.exists_subgroup k p hp G
  obtain ⟨Q, q, hs, ha, hq, hr⟩ :=
    exists_centralIsogeny_of_finite_central_subgroup k G N i hi hfin hc hn
  refine ⟨Q, q, hs, ha, hq, ?_⟩
  intro A _ _
  rw [← lie_range_kernelι_eq_ker_targetMapLinear, hr]
  exact ht A

/-- Connectedness is preserved by the preceding finite surjective quotient. -/
theorem exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (hp : 1 < p)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
      (_ : Smooth Q.X.hom) (ha : IsAffineHom Q.X.hom)
      (_ : ConnectedSpace Q.X.left),
      letI : IsAffineHom Q.X.hom := ha
      IsCentralIsogeny q ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A],
          LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A := by
  obtain ⟨Q, q, hs, ha, hq, ht⟩ :=
    exists_centralIsogeny_ker_targetMapLinear_eq_center_lie k p hp G
  have hconn : ConnectedSpace Q.X.left :=
    hq.surjective.surj.connectedSpace q.hom.hom.left.continuous
  exact ⟨Q, q, hs, ha, hconn, hq, ht⟩

/-- Universal form of the exact centre-tangent quotient construction. -/
def CenterTangentQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p],
    1 < p →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
        (_ : Smooth Q.X.hom) (ha : IsAffineHom Q.X.hom)
        (_ : ConnectedSpace Q.X.left),
        letI : IsAffineHom Q.X.hom := ha
        IsCentralIsogeny q ∧
          ∀ (A : Type u) [CommRing A] [Algebra k A],
            LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A

theorem centerTangentQuotient : CenterTangentQuotientStatement.{u} := by
  intro k _ p _ hp G _ _ _
  exact exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie k p hp G

end Langlands.GroupScheme
