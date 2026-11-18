import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionActionReduction
import Langlands.GroupScheme.Torus.DiagonalizableRigidityProof
import Langlands.GroupScheme.AutomorphicAction.CentralDifference

/-! # Proof: connected groups act trivially on central extensions of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open MultiplicativeTypeExtensionAction in
/-- **Milne, *Algebraic Groups*, Corollary 12.41 (with `N` central).** A connected algebraic
group acting on a central extension of a group of multiplicative type by a group of
multiplicative type, preserving the central subgroup, acts trivially. -/
theorem multiplicativeTypeExtensionAction : MultiplicativeTypeExtensionActionStatement.{u} := by
  intro k _ G H N Q j p hGft hGqc hGc _ hHqc hj hc hp hN hQ a ha T g x
  have hRig := diagonalizableRigidity.{u}
  have hNfix : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (n : T ⟶ N.X),
      a.act g (n ≫ j.hom.hom) = n ≫ j.hom.hom :=
    fun _ g n => act_comp_eq hRig hGft hGqc hGc hj hN a ha g n
  have hQfix : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
      a.act g x ≫ p.hom.hom = x ≫ p.hom.hom :=
    fun _ g x => act_comp_quotient hRig hGft hGqc hGc hHqc hp hQ a ha g x
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffine Q.X.left := hQ.isAffine
  have : QuasiCompact p.hom.hom.left := quasiCompact_quotient
  have : Flat p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2.1
  let ψ := AutomorphicAction.centralDifference a j p hp.2.2.2 hQfix hNfix
  refine act_eq_of_difference (j := j) (p := p) a ψ (fun T g x => ?_) (fun T g q => ?_) g x
  · have h := AutomorphicAction.lift_centralDifference_comp a j p hp.2.2.2 hQfix hNfix g x
    rw [Category.assoc] at h
    rw [h, mul_inv_cancel_left]
  · have hF : HomFamily.IsHomFamily (U := G.X) (fun _ g q => lift g q ≫ ψ) :=
      ⟨fun _ g q q' => AutomorphicAction.centralDifference_mul a j p hp.2.2.2 hQfix hNfix hc
          g q q',
        fun f g q => by rw [← Category.assoc, comp_lift]⟩
    exact homFamily_eq hRig hGft hGqc hGc hQ hN hF g q

end Langlands.GroupScheme
