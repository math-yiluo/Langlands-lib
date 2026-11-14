import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: local lifting of geometric normalizer points modulo a split torus -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a split reductive group over an arbitrary affine base, each geometric normalizer
point can, modulo the torus, be lifted to a normalizer section on a Zariski neighbourhood.
This is the local consequence of Conrad's Proposition 5.1.6 and Corollary 5.1.11 used in
Corollary 5.2.13(2). All points are written over the original base to avoid choices of
iterated-pullback identifications. -/
def SplitNormalizerGeometricLocalLiftingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Fintype I] (t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
    haveI := hG.isAffineHom
    IsClosedSubgroup t →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t →
    IsFibrewiseRootDatumOf I G t P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G t (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (n : Over.mk x ⟶ G.X),
      n ∈ (SubgroupFunctor.range t).normalizer.carrier (Over.mk x) →
      ∃ V : (Spec (CommRingCat.of R)).Opens, x (IsLocalRing.closedPoint k) ∈ V ∧
        ∃ (a : Over.mk x ⟶ Over.mk V.ι) (nV : Over.mk V.ι ⟶ G.X),
          nV ∈ (SubgroupFunctor.range t).normalizer.carrier (Over.mk V.ι) ∧
            (a ≫ nV) * n⁻¹ ∈ (SubgroupFunctor.range t).carrier (Over.mk x)

end Langlands.GroupScheme
