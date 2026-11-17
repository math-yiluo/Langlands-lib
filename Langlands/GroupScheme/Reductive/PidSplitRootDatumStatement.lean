import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Statement: full split root data and free root spaces over a principal ideal domain -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A fibrewise maximal coordinate split torus of a reductive group over a
principal ideal domain has one full root datum on all field fibres and
free root spaces of rank one. This is derived from Conrad's Definition
5.1.1 and the following remark, p.136. -/
def PidSplitRootDatumStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        haveI := hG.isAffineHom
        IsFibrewiseRootDatumOf I G i P ∧
          ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[
            CommRingCat.of R] CommRingCat.of R)

end Langlands.GroupScheme
