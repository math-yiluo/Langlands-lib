import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: a single integral reductive realization of a root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The integral-existence consequence of Conrad's Theorem 6.1.16(2): every
finite reduced root datum has one reductive realization over the integers,
with a closed coordinate split torus that is maximal on every field fibre
and with one common full root datum on those fibres. -/
def ChevalleyIntegralExistenceStatement : Prop :=
  ∀ (J X Y : Type u) [Finite J] [AddCommGroup X] [AddCommGroup Y]
    [Module.Finite ℤ X] (P : RootDatum J X Y), P.IsReduced →
      ∃ (G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))) (hG : IsReductive G)
        (I : Type u) (_ : Fintype I)
        (i : splitTorus (Spec (CommRingCat.of (ULift.{u} ℤ))) I ⟶ G)
        (Q : RootDatum J (I → ℤ) (I → ℤ)),
        IsClosedSubgroup i ∧ Nonempty (RootPairing.Equiv P Q) ∧
          (∀ (k : Type u) [Field k] [Algebra (ULift.{u} ℤ) k],
            IsMaximalTorus
              (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
              (splitTorus.baseChangeHom (K := k) G I i)) ∧
          (haveI := hG.isAffineHom
           IsFibrewiseRootDatumOf I G i Q)

end Langlands.GroupScheme
