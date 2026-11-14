import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Statement: finitely many parabolic types on an étale neighbourhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A reductive group scheme has, étale-locally at each base point, finitely many
relative parabolic subgroups whose pullbacks represent, without repetition, the
rational conjugacy classes of parabolic subgroups over every field-valued point.
This isolates the finite-type step in Conrad (2014), proof of Corollary 5.2.9,
p.157; it does not assert representability or descent of the parabolic functor. -/
def RelativeParabolicEtaleLocalFiniteTypesStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G → ∀ s : S,
    ∃ (R : Type u) (_ : CommRing R) (f : Spec (CommRingCat.of R) ⟶ S),
      Etale f ∧ (∃ x : Spec (CommRingCat.of R), f.base x = s) ∧
      ∃ (n : ℕ) (P : Fin n → GroupScheme (Spec (CommRingCat.of R)))
        (j : ∀ a, P a ⟶ (GroupScheme.baseChange f).obj G),
        (∀ a, IsRelativeParabolicSubgroup (j a)) ∧
        ∀ (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶
          Spec (CommRingCat.of R))
          (Q : GroupScheme (Spec (CommRingCat.of k)))
          (i : Q ⟶ (GroupScheme.baseChange x).obj ((GroupScheme.baseChange f).obj G)),
          IsParabolicSubgroup i →
          ∃! a : Fin n,
            ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
                ((GroupScheme.baseChange x).obj ((GroupScheme.baseChange f).obj G)).X,
              SubgroupFunctor.range
                  (i ≫ (((GroupScheme.baseChange x).obj
                    ((GroupScheme.baseChange f).obj G)).innerIso g).hom) =
                SubgroupFunctor.range ((GroupScheme.baseChange x).map (j a))

end Langlands.GroupScheme
