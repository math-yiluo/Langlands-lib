import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.Statement

/-! # Statements on minimal rational parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A generic cocharacter of a maximal split torus defines a minimal rational parabolic
subgroup functor. Minimality is tested on every scheme over the ground field. -/
def GenericMinimalParabolicStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i → ∀ ν : cocharacterLattice T,
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν →
      IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))

/-- Any two minimal parabolic subgroups of a connected reductive group over a field
are conjugate by a rational point, as actual subgroup schemes. -/
def MinimalParabolicConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P P' : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (j' : P' ⟶ G),
      IsMinimalParabolicSubgroup j → IsMinimalParabolicSubgroup j' →
      ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (e : P ≅ P'),
        j ≫ (G.innerIso g).hom = e.hom ≫ j'

/-- Every rational parabolic subgroup of a connected reductive group contains a minimal
rational parabolic subgroup, with containment on all test schemes. -/
def ParabolicContainsMinimalStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (j' : Q ⟶ G),
        IsMinimalParabolicSubgroup j' ∧ SubgroupFunctor.range j' ≤ SubgroupFunctor.range j

end Langlands.GroupScheme
