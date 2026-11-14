import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Rational.NoProperParabolicSplitTorusContainment
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType

/-! # Prescribed split-torus lifts through homomorphisms preserving maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section MaximalTorusImages

variable {k : Type u} [Field k]
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (q : H ⟶ Q)
  (hmax : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
    IsMaximalTorus i → IsMaximalTorus (i ≫ q))

include hmax in
/-- If all maximal tori remain maximal under a homomorphism, every closed
torus has a closed composite. -/
theorem IsClosedSubgroup.comp_of_maximalTorus_images
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ H} (hi : IsClosedSubgroup i) (hT : IsTorus T.toGrp) :
    IsClosedSubgroup (i ≫ q) := by
  obtain ⟨M, j, hj, a, ha⟩ :=
    exists_maximalTorus_extension_of_finiteType H i hT hi
  have haClosed : IsClosedSubgroup a :=
    IsClosedSubgroup.of_comp hj.2.1 (by rwa [ha])
  have hcomp : IsClosedSubgroup (a ≫ (j ≫ q)) :=
    haClosed.comp (hmax M j hj).2.1
  simpa only [← Category.assoc, ha] using hcomp

include hmax in
/-- Closed split tori are maximal if their composite is maximal and every
source maximal torus remains maximal. -/
theorem IsMaximalSplitTorus.of_comp_of_maximalTorus_images
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ H} (hi : IsMaximalSplitTorus (i ≫ q))
    (hclosed : IsClosedSubgroup i) : IsMaximalSplitTorus i := by
  refine ⟨⟨hi.1.1, hclosed⟩, ?_⟩
  intro T' i' hi' f hf
  have hclosed' : IsClosedSubgroup (i' ≫ q) :=
    hi'.2.comp_of_maximalTorus_images q hmax hi'.1.isTorus
  apply hi.2 T' (i' ≫ q) ⟨hi'.1, hclosed'⟩ f
  simpa only [Category.assoc] using congrArg (fun a => a ≫ q) hf

end MaximalTorusImages

section Factorization

variable {k : Type u} [Field k]
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (q : H ⟶ Q)
  (hmax : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
    IsMaximalTorus i → IsMaximalTorus (i ≫ q))
  (hQ : IsConnectedReductive Q)
  (hpar : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ Q),
    IsParabolicSubgroup p → IsIso p)

include hmax hQ hpar in
/-- A prescribed target maximal split torus factors through every source
maximal torus, and its lift is maximal split in the source group. -/
theorem IsMaximalSplitTorus.exists_commFactor_of_maximalTorus_images
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {s : S.toGrp ⟶ Q} (hs : IsMaximalSplitTorus s)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ H} (hi : IsMaximalTorus i) :
    ∃ f : S ⟶ T,
      (CommGroupScheme.groupHom f ≫ i) ≫ q = s ∧
      IsMaximalSplitTorus (CommGroupScheme.groupHom f) ∧
      IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ i) := by
  obtain ⟨-, f, hf, hfMax⟩ :=
    hs.exists_commFactor_of_noProperParabolic hQ hpar (hmax T i hi)
  have hclosed : IsClosedSubgroup (CommGroupScheme.groupHom f ≫ i) :=
    hfMax.1.2.comp hi.2.1
  have hdown : IsMaximalSplitTorus ((CommGroupScheme.groupHom f ≫ i) ≫ q) := by
    simpa only [Category.assoc, hf] using hs
  exact ⟨f, by simpa only [Category.assoc] using hf, hfMax,
    hdown.of_comp_of_maximalTorus_images q hmax hclosed⟩

include hmax hQ hpar in
/-- There is an original-field maximal torus through which the prescribed
target maximal split torus lifts with its same source. -/
theorem IsMaximalSplitTorus.exists_maximalTorus_commFactor_of_maximalTorus_images
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {s : S.toGrp ⟶ Q} (hs : IsMaximalSplitTorus s) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
      IsMaximalTorus i ∧
      ∃ f : S ⟶ T,
        (CommGroupScheme.groupHom f ≫ i) ≫ q = s ∧
        IsMaximalSplitTorus (CommGroupScheme.groupHom f) ∧
        IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ i) := by
  obtain ⟨T₀, i₀, hT₀, hi₀⟩ := TorusExistence.exists_closedTorus H
  obtain ⟨T, i, hi, -⟩ :=
    exists_maximalTorus_extension_of_finiteType H i₀ hT₀ hi₀
  exact ⟨T, i, hi,
    hs.exists_commFactor_of_maximalTorus_images q hmax hQ hpar hi⟩

end Factorization

/-- Prescribed maximal split tori lift through every source maximal torus
when maximal tori are preserved and the target has no proper parabolics. -/
def MaximalTorusImageSplitLiftStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H Q : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (q : H ⟶ Q),
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q)) →
    IsConnectedReductive Q →
    (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ Q),
      IsParabolicSubgroup p → IsIso p) →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ Q),
      IsMaximalSplitTorus s →
      (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
        IsMaximalTorus i →
        ∃ f : S ⟶ T,
          (CommGroupScheme.groupHom f ≫ i) ≫ q = s ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom f) ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ i)) ∧
      (∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ H),
        IsMaximalTorus i ∧
        ∃ f : S ⟶ T,
          (CommGroupScheme.groupHom f ≫ i) ≫ q = s ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom f) ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ i))

theorem maximalTorusImageSplitLift : MaximalTorusImageSplitLiftStatement.{u} := by
  intro k _ H Q _ _ q hmax hQ hpar S s hs
  exact ⟨fun T i hi =>
    hs.exists_commFactor_of_maximalTorus_images q hmax hQ hpar hi,
    hs.exists_maximalTorus_commFactor_of_maximalTorus_images q hmax hQ hpar⟩

end Langlands.GroupScheme
