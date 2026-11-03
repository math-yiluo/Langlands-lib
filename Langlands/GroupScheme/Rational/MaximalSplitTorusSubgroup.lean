import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Maximal split tori inside closed subgroup schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A split subtorus of a closed subgroup is a split subtorus of the ambient group. -/
theorem IsSplitSubtorus.comp {i : T.toGrp ⟶ H} (hi : IsSplitSubtorus i)
    {j : H ⟶ G} (hj : IsClosedSubgroup j) : IsSplitSubtorus (i ≫ j) :=
  ⟨hi.1, hi.2.comp hj⟩

/-- A split subtorus that factors through a closed subgroup is closed in that subgroup. -/
theorem IsSplitSubtorus.of_comp {i : T.toGrp ⟶ H} {j : H ⟶ G}
    (hj : IsClosedSubgroup j) (hi : IsSplitSubtorus (i ≫ j)) :
    IsSplitSubtorus i :=
  ⟨hi.1, IsClosedSubgroup.of_comp hj hi.2⟩

/-- A torus maximal split in the ambient group is maximal split in every closed
subgroup through which its embedding factors. -/
theorem IsMaximalSplitTorus.of_comp {i : T.toGrp ⟶ H} {j : H ⟶ G}
    (hj : IsClosedSubgroup j) (hi : IsMaximalSplitTorus (i ≫ j)) :
    IsMaximalSplitTorus i := by
  refine ⟨IsSplitSubtorus.of_comp hj hi.1, ?_⟩
  intro T' i' hi' f hf
  apply hi.2 T' (i' ≫ j) (hi'.comp hj) f
  rw [← Category.assoc, hf]

/-- The actual lift of an ambient maximal split torus through a closed represented
subgroup remains a maximal split torus. Containment is on every test scheme. -/
theorem IsMaximalSplitTorus.isMaximalSplitTorus_factorHom
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hcontained : SubgroupFunctor.range i ≤ F) :
    IsMaximalSplitTorus (hj.factorHom i hcontained) := by
  apply IsMaximalSplitTorus.of_comp hjc
  rwa [hj.factorHom_comp]

/-- The factorization of an ambient maximal split torus, bundled with its
maximality in the closed represented subgroup and its composite equality. -/
def IsMaximalSplitTorus.lift
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hcontained : SubgroupFunctor.range i ≤ F) :
    {iH : T.toGrp ⟶ H // IsMaximalSplitTorus iH ∧ iH ≫ j = i} :=
  ⟨hj.factorHom i hcontained,
    hi.isMaximalSplitTorus_factorHom hj hjc hcontained,
    hj.factorHom_comp i hcontained⟩

/-- An ambient maximal split torus contained in a closed represented subgroup has
an embedding there, maximal split there, whose composite is the original embedding. -/
theorem IsMaximalSplitTorus.exists_lift
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hcontained : SubgroupFunctor.range i ≤ F) :
    ∃ iH : T.toGrp ⟶ H, IsMaximalSplitTorus iH ∧ iH ≫ j = i :=
  ⟨(hi.lift hj hjc hcontained).val, (hi.lift hj hjc hcontained).property⟩

/-- If a dynamic parabolic contains the dynamic parabolic of a cocharacter of an
ambient maximal split torus, that torus lifts to any closed representative of the
larger parabolic and is maximal split in it. No genericity is needed. -/
theorem IsMaximalSplitTorus.exists_lift_of_parabolic_le
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta)
    {j : H ⟶ G} (hj : (Dynamic.parabolic zeta).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    ∃ iH : T.toGrp ⟶ H, IsMaximalSplitTorus iH ∧ iH ≫ j = i :=
  hi.exists_lift hj hjc
    (((range_le_torusCentralizer i).trans
      (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν))).trans
      ((Dynamic.centralizer_le_parabolic _).trans hP))

end Langlands.GroupScheme
