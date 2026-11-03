import Langlands.GroupScheme.Rational.SemistandardIntersection
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # The general semistandard parabolic intersection target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The common maximal split torus lifts to a closed centralizer representative,
and its lift lies in the other parabolic on every test scheme. -/
theorem IsMaximalSplitTorus.exists_lift_to_centralizer_parabolic
    {k : Type u} [Field k] {G M : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (α β : cocharacterLattice T)
    {j : M ⟶ G}
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    ∃ iM : T.toGrp ⟶ M,
      IsMaximalSplitTorus iM ∧ iM ≫ j = i ∧
        SubgroupFunctor.range iM ≤
          (Dynamic.parabolic (CommGroupScheme.groupHom β ≫ i)).comap j := by
  obtain ⟨iM, hiM, hcomp⟩ := hi.exists_lift hj hjc
    ((range_le_torusCentralizer i).trans
      (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom α)))
  refine ⟨iM, hiM, hcomp, ?_⟩
  intro X x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [SubgroupFunctor.mem_comap, Category.assoc, ← Grp.comp_hom_hom, hcomp]
  exact range_le_dynamicParabolic i (CommGroupScheme.groupHom β) X ⟨t, rfl⟩

/-- Two cocharacters of a common maximal split torus give the general
semistandard intersection parabolic, its actual Levi and geometric radical,
and both displayed products on every test scheme. No nesting is assumed. -/
def DynamicSemistandardIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ α β : cocharacterLattice T,
        let χ := CommGroupScheme.groupHom α ≫ i
        let ψ := CommGroupScheme.groupHom β ≫ i
        ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
          (Dynamic.centralizer χ).IsRepresentedBy j → IsClosedSubgroup j →
            SubgroupFunctor.IsParabolicWithLeviAndRadical
                ((Dynamic.parabolic ψ).comap j)
                ((Dynamic.centralizer ψ).comap j)
                ((Dynamic.unipotent ψ).comap j) ∧
              SubgroupFunctor.SemistandardIntersectionProducts
                (Dynamic.centralizer χ) (Dynamic.unipotent χ)
                (Dynamic.parabolic ψ) (Dynamic.centralizer ψ) (Dynamic.unipotent ψ) ∧
              ∃ iM : T.toGrp ⟶ M,
                IsMaximalSplitTorus iM ∧ iM ≫ j = i ∧
                  SubgroupFunctor.range iM ≤ (Dynamic.parabolic ψ).comap j

end Langlands.GroupScheme
