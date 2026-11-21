import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Rational.MaximalSplitGeneratedCell
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Central homomorphisms factor through every standard Levi

The standard Levi of a parabolic root presentation is the common dynamic centralizer of the
standard cocharacters of the maximal split torus. The image of a central homomorphism
centralizes every torus, so it lies in that intersection. Representability of the Levi then
factors the homomorphism through it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}

/-- The image of a central homomorphism centralizes every torus, on every test scheme. -/
theorem IsCentral.range_le_torusCentralizer {i : Z ⟶ G} (hi : IsCentral i)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (t : T.toGrp ⟶ G) :
    SubgroupFunctor.range i ≤ torusCentralizer t := by
  intro U g hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  intro V c s
  have hc := hi V (c ≫ y)
  rw [Category.assoc] at hc
  exact commute_of_mem_center hc _

namespace ParabolicRootPresentation

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

include r in
/-- The image of a central homomorphism lies in the specified standard Levi. -/
theorem range_le_levi_of_isCentral {i : Z ⟶ G} (hi : IsCentral i) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range (l ≫ p) := by
  rw [r.isCompatible.levi_eq]
  intro U g hg
  change g ∈ ⨅ (zeta : cocharacterLattice r.data.T)
    (_ : IsStandardCocharacter r.data.i r.data.ν r.data.J zeta),
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ r.data.i)).carrier U
  simp only [Subgroup.mem_iInf]
  intro zeta _
  exact MaximalSplitSubgroup.torusCentralizer_le_centralizer_cocharacter r.data.i zeta U
    (hi.range_le_torusCentralizer r.data.i U hg)

include r in
/-- **Central homomorphisms factor through the Levi.** Every central homomorphism into `G`
factors through the specified Levi `l ≫ p` of a parabolic root presentation. -/
theorem exists_levi_factor_of_isCentral {i : Z ⟶ G} (hi : IsCentral i) :
    ∃ j : Z ⟶ M, j ≫ l ≫ p = i := by
  have hcl := r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  let := hcl.mono
  have hrep : (SubgroupFunctor.range (l ≫ p)).IsRepresentedBy (l ≫ p) :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact ⟨hrep.factorHom i (r.range_le_levi_of_isCentral hi),
    SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _⟩

/-- Every central homomorphism into `G` factors through the specified Levi of any parabolic
root presentation. -/
def CentralLeviFactorStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P M Z : GroupScheme (Spec (CommRingCat.of k)))
    (A : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M), ParabolicRootPresentation p l a →
    ∀ i : Z ⟶ G, IsCentral i → ∃ j : Z ⟶ M, j ≫ l ≫ p = i

theorem centralLeviFactor : CentralLeviFactorStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ r _ hi => r.exists_levi_factor_of_isCentral hi

end ParabolicRootPresentation

end Langlands.GroupScheme
