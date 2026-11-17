import Langlands.GroupScheme.Absolute.TorusCentralizerBorelContainmentStatement
import Langlands.GroupScheme.Cartan.StructureProof
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Maximal-torus centralizers lie in every Borel containing the torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected closed subgroup of a maximal-torus centralizer lies in
each Borel subgroup containing that torus. -/
theorem torusCentralizerBorelContainment :
    TorusCentralizerBorelContainmentStatement.{u} := by
  intro k _ _ G _ _ _ T j hj B b hb hTb H h _ _ hH
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, c, hCartan, hc⟩ := exists_isCartanSubgroup_of_isMaximalTorus hj
  obtain ⟨hsm, hconn, hnil⟩ := cartanStructure k G C c hCartan
  have hsplit : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hsplit.exists_cocharacter_centralizer j
  have hcχ : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy c := by
    rw [hν]
    exact hc
  have hχB : SubgroupFunctor.range (CommGroupScheme.groupHom ν ≫ j) ≤
      SubgroupFunctor.range b := by
    intro V x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply hTb V
    exact SubgroupFunctor.mem_range.mpr
      ⟨t ≫ (CommGroupScheme.groupHom ν).hom.hom, by
        rw [Grp.comp_hom_hom, Category.assoc]⟩
  obtain ⟨D, d, hd, hDB⟩ :=
    centralizerBorelIntersection k G (CommGroupScheme.groupHom ν ≫ j)
      C c hCartan.isClosedSubgroup hcχ hsm hconn B b hb hχB
  have : IsIso d :=
    hd.maximal C (𝟙 C) d (IsClosedSubgroup.of_iso (Iso.refl C)) hsm hconn
      hnil.isSolvableGroupScheme (Category.comp_id d)
  have heq : SubgroupFunctor.range (d ≫ c) = SubgroupFunctor.range c :=
    SubgroupFunctor.range_iso_comp (asIso d) c
  rw [heq] at hDB
  rw [← hc.2] at hH
  exact hH.trans hDB

end Langlands.GroupScheme
