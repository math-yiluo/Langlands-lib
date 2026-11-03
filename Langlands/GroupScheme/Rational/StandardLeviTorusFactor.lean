import Langlands.GroupScheme.Rational.StandardLeviAnnihilator
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup

/-! # The ambient torus in an actual standard Levi representative -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))

/-- The ambient torus is contained in the standard Levi on every test scheme. -/
theorem range_le_standardLevi :
    SubgroupFunctor.range i ≤ standardLevi i ν J :=
  (range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν J)

variable {j : L ⟶ G}

/-- The actual factor of the ambient torus through a standard Levi representative. -/
def standardLeviTorusFactor (hj : (standardLevi i ν J).IsRepresentedBy j) :
    T.toGrp ⟶ L :=
  hj.factorHom i (range_le_standardLevi i ν J)

theorem standardLeviTorusFactor_comp
    (hj : (standardLevi i ν J).IsRepresentedBy j) :
    standardLeviTorusFactor i ν J hj ≫ j = i :=
  hj.factorHom_comp _ _

/-- Maximality of the ambient split torus is preserved by this actual factor. -/
theorem IsMaximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor
    (hi : IsMaximalSplitTorus i)
    (hj : (standardLevi i ν J).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    IsMaximalSplitTorus (standardLeviTorusFactor i ν J hj) :=
  hi.isMaximalSplitTorus_factorHom hj hjc (range_le_standardLevi i ν J)

/-- Every closed standard Levi representative contains an actual lift of the
ambient maximal split torus, maximal split in that representative. -/
theorem IsMaximalSplitTorus.exists_standardLevi_lift
    (hi : IsMaximalSplitTorus i)
    (hj : (standardLevi i ν J).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    ∃ iL : T.toGrp ⟶ L, IsMaximalSplitTorus iL ∧ iL ≫ j = i :=
  ⟨standardLeviTorusFactor i ν J hj,
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc,
    standardLeviTorusFactor_comp i ν J hj⟩

/-- A cocharacter whose ambient image is centralized by the standard Levi
becomes central in every actual representative of that Levi. -/
theorem isCentral_standardLeviTorusFactor_of_le
    (hj : (standardLevi i ν J).IsRepresentedBy j)
    (zeta : cocharacterLattice T)
    (hcentralizer : standardLevi i ν J ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)) :
    IsCentral (CommGroupScheme.groupHom zeta ≫ standardLeviTorusFactor i ν J hj) := by
  intro U x V a y
  apply (commute_iff_eq _ _).mpr
  apply hj.1.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  have hy := hcentralizer V (hj.pointsEquiv V y).2
  rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hy
  have hc := hy V (𝟙 V) (a ≫ x)
  have hcomp :
      (standardLeviTorusFactor i ν J hj).hom.hom ≫ j.hom.hom = i.hom.hom :=
    congrArg (fun f : T.toGrp ⟶ G => f.hom.hom)
      (standardLeviTorusFactor_comp i ν J hj)
  simpa only [Grp.comp_hom_hom, Category.assoc, hcomp, Category.id_comp,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe]
    using hc.symm.eq

/-- Every standard cocharacter is central after lifting to the standard Levi. -/
theorem IsStandardCocharacter.isCentral_standardLeviTorusFactor
    (hj : (standardLevi i ν J).IsRepresentedBy j)
    {zeta : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    IsCentral (CommGroupScheme.groupHom zeta ≫ standardLeviTorusFactor i ν J hj) :=
  isCentral_standardLeviTorusFactor_of_le i ν J hj zeta
    (standardLevi_le_dynamicCentralizer i ν hzeta)

/-- Under the published finite-root and standard-cocharacter premises, every
cocharacter annihilating the selected roots is central in the standard Levi. -/
theorem isCentral_standardLeviTorusFactor_of_annihilates
    (hj : (standardLevi i ν J).IsRepresentedBy j)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (zeta : cocharacterLattice T)
    (hzeta : ∀ α ∈ J, latticePairing T α zeta = 0) :
    IsCentral (CommGroupScheme.groupHom zeta ≫ standardLeviTorusFactor i ν J hj) := by
  apply isCentral_standardLeviTorusFactor_of_le i ν J hj zeta
  rw [standardLevi_eq_cocharacterAnnihilatorCentralizer i ν hfinite J hexists]
  intro U g hg
  exact (mem_cocharacterAnnihilatorCentralizer i J).mp hg zeta hzeta

end Langlands.GroupScheme
