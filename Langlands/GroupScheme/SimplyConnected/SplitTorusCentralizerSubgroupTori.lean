import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerRootModel
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.HeightExistence

/-! # Compatible maximal tori for subgroups of split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option autoImplicit false

variable {k : Type u} [Field k]
  {G M D : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual ambient/centralizer torus model together with a compatible split
maximal torus of a supplied closed subgroup of the centralizer. -/
structure SplitTorusCentralizerSubgroupTorusModel
    (a : A.toGrp ⟶ G) (j : M ⟶ G) (d : D ⟶ M) where
  rootModel : SplitTorusCentralizerRootModel a j
  subgroupTorus : CommGroupScheme (Spec (CommRingCat.of k))
  subgroup : subgroupTorus.toGrp ⟶ D
  inclusion : subgroupTorus ⟶ rootModel.torus
  isSplit : IsSplitTorus subgroupTorus.toGrp
  isMaximal : IsMaximalTorus subgroup
  inclusion_closed : IsClosedSubgroup (CommGroupScheme.groupHom inclusion)
  inclusion_comp : CommGroupScheme.groupHom inclusion ≫ rootModel.centralizer =
    subgroup ≫ d

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Compatible actual split maximal tori exist for every closed subgroup of an
arbitrary representative of a split-torus centralizer over an algebraically
closed field. No conjugacy theorem or reductivity premise is used. -/
theorem exists_splitTorusCentralizerSubgroupTorusModel [IsAlgClosed k]
    (a : A.toGrp ⟶ G) (ha : IsSplitSubtorus a) (j : M ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (d : D ⟶ M) (hd : IsClosedSubgroup d) :
    Nonempty (SplitTorusCentralizerSubgroupTorusModel a j d) := by
  have hjc : IsClosedSubgroup j := ha.1.isClosedSubgroup_torusCentralizer a hj
  let : IsAffineHom M.X.hom := hjc.isAffineHom
  let : LocallyOfFiniteType M.X.hom := hjc.locallyOfFiniteType
  let : IsAffineHom D.X.hom := hd.isAffineHom
  let : LocallyOfFiniteType D.X.hom := hd.locallyOfFiniteType
  obtain ⟨S, t, ht⟩ := exists_isMaximalTorus D
  have hS : IsSplitTorus S.toGrp :=
    ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨T₀, i₀, hi₀, e, he⟩ :=
    exists_maximalTorus_extension_of_finiteType M (t ≫ d) ht.1 (ht.2.1.comp hd)
  have hT₀ : IsSplitTorus T₀.toGrp :=
    hi₀.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨b, hb⟩ := (hi₀.isMaximalSplitTorus hT₀).exists_factor_of_commute ha.1
    (torusCentralizerFactor a hj)
    ((isCentral_torusCentralizerFactor a hj).commute_values i₀)
  obtain ⟨T, i, hi, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G (i₀ ≫ j) hi₀.1
      (hi₀.2.1.comp hjc)
  let g : A.toGrp ⟶ T.toGrp := b ≫ f
  have hg : g ≫ i = a := by
    change (b ≫ f) ≫ i = a
    rw [Category.assoc, hf, ← Category.assoc, hb, torusCentralizerFactor_comp]
  let iM : T.toGrp ⟶ M :=
    hj.factorHom i (range_le_torusCentralizer_of_factor a i g hg)
  have hiM : iM ≫ j = i := hj.factorHom_comp _ _
  have hinc : (e ≫ f) ≫ iM = t ≫ d := by
    apply hj.hom_ext
    rw [Category.assoc, hiM, Category.assoc, hf, ← Category.assoc, he]
  refine ⟨{
    rootModel := {
      torus := T
      ambient := i
      centralizer := iM
      factor := Additive.ofMul g
      isSplit := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
      ambient_maximal := hi
      centralizer_maximal := IsMaximalTorus.of_comp hjc (hiM.symm ▸ hi)
      factor_closed := IsClosedSubgroup.of_comp hi.2.1 (hg.symm ▸ ha.2)
      centralizer_comp := hiM
      factor_comp := hg }
    subgroupTorus := S
    subgroup := t
    inclusion := Additive.ofMul (e ≫ f)
    isSplit := hS
    isMaximal := ht
    inclusion_closed := IsClosedSubgroup.of_comp
      (IsClosedSubgroup.of_comp hjc (hiM.symm ▸ hi.2.1))
      (hinc.symm ▸ ht.2.1.comp hd)
    inclusion_comp := hinc }⟩

/-- Choose the compatible actual split maximal tori. -/
def splitTorusCentralizerSubgroupTorusModel [IsAlgClosed k]
    (a : A.toGrp ⟶ G) (ha : IsSplitSubtorus a) (j : M ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (d : D ⟶ M) (hd : IsClosedSubgroup d) :
    SplitTorusCentralizerSubgroupTorusModel a j d :=
  Classical.choice (exists_splitTorusCentralizerSubgroupTorusModel a ha j hj d hd)

namespace SplitTorusCentralizerSubgroupTorusModel

variable {a : A.toGrp ⟶ G} {j : M ⟶ G} {d : D ⟶ M}
  (C : SplitTorusCentralizerSubgroupTorusModel a j d)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The closed torus map intertwines the supplied subgroup and ambient maps. -/
theorem inclusion_ambient_comp :
    CommGroupScheme.groupHom C.inclusion ≫ C.rootModel.ambient =
      C.subgroup ≫ d ≫ j := by
  rw [← C.rootModel.centralizer_comp, ← Category.assoc, C.inclusion_comp,
    Category.assoc]

end SplitTorusCentralizerSubgroupTorusModel

end Langlands.GroupScheme
