import Langlands.GroupScheme.Unipotent.NormalMultiplicativeProductStatement
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof
import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.SubgroupFunctor.FppfProductCriterion
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuotients
import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Direct product of complementary normal multiplicative and unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem mono_multiplication_of_disjoint {S : Scheme.{u}} {T U G : GroupScheme S}
    (t : T ⟶ G) (i : U ⟶ G) [Mono t.hom.hom] [Mono i.hom.hom]
    (h : ∀ V : Over S, Disjoint ((SubgroupFunctor.range t).carrier V)
      ((SubgroupFunctor.range i).carrier V)) :
    Mono (subgroupMultiplication t i) := by
  constructor
  intro V x y hxy
  let coords (z : V ⟶ T.X ⊗ U.X) :
      (SubgroupFunctor.range t).carrier V × (SubgroupFunctor.range i).carrier V :=
    (⟨z ≫ fst T.X U.X ≫ t.hom.hom,
        SubgroupFunctor.mem_range.mpr ⟨z ≫ fst T.X U.X, Category.assoc _ _ _⟩⟩,
      ⟨z ≫ snd T.X U.X ≫ i.hom.hom,
        SubgroupFunctor.mem_range.mpr ⟨z ≫ snd T.X U.X, Category.assoc _ _ _⟩⟩)
  have he : (coords x).1.val * (coords x).2.val = (coords y).1.val * (coords y).2.val := by
    simpa only [coords, subgroupMultiplication, MonObj.comp_mul] using hxy
  have hc : coords x = coords y := Subgroup.mul_injective_of_disjoint (h V) he
  apply CartesianMonoidalCategory.hom_ext
  · exact (cancel_mono t.hom.hom).mp (by
      simpa only [coords, Category.assoc] using congrArg (fun z => z.1.val) hc)
  · exact (cancel_mono i.hom.hom).mp (by
      simpa only [coords, Category.assoc] using congrArg (fun z => z.2.val) hc)

/-- If one full quotient kernel is contained in another, the second quotient factors
through the first by a flat surjective morphism locally of finite presentation. -/
private theorem exists_fppf_quotient_factor {S : Scheme.{u}} {G P Q : GroupScheme S}
    {F N : SubgroupFunctor G} {p : G ⟶ P} {q : G ⟶ Q}
    (hp : RelativeRoot.IsFppfQuotient F p) (hq : RelativeRoot.IsFppfQuotient N q)
    (hFN : F ≤ N) :
    ∃ d : P ⟶ Q, p ≫ d = q ∧ Flat d.hom.hom.left ∧ Surjective d.hom.hom.left ∧
      LocallyOfFinitePresentation d.hom.hom.left := by
  have hk : kernelι p ≫ q = 0 := by
    apply Grp.hom_ext
    change (kernelι p).hom.hom ≫ q.hom.hom = 1
    apply (mem_range_kernelι_iff q _).mp
    rw [hq.2.2.2]
    apply hFN (kernel p).X
    rw [← hp.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  let : Flat p.hom.hom.left := hp.1
  let : Surjective p.hom.hom.left := hp.2.1
  let : LocallyOfFinitePresentation p.hom.hom.left := hp.2.2.1
  let d := FppfHomDescent.hom p q hk
  have hd : p ≫ d = q := FppfHomDescent.fac p q hk
  have he : p.hom.hom.left ≫ d.hom.hom.left = q.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) hd
  let : Flat (p.hom.hom.left ≫ d.hom.hom.left) := he.symm ▸ hq.1
  let : Surjective (p.hom.hom.left ≫ d.hom.hom.left) := he.symm ▸ hq.2.1
  let : LocallyOfFinitePresentation (p.hom.hom.left ≫ d.hom.hom.left) := he.symm ▸ hq.2.2.1
  exact ⟨d, hd,
    Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      p.hom.hom.left d.hom.hom.left,
    Surjective.of_comp p.hom.hom.left d.hom.hom.left,
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      p.hom.hom.left d.hom.hom.left⟩

/-- Milne, *Algebraic Groups*, Lemma 16.44. The ordered multiplication of the
complementary normal multiplicative and unipotent subgroups is an isomorphism. -/
theorem normalMultiplicativeUnipotentProduct : NormalMultiplicativeUnipotentProductStatement.{u} := by
  intro k _ G _ _ T U P Q t i p q ht htn hT hp hP hi hin hU hq hQ
  have hInt := (unipotentMultiplicativeTriviality k).2.1 G U T i t hi ht hU hT
  have hDisjoint (V : Over (Spec (CommRingCat.of k))) :
      Disjoint ((SubgroupFunctor.range t).carrier V) ((SubgroupFunctor.range i).carrier V) := by
    apply disjoint_iff.mpr
    rw [inf_comm]
    exact congrArg (fun F : SubgroupFunctor G => F.carrier V) hInt
  have hComm (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ T.X) (y : V ⟶ U.X) :
      Commute (x ≫ t.hom.hom) (y ≫ i.hom.hom) :=
    Subgroup.commute_of_normal_of_disjoint _ _
      ⟨fun a ha g => htn V g a (Subgroup.mem_top _) ha⟩
      ⟨fun a ha g => hin V g a (Subgroup.mem_top _) ha⟩ (hDisjoint V) _ _
      (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  refine ⟨fun V x y => (hComm V x y).eq, ?_⟩
  let : Mono t.hom.hom := ht.mono_overHom
  let : Mono i.hom.hom := hi.mono_overHom
  let : Mono (subgroupMultiplication t i) := mono_multiplication_of_disjoint t i hDisjoint
  let m := commutingSubgroupMultiplicationHom t i hComm
  let : IsAffineHom (T ⊗ U).X.hom := by
    change IsAffineHom (pullback.fst T.X.hom U.X.hom ≫ T.X.hom)
    let : IsAffineHom T.X.hom := ht.isAffineHom
    let : IsAffineHom (pullback.fst T.X.hom U.X.hom) := by
      set_option backward.isDefEq.respectTransparency.types false in
      exact MorphismProperty.pullback_fst _ _ hi.isAffineHom
    infer_instance
  let : LocallyOfFiniteType (T ⊗ U).X.hom :=
    prop_tensor_hom (@LocallyOfFiniteType) T.X U.X ht.locallyOfFiniteType hi.locallyOfFiniteType
  obtain ⟨I, a, j, -, hIaff, hj, hfac, ha⟩ := affineHomImage k (T ⊗ U) G m
  have hmul : a.hom.hom ≫ j.hom.hom = subgroupMultiplication t i :=
    congrArg (fun f => f.hom.hom) hfac
  let : Flat a.hom.hom.left := ha.1
  let : Surjective a.hom.hom.left := ha.2.1
  let : LocallyOfFinitePresentation a.hom.hom.left := ha.2.2.1
  have hProduct := SubgroupFunctor.isFppfProduct_of_fppf_factorization t i j hj a.hom.hom hmul
  obtain ⟨C, r, -, hCaff, hr⟩ :=
    affineNormalSubgroupQuotient k G I j hj (hProduct.isNormal htn hin)
  obtain ⟨p', -, hpf, hps, -⟩ := exists_fppf_quotient_factor hp hr hProduct.left_le
  obtain ⟨q', -, hqf, hqs, hql⟩ := exists_fppf_quotient_factor hq hr hProduct.right_le
  let : Flat p'.hom.hom.left := hpf
  let : Surjective p'.hom.hom.left := hps
  let : Flat q'.hom.hom.left := hqf
  let : Surjective q'.hom.hom.left := hqs
  let : LocallyOfFinitePresentation q'.hom.hom.left := hql
  let : IsAffineHom C.X.hom := hCaff
  have hCid : (𝟙 C : C ⟶ C) = 0 :=
    (hQ.of_fppfHom q').hom_eq_zero_of_isUnipotent (hP.of_flat_surjective p') (𝟙 C)
  have hrzero : r = 0 := by
    calc
      r = r ≫ 𝟙 C := (Category.comp_id r).symm
      _ = 0 := by rw [hCid, comp_zero]
  have hmem : 𝟙 G.X ∈ (SubgroupFunctor.range j).carrier G.X := by
    rw [← hr.2.2.2, mem_range_kernelι_iff, hrzero]
    exact MonObj.comp_one _
  obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hmem
  let : Mono j.hom.hom := hj.mono_overHom
  let : IsSplitEpi j.hom.hom := IsSplitEpi.mk' ⟨s, hs⟩
  let : IsIso j.hom.hom := isIso_of_mono_of_isSplitEpi _
  let : Mono a.hom.hom := mono_of_mono_fac hmul
  let : Mono a.hom.hom.left := Over.mono_left_of_mono _
  let : IsAffineHom I.X.hom := hIaff
  let : IsAffine (T ⊗ U).X.left := isAffine_of_isAffineHom (T ⊗ U).X.hom
  let : IsAffine I.X.left := isAffine_of_isAffineHom I.X.hom
  let : IsAffineHom a.hom.hom.left := isAffineHom_of_isAffine _
  let : IsIso ((Over.forget _).map a.hom.hom) :=
    Flat.isIso_of_surjective_of_mono a.hom.hom.left
  let : IsIso a.hom.hom := isIso_of_reflects_iso a.hom.hom (Over.forget _)
  rw [← hmul]
  infer_instance

end Langlands.GroupScheme
