import Langlands.GroupScheme.Absolute.BorelContainingSubgroupSelfNormalizerStatement
import Langlands.GroupScheme.Absolute.UnipotentQuotientParabolics
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.BaseChangeReflection

/-! # Subgroups containing a Borel subgroup are connected and self-normalizing: proof -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G Q P I : GroupScheme S}

/-- In a commuting square `i ≫ q = p ≫ j` whose top map `p` is fpqc and whose
bottom inclusion `j` is monic, a point normalizing `range i` maps under `q` to
a point normalizing `range j`, on every test scheme. -/
theorem normalizer_range_le_comap_normalizer_of_fpqc_square
    (i : P ⟶ G) (q : G ⟶ Q) (p : P ⟶ I) (j : I ⟶ Q)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left] [Mono j.hom.hom]
    (hsquare : i ≫ q = p ≫ j) :
    (range i).normalizer ≤ ((range j).normalizer).comap q := by
  have hs : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) hsquare
  intro U g hg
  rw [mem_comap]
  intro V a x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  constructor
  · apply mem_range_of_local_quotient_lift p j y
    intro W b z hz
    have h := (hg W (b ≫ a) (z ≫ i.hom.hom) (mem_range.mpr ⟨z, rfl⟩)).1
    obtain ⟨w, hw⟩ := mem_range.mp h
    refine mem_range.mpr ⟨w ≫ p.hom.hom, ?_⟩
    calc
      (w ≫ p.hom.hom) ≫ j.hom.hom = (w ≫ i.hom.hom) ≫ q.hom.hom := by
        rw [Category.assoc, ← hs, ← Category.assoc]
      _ = (((b ≫ a) ≫ g) * (z ≫ i.hom.hom) * ((b ≫ a) ≫ g)⁻¹) ≫ q.hom.hom := by
        rw [hw]
      _ = b ≫ ((a ≫ g ≫ q.hom.hom) * (y ≫ j.hom.hom) *
          (a ≫ g ≫ q.hom.hom)⁻¹) := by
        simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul,
          GrpObj.comp_inv, Category.assoc]
        rw [hs, ← Category.assoc z p.hom.hom j.hom.hom, ← hz]
        simp only [Category.assoc]
  · apply mem_range_of_local_quotient_lift p j y
    intro W b z hz
    have h := (hg W (b ≫ a) (z ≫ i.hom.hom) (mem_range.mpr ⟨z, rfl⟩)).2
    obtain ⟨w, hw⟩ := mem_range.mp h
    refine mem_range.mpr ⟨w ≫ p.hom.hom, ?_⟩
    calc
      (w ≫ p.hom.hom) ≫ j.hom.hom = (w ≫ i.hom.hom) ≫ q.hom.hom := by
        rw [Category.assoc, ← hs, ← Category.assoc]
      _ = (((b ≫ a) ≫ g)⁻¹ * (z ≫ i.hom.hom) * ((b ≫ a) ≫ g)) ≫ q.hom.hom := by
        rw [hw]
      _ = b ≫ ((a ≫ g ≫ q.hom.hom)⁻¹ * (y ≫ j.hom.hom) *
          (a ≫ g ≫ q.hom.hom)) := by
        simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul,
          GrpObj.comp_inv, Category.assoc]
        rw [hs, ← Category.assoc z p.hom.hom j.hom.hom, ← hz]
        simp only [Category.assoc]

end SubgroupFunctor

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, every geometric parabolic subgroup of a
smooth connected affine group is its own normalizer on all test schemes. The
ambient group is not assumed reductive: the proof passes to the reductive
quotient by the unipotent radical. -/
theorem normalizer_eq_of_isParabolicSubgroup_of_isAlgClosed [IsAlgClosed k]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i := by
  obtain ⟨U, r, hr⟩ := unipotentRadicalExistence k G
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U r hr
  have : Smooth U.X.hom := hr.smooth
  have : ConnectedSpace U.X.left := hr.connectedSpace
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have hQr : IsConnectedReductive Q := hQ.isConnectedReductive_of_isAlgClosed
  have : IsAffineHom Q.X.hom := hQr.isAffineHom
  have hker : HasSmoothConnectedUnipotentKernel q :=
    HasSmoothConnectedUnipotentKernel.of_representative r hr.isClosedSubgroup
      hr.isUnipotent hq
  obtain ⟨I, j, p, hj, hsq, hpf, hps, hpqc, -, hcomap, -⟩ :=
    (unipotentQuotientParabolicCorrespondence k G Q q hker).1 P i hi
  have : Flat p.hom.hom.left := hpf
  have : Surjective p.hom.hom.left := hps
  have : QuasiCompact p.hom.hom.left := hpqc
  have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
  have hN := parabolicSelfNormalizer k Q hQr I j hj
  apply le_antisymm _ (SubgroupFunctor.le_normalizer _)
  calc
    (SubgroupFunctor.range i).normalizer ≤
        ((SubgroupFunctor.range j).normalizer).comap q :=
      SubgroupFunctor.normalizer_range_le_comap_normalizer_of_fpqc_square i q p j hsq
    _ = (SubgroupFunctor.range j).comap q := by rw [hN]
    _ = SubgroupFunctor.range i := hcomap

/-- A smooth closed subgroup through which a geometric Borel subgroup factors is a
geometric parabolic subgroup. -/
theorem isParabolicSubgroup_of_geometricBorel_factor
    {B : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) (j : B ⟶ G) (f : B ⟶ P) (hi : IsClosedSubgroup i)
    (hP : Smooth P.X.hom) (hj : IsGeometricBorelSubgroup j) (hf : f ≫ i = j) :
    IsParabolicSubgroup i := by
  refine ⟨hi, hP, _, (GroupScheme.baseChange (toAlgebraicClosure k)).map j,
    (GroupScheme.baseChange (toAlgebraicClosure k)).map f, hj.2, ?_⟩
  rw [← Functor.map_comp, hf]

/-- Milne, Theorem 17.48 and Corollary 17.49: a smooth closed subgroup containing a
geometric Borel subgroup of a smooth connected affine group over any field is
connected and equals its normalizer on all test schemes. -/
theorem borelContainingSubgroupSelfNormalizer :
    BorelContainingSubgroupSelfNormalizerStatement.{u} := by
  intro k _ G _ _ _ P B i j f hi hP hj hf
  have hpar : IsParabolicSubgroup i :=
    isParabolicSubgroup_of_geometricBorel_factor i j f hi hP hj hf
  refine ⟨hpar.connectedSpace, ?_⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj G).X.left := G.connectedSpace_baseChange_of_smooth_affine b
  have : Mono i.hom.hom := hi.mono_overHom
  have heq := normalizer_eq_of_isParabolicSubgroup_of_isAlgClosed (F.map i)
    hpar.baseChange_toAlgebraicClosure
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hbSurjective
  have : Flat b := hbFlat
  have : QuasiCompact b := hbQuasiCompact
  apply SubgroupFunctor.normalizer_eq_of_baseChange_eq b i
  simpa only [F, SubgroupFunctor.range_baseChangeHom] using heq

end Langlands.GroupScheme
