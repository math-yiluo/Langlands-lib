import Langlands.GroupScheme.Derived.StructureStatement
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof

/-! # Field base change for the scheme-theoretic derived subgroup -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S}

/-- Points whose every refinement over the extended base belongs to `F`. -/
def restrictionCore (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∀ (T' : Over S') (c : (Over.map b).obj T' ⟶ T),
        (baseChangePointsEquiv b G T').symm (c ≫ g) ∈ F.carrier T'}
      one_mem' := by
        intro T' c
        rw [MonObj.comp_one, map_one]
        exact (F.carrier T').one_mem
      mul_mem' := by
        intro g h hg hh T' c
        rw [MonObj.comp_mul, map_mul]
        exact (F.carrier T').mul_mem (hg T' c) (hh T' c)
      inv_mem' := by
        intro g hg T' c
        rw [GrpObj.comp_inv, map_inv]
        exact (F.carrier T').inv_mem (hg T' c) }
  comp_mem c g hg T' d := by
    rw [← Category.assoc]
    exact hg T' (d ≫ c)

/-- The core, after base change, lies in the original subgroup. -/
theorem restrictionCore_baseChange_le
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    (restrictionCore b F).baseChange b ≤ F := by
  intro T x hx
  have h := hx T (𝟙 ((Over.map b).obj T))
  change (baseChangePointsEquiv b G T).symm
    (𝟙 ((Over.map b).obj T) ≫ baseChangePointsEquiv b G T x) ∈ F.carrier T at h
  simpa only [Category.id_comp, MulEquiv.symm_apply_apply] using h

/-- The restriction core of a commutator-containing subgroup contains commutators. -/
theorem ContainsCommutators.restrictionCore
    {F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)}
    (hF : F.ContainsCommutators) :
    (restrictionCore b F).ContainsCommutators := by
  intro T g h T' c
  simp only [MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv]
  exact hF T' _ _

/-- The underlying inclusion with the actual pullback as codomain. -/
def restrictionCoreLeft {H : GroupScheme S'}
    (i : H ⟶ (GroupScheme.baseChange b).obj G) :
    H.X.left ⟶ pullback G.X.hom b :=
  i.hom.hom.left

/-- The inclusion over the extended base, viewed in the product over the original base. -/
def restrictionCoreMap {H : GroupScheme S'}
    (i : H ⟶ (GroupScheme.baseChange b).obj G) :
    (Over.map b).obj H.X ⟶ Over.mk b ⊗ G.X :=
  Over.homMk (restrictionCoreLeft b i ≫ (pullbackSymmetry G.X.hom b).hom) (by
    change (restrictionCoreLeft b i ≫ (pullbackSymmetry G.X.hom b).hom) ≫
      (pullback.fst b G.X.hom ≫ b) = H.X.hom ≫ b
    calc
      _ = (restrictionCoreLeft b i ≫
          ((pullbackSymmetry G.X.hom b).hom ≫ pullback.fst b G.X.hom)) ≫ b := by
        simp only [Category.assoc]
      _ = (restrictionCoreLeft b i ≫ pullback.snd G.X.hom b) ≫ b := by
        rw [pullbackSymmetry_hom_comp_fst]
      _ = H.X.hom ≫ b := congrArg (fun z => z ≫ b) i.hom.hom.w)

/-- Closedness survives forgetting the base and interchanging the product factors. -/
theorem restrictionCoreMap_isClosedImmersion {H : GroupScheme S'}
    (i : H ⟶ (GroupScheme.baseChange b).obj G) (hi : IsClosedSubgroup i) :
    IsClosedImmersion (restrictionCoreMap b i).left := by
  let : IsClosedImmersion i.hom.hom.left := hi
  change IsClosedImmersion (restrictionCoreLeft b i ≫ (pullbackSymmetry G.X.hom b).hom)
  have : IsClosedImmersion (restrictionCoreLeft b i) := hi
  infer_instance

/-- The core condition is the universal factorization of the full parameter product. -/
theorem mem_restrictionCore_range_iff {H : GroupScheme S'}
    (i : H ⟶ (GroupScheme.baseChange b).obj G) (T : Over S) (g : T ⟶ G.X) :
    g ∈ (restrictionCore b (range i)).carrier T ↔
      ∃ q : Over.mk b ⊗ T ⟶ (Over.map b).obj H.X,
        q ≫ restrictionCoreMap b i = Over.mk b ◁ g := by
  have hw1 : (Over.mk b ◁ g).left ≫ pullback.fst b G.X.hom =
      pullback.fst b T.hom := Over.whiskerLeft_left_fst g
  have hw2 : (Over.mk b ◁ g).left ≫ pullback.snd b G.X.hom =
      pullback.snd b T.hom ≫ g.left := Over.whiskerLeft_left_snd g
  have hiw : restrictionCoreLeft b i ≫ pullback.snd G.X.hom b = H.X.hom :=
    i.hom.hom.w
  constructor
  · intro hg
    let T' : Over S' := Over.mk (pullback.fst b T.hom)
    obtain ⟨y, hy⟩ := hg T' (snd (Over.mk b) T)
    refine ⟨(Over.map b).map y, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (y.left ≫ restrictionCoreLeft b i ≫ (pullbackSymmetry G.X.hom b).hom) ≫
        pullback.fst b G.X.hom = (Over.mk b ◁ g).left ≫ pullback.fst b G.X.hom
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, hiw, hw1]
      exact y.w
    · have h := congrArg (fun z => (baseChangePointsEquiv b G T' z).left) hy
      change (y.left ≫ i.hom.hom.left) ≫ pullback.fst G.X.hom b =
        ((baseChangePointsEquiv b G T')
          ((baseChangePointsEquiv b G T').symm (snd (Over.mk b) T ≫ g))).left at h
      rw [MulEquiv.apply_symm_apply] at h
      change (y.left ≫ restrictionCoreLeft b i ≫ (pullbackSymmetry G.X.hom b).hom) ≫
        pullback.snd b G.X.hom = (Over.mk b ◁ g).left ≫ pullback.snd b G.X.hom
      simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, hw2]
      simpa only [restrictionCoreLeft, Category.assoc, Over.comp_left, Over.snd_left,
        Over.mk_hom] using h
  · rintro ⟨q, hq⟩ T' c
    let s : (Over.map b).obj T' ⟶ Over.mk b ⊗ T :=
      lift (Over.homMk T'.hom) c
    have hfst := congrArg (fun z => z.left ≫ pullback.fst b G.X.hom) hq
    have hsnd := congrArg (fun z => z.left ≫ pullback.snd b G.X.hom) hq
    have hyw : (s.left ≫ q.left) ≫ H.X.hom = T'.hom := by
      simp only [Over.comp_left, restrictionCoreMap, Over.homMk_left,
        Category.assoc, pullbackSymmetry_hom_comp_fst, hiw, hw1] at hfst
      rw [Category.assoc, hfst]
      simp [s]
    let y : T' ⟶ H.X := Over.homMk (s.left ≫ q.left) hyw
    refine ⟨y, ?_⟩
    apply (baseChangePointsEquiv b G T').injective
    rw [MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, restrictionCoreMap, Over.homMk_left,
      Category.assoc, pullbackSymmetry_hom_comp_snd, hw2] at hsnd
    change ((s.left ≫ q.left) ≫ restrictionCoreLeft b i) ≫ pullback.fst G.X.hom b =
      c.left ≫ g.left
    calc
      ((s.left ≫ q.left) ≫ restrictionCoreLeft b i) ≫ pullback.fst G.X.hom b =
          s.left ≫ (q.left ≫ restrictionCoreLeft b i ≫ pullback.fst G.X.hom b) := by
        simp only [Category.assoc]
      _ = s.left ≫ (pullback.snd b T.hom ≫ g.left) := by
        rw [hsnd]
      _ = c.left ≫ g.left := by simp [s]

/-- Over a field, restriction cores of closed subgroups along an affine map
are again represented by closed subgroup schemes. -/
theorem restrictionCore_isClosedRepresentable {k : Type u} [Field k]
    {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k)) [IsAffineHom b]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G))
    (hF : F.IsClosedRepresentable) :
    (restrictionCore b F).IsClosedRepresentable := by
  obtain ⟨H, i, hi, hclosed⟩ := hF
  rw [← hi.2]
  let X : Over (Spec (CommRingCat.of k)) := Over.mk b
  have : IsAffine X.left := isAffine_of_isAffineHom b
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hX : Langlands.AlgebraicGeometry.HasFpqcProjectiveCoordinateModule X := by
    refine ⟨CommAlgCat.of (CommRingCat.of k) k, ?_, ?_⟩
    · infer_instance
    · infer_instance
  have : IsClosedImmersion (restrictionCoreMap b i).left :=
    restrictionCoreMap_isClosedImmersion b i hclosed
  obtain ⟨Z, j, hj, hrep⟩ :=
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.affine
      X G.X hX (restrictionCoreMap b i)
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  apply (restrictionCore b (range i)).isClosedRepresentable_of_scheme j
  intro T g
  exact (mem_restrictionCore_range_iff b i T g).trans (hrep T g).symm

end SubgroupFunctor

end Langlands.GroupScheme
