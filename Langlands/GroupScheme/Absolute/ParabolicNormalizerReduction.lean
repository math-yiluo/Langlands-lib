import Langlands.GroupScheme.Absolute.ParabolicNormalizerPointsReduction
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.SubgroupFunctor.OpenCellNormalizer

/-! # All-test normalization from geometric Borel overgroups and an open cell -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' : Scheme.{u}} {P G : GroupScheme S}

/-- Pointwise membership over the new base pulls back to membership over that test scheme. -/
theorem mem_range_of_mem_normalizer_of_baseChange
    (b : S' ⟶ S) (i : P ⟶ G)
    (h : ∀ (x : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X),
      x ∈ (range ((GroupScheme.baseChange b).map i)).normalizer.carrier
        (Over.mk (𝟙 S')) →
      x ∈ (range ((GroupScheme.baseChange b).map i)).carrier (Over.mk (𝟙 S')))
    {g : Over.mk b ⟶ G.X}
    (hg : g ∈ (range i).normalizer.carrier (Over.mk b)) :
    g ∈ (range i).carrier (Over.mk b) := by
  let T : Over S' := Over.mk (𝟙 S')
  let e : Over.mk b ≅ (Over.map b).obj T :=
    Over.isoMk (Iso.refl S') (by simp [T])
  let x := (baseChangePointsEquiv b G T).symm (e.inv ≫ g)
  have hxN : x ∈ (range ((GroupScheme.baseChange b).map i)).normalizer.carrier T := by
    rw [range_baseChangeHom, ← normalizer_baseChange]
    change baseChangePointsEquiv b G T x ∈ (range i).normalizer.carrier _
    rw [MulEquiv.apply_symm_apply]
    exact (range i).normalizer.comp_mem e.inv hg
  have hx := h x hxN
  rw [range_baseChangeHom] at hx
  change baseChangePointsEquiv b G T x ∈ (range i).carrier _ at hx
  rw [MulEquiv.apply_symm_apply] at hx
  simpa only [Iso.hom_inv_id_assoc] using (range i).comp_mem e.hom hx

end SubgroupFunctor

variable {k : Type u} [Field k]
  {P G : GroupScheme (Spec (CommRingCat.of k))}

/-- The exact global Borel statements supply the two point hypotheses of the reduction. -/
theorem mem_range_of_mem_normalizer_of_borel_statements
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] [Smooth P.X.hom] [ConnectedSpace P.X.left]
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (B : GroupScheme (Spec (CommRingCat.of k))) (j : B ⟶ G) (f : B ⟶ P)
    (hj : IsBorelSubgroup j) (hf : f ≫ i = j)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : n ∈ (SubgroupFunctor.range i).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    n ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact mem_range_of_mem_normalizer_of_borel i j f hi hj hf
    (hconj k P).2 (hnorm k G B j hj) hn

/-- Explicit geometric hypotheses for a closed overgroup of ambient Borels.
This condition does not assert that these hypotheses hold for all parabolics. -/
def GeometricBorelOvergroupCondition (i : P ⟶ G) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
    ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left ∧
    ConnectedSpace ((GroupScheme.baseChange b).obj P).X.left ∧
    ∃ (B : GroupScheme (Spec (CommRingCat.of K)))
      (j : B ⟶ (GroupScheme.baseChange b).obj G)
      (f : B ⟶ (GroupScheme.baseChange b).obj P),
      IsBorelSubgroup j ∧ f ≫ (GroupScheme.baseChange b).map i = j

/-- Borel normalization and conjugacy imply membership of all geometric normalizer points. -/
theorem geometric_mem_range_of_borel_statements
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth P.X.hom]
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hgeom : GeometricBorelOvergroupCondition i)
    (K : Type u) [Field K] [IsAlgClosed K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {g : Over.mk b ⟶ G.X}
    (hg : g ∈ (SubgroupFunctor.range i).normalizer.carrier (Over.mk b)) :
    g ∈ (SubgroupFunctor.range i).carrier (Over.mk b) := by
  obtain ⟨hG, hP, B, j, f, hj, hf⟩ := hgeom K b
  let F := GroupScheme.baseChange b
  have : ConnectedSpace (F.obj G).X.left := hG
  have : ConnectedSpace (F.obj P).X.left := hP
  have : Smooth (F.obj G).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have : Smooth (F.obj P).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd P.X.hom b)
    infer_instance
  apply SubgroupFunctor.mem_range_of_mem_normalizer_of_baseChange b i _ hg
  exact fun x hx => mem_range_of_mem_normalizer_of_borel_statements
    hconj hnorm (F.map i) (hi.baseChange b) B j f hj hf hx

variable {U : GroupScheme (Spec (CommRingCat.of k))}

/-- With explicit geometric Borel hypotheses, an open cell upgrades the point reduction
into equality of subgroup functors on every test scheme. -/
theorem normalizer_eq_of_geometric_borels_and_open_cell
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth P.X.hom]
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (iU : U ⟶ G) (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hgeom : GeometricBorelOvergroupCondition i)
    (hsep : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (SubgroupFunctor.range iU).carrier T →
      g ∈ (SubgroupFunctor.range i).normalizer.carrier T → g = 1)
    (hopen : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU i).left) :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i := by
  apply SubgroupFunctor.normalizer_eq_of_open_cell iU i hsep _ hopen
  exact fun K _ _ b g hg =>
    geometric_mem_range_of_borel_statements hconj hnorm i hi hgeom K b hg

/-- Lift any normalizer point along the original inclusion using the geometric Borel
and open-cell hypotheses; the test scheme may be non-affine or nonreduced. -/
def normalizerPointsEquivOfGeometricBorels
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth P.X.hom]
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (iU : U ⟶ G) (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hgeom : GeometricBorelOvergroupCondition i)
    (hsep : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (SubgroupFunctor.range iU).carrier T →
      g ∈ (SubgroupFunctor.range i).normalizer.carrier T → g = 1)
    (hopen : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU i).left)
    (T : Over (Spec (CommRingCat.of k))) :
    (SubgroupFunctor.range i).normalizer.carrier T ≃* (T ⟶ P.X) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.normalizerPointsEquivOfOpenCell iU i hsep
    (fun K _ _ b g hg =>
      geometric_mem_range_of_borel_statements hconj hnorm i hi hgeom K b hg) hopen T


/-- The equivalence lifts along the given inclusion, rather than another presentation. -/
theorem normalizerPointsEquivOfGeometricBorels_comp
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth P.X.hom]
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (iU : U ⟶ G) (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hgeom : GeometricBorelOvergroupCondition i)
    (hsep : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
      g ∈ (SubgroupFunctor.range iU).carrier T →
      g ∈ (SubgroupFunctor.range i).normalizer.carrier T → g = 1)
    (hopen : IsOpenImmersion (SubgroupFunctor.cellMultiplication iU i).left)
    (T : Over (Spec (CommRingCat.of k)))
    (g : (SubgroupFunctor.range i).normalizer.carrier T) :
    normalizerPointsEquivOfGeometricBorels hconj hnorm iU i hi hgeom hsep hopen T g ≫
      i.hom.hom = g := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact SubgroupFunctor.normalizerPointsEquivOfOpenCell_comp iU i hsep
    (fun K _ _ b g hg =>
      geometric_mem_range_of_borel_statements hconj hnorm i hi hgeom K b hg) hopen T g

end Langlands.GroupScheme
