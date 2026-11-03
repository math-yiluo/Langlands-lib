import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.FiniteEtaleImage
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # All-test self-normalization from an open cell and geometric points -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G U P : GroupScheme S} (iU : U ⟶ G) (iP : P ⟶ G)

/-- The right factor is contained in the cell, using the identity in the left factor. -/
theorem range_right_subset_cell :
    Set.range iP.hom.hom.left ⊆ Set.range (cellMultiplication iU iP).left := by
  let a : P.X ⟶ U.X ⊗ P.X := lift 1 (𝟙 _)
  have ha : a ≫ cellMultiplication iU iP = iP.hom.hom := by
    simp only [a, lift_cellMultiplication, MonObj.one_comp, Category.id_comp, one_mul]
  rintro _ ⟨p, rfl⟩
  refine ⟨a.left p, ?_⟩
  change (a ≫ cellMultiplication iU iP).left p = _
  rw [ha]

variable
  (hsep : ∀ (T : Over S) (g : T ⟶ G.X),
    g ∈ (range iU).carrier T → g ∈ (range iP).normalizer.carrier T → g = 1)

include hsep in
/-- A normalizing point whose image is contained in an open multiplication cell
belongs to the right subgroup if the left subgroup meets the normalizer trivially. -/
theorem mem_range_of_mem_normalizer_of_range_subset_cell
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left)
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (range iP).normalizer.carrier T)
    (hrange : Set.range g.left ⊆ Set.range (cellMultiplication iU iP).left) :
    g ∈ (range iP).carrier T := by
  have : IsOpenImmersion (cellMultiplication iU iP).left := hopen
  let a := FiniteEtaleImage.liftOver (cellMultiplication iU iP) g hrange
  let x : T ⟶ G.X := a ≫ fst U.X P.X ≫ iU.hom.hom
  let y : T ⟶ G.X := a ≫ snd U.X P.X ≫ iP.hom.hom
  have hx : x ∈ (range iU).carrier T := mem_range.mpr ⟨a ≫ fst U.X P.X, rfl⟩
  have hy : y ∈ (range iP).carrier T := mem_range.mpr ⟨a ≫ snd U.X P.X, rfl⟩
  have hxy : g = x * y := by
    have h := FiniteEtaleImage.liftOver_fac (cellMultiplication iU iP) g hrange
    simpa only [a, cellMultiplication, MonObj.comp_mul, Category.assoc, x, y] using h.symm
  have hyN := le_normalizer (range iP) T hy
  have hxN : x ∈ (range iP).normalizer.carrier T := by
    have h := ((range iP).normalizer.carrier T).mul_mem hg
      (((range iP).normalizer.carrier T).inv_mem hyN)
    simpa only [hxy, mul_inv_cancel_right] using h
  have hx1 := hsep T x hx hxN
  simpa only [hxy, hx1, one_mul] using hy

variable
  (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (CommRingCat.of K) ⟶ S)
    (g : Over.mk b ⟶ G.X),
    g ∈ (range iP).normalizer.carrier (Over.mk b) →
      g ∈ (range iP).carrier (Over.mk b))

include hgeom in
/-- Geometric normalizer point membership puts the topological image of every
normalizer-valued test map in the multiplication cell. -/
theorem range_subset_cell_of_geometric_mem
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (range iP).normalizer.carrier T) :
    Set.range g.left ⊆ Set.range (cellMultiplication iU iP).left := by
  rintro _ ⟨t, rfl⟩
  let K := AlgebraicClosure (T.left.residueField t)
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let s : Spec (CommRingCat.of K) ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫
      T.left.fromSpecResidueField t
  have hs : s pt = t := by
    simp only [s, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  let b := s ≫ T.hom
  let a : Over.mk b ⟶ T := Over.homMk s rfl
  have hgp := hgeom K b (a ≫ g) ((range iP).normalizer.comp_mem a hg)
  obtain ⟨p, hp⟩ := mem_range.mp hgp
  apply range_right_subset_cell iU iP
  refine ⟨p.left pt, ?_⟩
  change (p ≫ iP.hom.hom).left pt = g.left t
  rw [hp]
  change g.left (s pt) = g.left t
  rw [hs]

include hsep hgeom in
/-- An open cell, trivial intersection of its left subgroup with the normalizer,
and geometric point membership imply equality of subgroup functors on all tests. -/
theorem normalizer_eq_of_open_cell
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left) :
    (range iP).normalizer = range iP := by
  apply le_antisymm
  · intro T g hg
    exact mem_range_of_mem_normalizer_of_range_subset_cell iU iP hsep hopen hg
      (range_subset_cell_of_geometric_mem iU iP hgeom hg)
  · exact le_normalizer (range iP)

include hsep hgeom in
/-- Under the open-cell and geometric-point hypotheses, the normalizer points
are multiplicatively equivalent to points of the represented right subgroup. -/
def normalizerPointsEquivOfOpenCell
    [Mono iP.hom.hom]
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left) (T : Over S) :
    (range iP).normalizer.carrier T ≃* (T ⟶ P.X) :=
  (MulEquiv.subgroupCongr
    (congrArg (fun F : SubgroupFunctor G => F.carrier T)
      (normalizer_eq_of_open_cell iU iP hsep hgeom hopen))).trans
    ((show (range iP).IsRepresentedBy iP from ⟨inferInstance, rfl⟩).pointsEquiv T).symm

include hsep hgeom in
/-- The point equivalence lifts each normalizer point along the original subgroup inclusion. -/
theorem normalizerPointsEquivOfOpenCell_comp
    [Mono iP.hom.hom]
    (hopen : IsOpenImmersion (cellMultiplication iU iP).left) (T : Over S)
    (g : (range iP).normalizer.carrier T) :
    normalizerPointsEquivOfOpenCell iU iP hsep hgeom hopen T g ≫ iP.hom.hom = g :=
  (show (range iP).IsRepresentedBy iP from ⟨inferInstance, rfl⟩).pointsEquiv_symm_comp _

end Langlands.GroupScheme.SubgroupFunctor
