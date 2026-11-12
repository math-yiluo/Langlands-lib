import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductUniqueness
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Dynamic.Functoriality
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn

/-! # Actual subproducts of almost-simple factors -/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Products

variable {S : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S)

/-- Insert a subset of coordinates into a finite product. -/
def piSubsetInclusionHom (s : Set I) : pi (fun i : s => A i) ⟶ pi A := by
  classical
  exact Pi.lift fun j => if h : j ∈ s then Pi.π (fun i : s => A i) ⟨j, h⟩
    else Grp.homMk (toUnit _ ≫ η[(A j).X])

/-- Project onto a subset of coordinates of a finite product. -/
def piSubsetProjectionHom (s : Set I) : pi A ⟶ pi (fun i : s => A i) :=
  Pi.lift fun i => Pi.π A i

@[simp] theorem piSubsetInclusionHom_π_mem (s : Set I) (i : s) :
    piSubsetInclusionHom A s ≫ Pi.π A i = Pi.π (fun j : s => A j) i := by
  classical
  simp [piSubsetInclusionHom, i.property]

theorem piSubsetInclusionHom_points_notMem (s : Set I) (i : I) (hi : i ∉ s)
    {T : Over S} (x : T ⟶ (pi (fun j : s => A j)).X) :
    (x ≫ (piSubsetInclusionHom A s).hom.hom) ≫ (Pi.π A i).hom.hom = 1 := by
  classical
  rw [Category.assoc, ← Grp.comp_hom_hom]
  simp only [piSubsetInclusionHom, Pi.lift_comp_π, dite_eq_right hi]
  exact MonObj.comp_one _

@[simp] theorem piSubsetInclusionHom_projection (s : Set I) :
    piSubsetInclusionHom A s ≫ piSubsetProjectionHom A s = 𝟙 _ := by
  apply Pi.hom_ext
  intro i
  simp [piSubsetProjectionHom]

/-- Membership in the actual subproduct is detected on every test scheme by
identity coordinates outside its index subset. -/
theorem mem_range_piSubsetInclusionHom_iff (s : Set I) {T : Over S}
    (x : T ⟶ (pi A).X) :
    x ∈ (SubgroupFunctor.range (piSubsetInclusionHom A s)).carrier T ↔
      ∀ i, i ∉ s → x ≫ (Pi.π A i).hom.hom = 1 := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact piSubsetInclusionHom_points_notMem A s i hi y
  · intro hx
    refine ⟨x ≫ (piSubsetProjectionHom A s).hom.hom, ?_⟩
    apply (piPointsEquiv A T).injective
    funext i
    change ((x ≫ (piSubsetProjectionHom A s).hom.hom) ≫
      (piSubsetInclusionHom A s).hom.hom) ≫ (Pi.π A i).hom.hom =
        x ≫ (Pi.π A i).hom.hom
    by_cases hi : i ∈ s
    · rw [Category.assoc _ (piSubsetInclusionHom A s).hom.hom,
        ← Grp.comp_hom_hom, piSubsetInclusionHom_π_mem A s ⟨i, hi⟩,
        Category.assoc, ← Grp.comp_hom_hom]
      simp [piSubsetProjectionHom]
    · rw [piSubsetInclusionHom_points_notMem A s i hi, hx i hi]

/-- Subproducts of arbitrary groups are normal on all test schemes. -/
theorem isNormal_range_piSubsetInclusionHom (s : Set I) :
    (SubgroupFunctor.range (piSubsetInclusionHom A s)).IsNormal := by
  intro T g x _ hx
  apply (mem_range_piSubsetInclusionHom_iff A s _).2
  intro i hi
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    (mem_range_piSubsetInclusionHom_iff A s x).1 hx i hi]
  simp

private theorem point_list_prod_comp {H Q : GroupScheme S} (q : H ⟶ Q)
    {T : Over S} (l : List (T ⟶ H.X)) :
    l.prod ≫ q.hom.hom = (l.map (fun x => x ≫ q.hom.hom)).prod := by
  induction l with
  | nil => exact MonObj.one_comp _
  | cons x l ih =>
    simp only [List.prod_cons, List.map_cons, MonObj.mul_comp, ih]

/-- Every point of a finite product is an ordered product of its single
coordinates. No commutativity of the individual groups is used. -/
theorem pi_point_eq_coordinate_prod {T : Over S} (x : T ⟶ (pi A).X) :
    ∃ l : List I, (∀ i, i ∈ l) ∧
      x = (l.map (fun i =>
        (x ≫ (Pi.π A i).hom.hom) ≫ (piFactorInclusionHom A i).hom.hom)).prod := by
  classical
  let e := (Finite.equivFin I).symm
  let l := List.ofFn e
  have hl : ∀ i, i ∈ l := fun i => List.mem_ofFn.mpr ⟨e.symm i, e.apply_symm_apply i⟩
  have hn : l.Nodup := List.nodup_ofFn.mpr e.injective
  refine ⟨l, hl, ?_⟩
  apply (piPointsEquiv A T).injective
  funext j
  simp only [piPointsEquiv_apply]
  rw [point_list_prod_comp, List.map_map]
  simp only [Function.comp_def]
  have he : (l.map (fun i =>
      ((x ≫ (Pi.π A i).hom.hom) ≫ (piFactorInclusionHom A i).hom.hom) ≫
        (Pi.π A j).hom.hom)).prod =
      (x ≫ (Pi.π A j).hom.hom) ^ l.count j := by
    simpa only [piFactorInclusionHom_points_self] using
      List.prod_map_eq_pow_single j (fun i =>
        ((x ≫ (Pi.π A i).hom.hom) ≫ (piFactorInclusionHom A i).hom.hom) ≫
          (Pi.π A j).hom.hom)
        (fun i hij _ => piFactorInclusionHom_points_ne A i j hij _)
  rw [he, List.count_eq_one_of_mem hn (hl j), pow_one]

/-- An all-test subgroup contains a subproduct exactly when it contains each
factor indexed by the subset. -/
theorem range_piSubsetInclusionHom_le_iff (s : Set I) (F : SubgroupFunctor (pi A)) :
    SubgroupFunctor.range (piSubsetInclusionHom A s) ≤ F ↔
      ∀ i ∈ s, SubgroupFunctor.range (piFactorInclusionHom A i) ≤ F := by
  constructor
  · intro h i hi T x hx
    apply h T
    apply (mem_range_piSubsetInclusionHom_iff A s _).2
    intro j hj
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    exact piFactorInclusionHom_points_ne A i j (fun he => hj (he ▸ hi)) y
  · intro h T x hx
    obtain ⟨l, _, hl⟩ := pi_point_eq_coordinate_prod A x
    rw [hl]
    apply (F.carrier T).list_prod_mem
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hz
    by_cases hi : i ∈ s
    · exact h i hi T (SubgroupFunctor.mem_range.2 ⟨_, rfl⟩)
    · rw [(mem_range_piSubsetInclusionHom_iff A s x).1 hx i hi, MonObj.one_comp]
      exact (F.carrier T).one_mem

end Products

private instance smoothGeometricallyConnected_comp :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).IsStableUnderComposition where
  comp_mem f g hf hg := by
    let : Smooth f := hf.1
    let : Smooth g := hg.1
    let : GeometricallyConnected f := hf.2
    let : GeometricallyConnected g := hg.2
    exact ⟨inferInstance, GeometricallyConnected.comp f g⟩

private instance smoothGeometricallyConnected_id :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).ContainsIdentities where
  id_mem X := by
    refine ⟨inferInstance, ⟨?_⟩⟩
    intro K _ x Y a b hp
    have : IsIso b := hp.isIso_snd_of_isIso
    exact b.homeomorph.connectedSpace_iff.mpr inferInstance

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

namespace SimplyConnectedAlmostSimpleProduct

variable (D : SimplyConnectedAlmostSimpleProduct G)

/-- The actual product on a chosen subset of the almost-simple factors. -/
abbrev subproduct (s : Set D.Index) : GroupScheme (Spec (CommRingCat.of k)) :=
  pi (fun i : s => D.factor i)

/-- Insert a subproduct into the original group. -/
def subproductInclusion (s : Set D.Index) : D.subproduct s ⟶ G :=
  piSubsetInclusionHom D.factor s ≫ D.iso.inv

/-- Retract the original group onto a subproduct. -/
def subproductProjection (s : Set D.Index) : G ⟶ D.subproduct s :=
  D.iso.hom ≫ piSubsetProjectionHom D.factor s

@[simp] theorem subproductInclusion_projection (s : Set D.Index) :
    D.subproductInclusion s ≫ D.subproductProjection s = 𝟙 _ := by
  simp only [subproductInclusion, subproductProjection, Category.assoc,
    Iso.inv_hom_id_assoc, piSubsetInclusionHom_projection]

/-- A subproduct is a closed subgroup of the original affine group. -/
theorem isClosedSubgroup_subproductInclusion [IsAffineHom G.X.hom]
    (s : Set D.Index) : IsClosedSubgroup (D.subproductInclusion s) := by
  change IsClosedImmersion (D.subproductInclusion s).hom.hom.left
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have he : (D.subproductInclusion s).hom.hom.left ≫
      (D.subproductProjection s).hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, subproductInclusion_projection,
      Grp.id_hom_hom, Over.id_left]
  have : IsClosedImmersion ((D.subproductInclusion s).hom.hom.left ≫
      (D.subproductProjection s).hom.hom.left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ (D.subproductProjection s).hom.hom.left

/-- The coordinate criterion, expressed in the original group. -/
theorem mem_range_subproductInclusion_iff (s : Set D.Index)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range (D.subproductInclusion s)).carrier T ↔
      ∀ i, i ∉ s → x ≫ (D.projection i).hom.hom = 1 := by
  have he : x ∈ (SubgroupFunctor.range (D.subproductInclusion s)).carrier T ↔
      (x ≫ D.iso.hom.hom.hom) ∈
        (SubgroupFunctor.range (piSubsetInclusionHom D.factor s)).carrier T := by
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
      refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
      change y ≫ (piSubsetInclusionHom D.factor s).hom.hom =
        (y ≫ (D.subproductInclusion s).hom.hom) ≫ D.iso.hom.hom.hom
      rw [subproductInclusion, Grp.comp_hom_hom, Category.assoc,
        Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id]
    · intro hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
      refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
      have he := congrArg (fun w => w ≫ D.iso.inv.hom.hom) hy
      simpa only [subproductInclusion, Grp.comp_hom_hom, Category.assoc,
        ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
        Category.comp_id] using he
  rw [he, mem_range_piSubsetInclusionHom_iff]
  simp only [projection, Grp.comp_hom_hom, Category.assoc]

/-- Every subproduct is normal on all test schemes of the original group. -/
theorem isNormal_range_subproductInclusion (s : Set D.Index) :
    (SubgroupFunctor.range (D.subproductInclusion s)).IsNormal := by
  intro T g x _ hx
  apply (D.mem_range_subproductInclusion_iff s _).2
  intro i hi
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    (D.mem_range_subproductInclusion_iff s x).1 hx i hi]
  simp

/-- Every actual subproduct is smooth and geometrically connected. -/
theorem subproduct_geometry (s : Set D.Index) :
    Smooth (D.subproduct s).X.hom ∧
      GeometricallyConnected (D.subproduct s).X.hom := by
  apply prop_pi_hom (@Smooth ⊓ @GeometricallyConnected) (fun i : s => D.factor i)
  intro i
  have h := (D.isAlmostSimple i).isSemisimple.isConnectedReductive
  let : Smooth (D.factor i).X.hom := h.smooth
  let : IsAffineHom (D.factor i).X.hom := h.isAffineHom
  let : ConnectedSpace (D.factor i).X.left := h.connectedSpace
  exact ⟨inferInstance, (D.factor i).geometricallyConnected_of_connected⟩

theorem smooth_subproduct (s : Set D.Index) : Smooth (D.subproduct s).X.hom :=
  (D.subproduct_geometry s).1

theorem connectedSpace_subproduct (s : Set D.Index) :
    ConnectedSpace (D.subproduct s).X.left := by
  let : GeometricallyConnected (D.subproduct s).X.hom := (D.subproduct_geometry s).2
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := (D.subproduct s).X.hom)

private theorem range_comp_le_iff {S : Scheme.{u}} {A B C : GroupScheme S}
    (a : A ⟶ B) (b : B ⟶ C) (F : SubgroupFunctor C) :
    SubgroupFunctor.range (a ≫ b) ≤ F ↔
      SubgroupFunctor.range a ≤ F.comap b := by
  constructor
  · intro h T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    change (y ≫ a.hom.hom) ≫ b.hom.hom ∈ F.carrier T
    apply h T
    refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc]
  · intro h T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    have hy := h T (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    change (y ≫ a.hom.hom) ≫ b.hom.hom ∈ F.carrier T at hy
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy

/-- In the original group, a subproduct is generated by precisely its
selected actual factors on every test scheme. -/
theorem range_subproductInclusion_le_iff (s : Set D.Index) (F : SubgroupFunctor G) :
    SubgroupFunctor.range (D.subproductInclusion s) ≤ F ↔
      ∀ i ∈ s, SubgroupFunctor.range (D.inclusion i) ≤ F := by
  simp only [subproductInclusion, inclusion, range_comp_le_iff,
    range_piSubsetInclusionHom_le_iff]

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
