import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleSubproducts
import Langlands.GroupScheme.SimplyConnected.DirectFactors
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Point-level helpers for the semisimple decomposition theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SimpleFactor

variable {S : Scheme.{u}}

/-- A test point of the target of a quasi-compact, flat and surjective morphism lifts to
the source after a quasi-compact, flat and surjective refinement of the test scheme. -/
theorem exists_refinement_lift {P G : Over S} (m : P ⟶ G) [QuasiCompact m.left]
    [Flat m.left] [Surjective m.left] {T : Over S} (g : T ⟶ G) :
    ∃ (W : Over S) (w : W ⟶ T) (z : W ⟶ P), QuasiCompact w.left ∧ Flat w.left ∧
      Surjective w.left ∧ w ≫ g = z ≫ m := by
  refine ⟨Over.mk (pullback.fst g.left m.left ≫ T.hom),
    Over.homMk (pullback.fst g.left m.left) rfl,
    Over.homMk (pullback.snd g.left m.left) ?_,
    show QuasiCompact (pullback.fst g.left m.left) from inferInstance,
    show Flat (pullback.fst g.left m.left) from inferInstance,
    show Surjective (pullback.fst g.left m.left) from inferInstance, ?_⟩
  · change pullback.snd g.left m.left ≫ P.hom = pullback.fst g.left m.left ≫ T.hom
    rw [← Over.w m, ← Over.w g, ← Category.assoc, ← pullback.condition, Category.assoc]
  · apply Over.OverMorphism.ext
    exact pullback.condition

/-- Composites of quasi-compact, flat and surjective refinements are effective
epimorphisms. -/
theorem effectiveEpi_comp_left {T W W' : Over S} (w : W ⟶ T) (w' : W' ⟶ W)
    [QuasiCompact w.left] [Flat w.left] [Surjective w.left]
    [QuasiCompact w'.left] [Flat w'.left] [Surjective w'.left] :
    EffectiveEpi (w' ≫ w).left := by
  rw [Over.comp_left]
  infer_instance

/-- Commutation of two test points is detected after an epimorphic refinement. -/
theorem commute_of_epi {G : GroupScheme S} {T W : Over S} (w : W ⟶ T) [Epi w.left]
    {x y : T ⟶ G.X} (h : Commute (w ≫ x) (w ≫ y)) : Commute x y := by
  have : Epi w := Over.epi_of_epi_left w
  apply (cancel_epi w).mp
  rw [MonObj.comp_mul, MonObj.comp_mul]
  exact h.eq

/-- A test point commutes with every point of the target of a quasi-compact flat
surjective homomorphism when it commutes, after every refinement, with the images of
points of the source. -/
theorem commute_of_lift {P G : GroupScheme S} (m : P ⟶ G) [QuasiCompact m.hom.hom.left]
    [Flat m.hom.hom.left] [Surjective m.hom.hom.left] {T : Over S} (x : T ⟶ G.X)
    (h : ∀ (W : Over S) (w : W ⟶ T) (z : W ⟶ P.X), Commute (w ≫ x) (z ≫ m.hom.hom))
    (g : T ⟶ G.X) : Commute x g := by
  obtain ⟨W, w, z, h1, h2, h3, hwz⟩ := exists_refinement_lift m.hom.hom g
  have : Epi w.left := inferInstance
  apply commute_of_epi w
  rw [hwz]
  exact h W w z

/-- The range of a monomorphic homomorphism is normal when it is normalized by the images
of all points of the source of a quasi-compact flat surjective homomorphism. -/
theorem isNormal_range_of_lift {P N G : GroupScheme S} (m : P ⟶ G)
    [QuasiCompact m.hom.hom.left] [Flat m.hom.hom.left] [Surjective m.hom.hom.left]
    (n : N ⟶ G) [Mono n.hom.hom]
    (h : ∀ (T : Over S) (z : T ⟶ P.X) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range n).carrier T →
        (z ≫ m.hom.hom) * x * (z ≫ m.hom.hom)⁻¹ ∈ (SubgroupFunctor.range n).carrier T) :
    (SubgroupFunctor.range n).IsNormal := by
  intro T g x _ hx
  obtain ⟨W, w, z, h1, h2, h3, hwz⟩ := exists_refinement_lift m.hom.hom g
  apply SubgroupFunctor.mem_range_of_comp_mem_range n w
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hwz]
  exact h W z (w ≫ x) ((SubgroupFunctor.range n).comp_mem w hx)

/-- A homomorphism carries points of the derived subgroup into the derived subgroup. -/
theorem comp_mem_derivedSubgroup {H G : GroupScheme S} (φ : H ⟶ G) {T : Over S}
    {x : T ⟶ H.X} (hx : x ∈ (derivedSubgroup H).carrier T) :
    x ≫ φ.hom.hom ∈ (derivedSubgroup G).carrier T := by
  intro C i hi hcomm
  have hcl : IsClosedSubgroup (subgroupIntersectionFst φ i) :=
    isClosedSubgroup_subgroupIntersectionFst φ hi
  have hrange := range_subgroupIntersectionFst_eq_comap φ i
  have hc : (SubgroupFunctor.range (subgroupIntersectionFst φ i)).ContainsCommutators := by
    rw [hrange]
    intro U a b
    rw [SubgroupFunctor.mem_comap, MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, GrpObj.inv_comp]
    exact hcomm U _ _
  have hmem := hx _ _ hcl hc
  rw [hrange, SubgroupFunctor.mem_comap] at hmem
  exact hmem

/-- A finite product of perfect group schemes is perfect. -/
theorem derivedSubgroup_pi_eq_top {I : Type u} [Finite I] (A : I → GroupScheme S)
    (hA : ∀ i, derivedSubgroup (A i) = ⊤) : derivedSubgroup (pi A) = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro x _
  obtain ⟨l, _, hl⟩ := pi_point_eq_coordinate_prod A x
  rw [hl]
  apply ((derivedSubgroup (pi A)).carrier T).list_prod_mem
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hz
  apply comp_mem_derivedSubgroup
  rw [hA i]
  exact Subgroup.mem_top _

/-- Tensoring a slice morphism on the right of an identity is its cartesian base change. -/
theorem isPullback_id_tensorHom {X Y : Over S} (f : X ⟶ Y) (Z : Over S) :
    IsPullback (𝟙 Z ⊗ₘ f) (snd Z X) (snd Z Y) f := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift (c.fst ≫ fst Z Y) c.snd) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using c.condition.symm
  · intro c
    exact lift_snd _ _
  · intro c m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · have hs := congrArg (fun a => a ≫ fst Z Y) hm
      simpa only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst] using hs
    · simpa using hn

/-- Taking a product with an identity on the left preserves central isogenies. -/
theorem IsCentralIsogeny.id_tensor {C H : GroupScheme S} {f : C ⟶ H}
    (hf : IsCentralIsogeny f) (K : GroupScheme S) : IsCentralIsogeny (𝟙 K ⊗ₘ f) := by
  have hpb := ((isPullback_id_tensorHom f.hom.hom K.X).map (Over.forget S)).flip
  refine ⟨⟨MorphismProperty.of_isPullback hpb hf.isFinite,
    MorphismProperty.of_isPullback hpb hf.flat,
    MorphismProperty.of_isPullback hpb hf.surjective⟩,
    MorphismProperty.of_isPullback hpb hf.locallyOfFinitePresentation, ?_⟩
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  change x ≫ (𝟙 K.X ⊗ₘ f.hom.hom) = 1 at hx
  have hxC : (x ≫ snd K.X C.X) ≫ f.hom.hom = 1 := by
    have h := congrArg (fun w => w ≫ snd K.X H.X) hx
    simpa only [Category.assoc, tensorHom_snd, MonObj.one_comp] using h
  have hxK : x ≫ fst K.X C.X = 1 := by
    have h := congrArg (fun w => w ≫ fst K.X H.X) hx
    simpa only [Category.assoc, tensorHom_fst, Category.comp_id, MonObj.one_comp] using h
  intro T' a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, Category.assoc, hxK, MonObj.comp_one, one_mul, mul_one]
  · simp only [MonObj.mul_comp, Category.assoc]
    exact (hf.mem_center_of_comp_eq_one hxC T' a (y ≫ snd K.X C.X)).eq

section CommutingMultiplication

variable {H K G : GroupScheme S} (j : H ⟶ G) (i : K ⟶ G)
  (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
    Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

/-- The value of the commuting multiplication on an arbitrary point of the product. -/
theorem comp_commutingSubgroupMultiplicationHom {T : Over S} (z : T ⟶ (H ⊗ K).X) :
    z ≫ (commutingSubgroupMultiplicationHom j i hc).hom.hom =
      ((z ≫ fst H.X K.X) ≫ j.hom.hom) * ((z ≫ snd H.X K.X) ≫ i.hom.hom) := by
  rw [commutingSubgroupMultiplicationHom_hom, subgroupMultiplication, MonObj.comp_mul,
    Category.assoc, Category.assoc]

include hc in
/-- A normal subgroup of the left factor of a flat surjective commuting multiplication
is normal in the ambient group. -/
theorem isNormal_range_comp_left
    [QuasiCompact (commutingSubgroupMultiplicationHom j i hc).hom.hom.left]
    [Flat (commutingSubgroupMultiplicationHom j i hc).hom.hom.left]
    [Surjective (commutingSubgroupMultiplicationHom j i hc).hom.hom.left]
    {R : GroupScheme S} (r : R ⟶ H) (hr : (SubgroupFunctor.range r).IsNormal)
    [Mono (r ≫ j).hom.hom] : (SubgroupFunctor.range (r ≫ j)).IsNormal := by
  apply isNormal_range_of_lift (commutingSubgroupMultiplicationHom j i hc)
  intro T z x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [comp_commutingSubgroupMultiplicationHom]
  set a := (z ≫ fst H.X K.X) with ha
  set b := (z ≫ snd H.X K.X) with hb
  have hcomm : Commute ((y ≫ r.hom.hom) ≫ j.hom.hom) (b ≫ i.hom.hom) :=
    hc T (y ≫ r.hom.hom) b
  have hmem : a * (y ≫ r.hom.hom) * a⁻¹ ∈ (SubgroupFunctor.range r).carrier T :=
    hr T a (y ≫ r.hom.hom) (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp hmem
  refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hy', MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  simp only [Category.assoc] at hcomm ⊢
  calc (a ≫ j.hom.hom) * (y ≫ r.hom.hom ≫ j.hom.hom) * (a ≫ j.hom.hom)⁻¹
      = (a ≫ j.hom.hom) * ((b ≫ i.hom.hom) * (y ≫ r.hom.hom ≫ j.hom.hom) *
          (b ≫ i.hom.hom)⁻¹) * (a ≫ j.hom.hom)⁻¹ := by
        rw [hcomm.symm.eq, mul_inv_cancel_right]
    _ = (a ≫ j.hom.hom) * (b ≫ i.hom.hom) * (y ≫ r.hom.hom ≫ j.hom.hom) *
          ((a ≫ j.hom.hom) * (b ≫ i.hom.hom))⁻¹ := by group

include hc in
/-- A normal subgroup of the right factor of a flat surjective commuting multiplication
is normal in the ambient group. -/
theorem isNormal_range_comp_right
    [QuasiCompact (commutingSubgroupMultiplicationHom j i hc).hom.hom.left]
    [Flat (commutingSubgroupMultiplicationHom j i hc).hom.hom.left]
    [Surjective (commutingSubgroupMultiplicationHom j i hc).hom.hom.left]
    {R : GroupScheme S} (r : R ⟶ K) (hr : (SubgroupFunctor.range r).IsNormal)
    [Mono (r ≫ i).hom.hom] : (SubgroupFunctor.range (r ≫ i)).IsNormal := by
  apply isNormal_range_of_lift (commutingSubgroupMultiplicationHom j i hc)
  intro T z x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [comp_commutingSubgroupMultiplicationHom]
  set a := (z ≫ fst H.X K.X) with ha
  set b := (z ≫ snd H.X K.X) with hb
  have hcomm : Commute (a ≫ j.hom.hom) ((y ≫ r.hom.hom) ≫ i.hom.hom) :=
    hc T a (y ≫ r.hom.hom)
  have hmem : b * (y ≫ r.hom.hom) * b⁻¹ ∈ (SubgroupFunctor.range r).carrier T :=
    hr T b (y ≫ r.hom.hom) (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp hmem
  refine SubgroupFunctor.mem_range.mpr ⟨y', ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hy', MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp]
  simp only [Category.assoc] at hcomm ⊢
  calc (b ≫ i.hom.hom) * (y ≫ r.hom.hom ≫ i.hom.hom) * (b ≫ i.hom.hom)⁻¹
      = (a ≫ j.hom.hom) * ((b ≫ i.hom.hom) * (y ≫ r.hom.hom ≫ i.hom.hom) *
          (b ≫ i.hom.hom)⁻¹) * (a ≫ j.hom.hom)⁻¹ := by
        have h1 : Commute (a ≫ j.hom.hom) (b ≫ i.hom.hom) := hc T a b
        have h2 : Commute (a ≫ j.hom.hom)
            ((b ≫ i.hom.hom) * (y ≫ r.hom.hom ≫ i.hom.hom) * (b ≫ i.hom.hom)⁻¹) :=
          (h1.mul_right hcomm).mul_right h1.inv_right
        rw [h2.eq, mul_inv_cancel_right]
    _ = (a ≫ j.hom.hom) * (b ≫ i.hom.hom) * (y ≫ r.hom.hom ≫ i.hom.hom) *
          ((a ≫ j.hom.hom) * (b ≫ i.hom.hom))⁻¹ := by group

end CommutingMultiplication

section Commutant

variable {G H K B P P' : GroupScheme S}

/-- The commutant of a subgroup functor: the points all of whose restrictions commute with
every point of the given subgroup functor over the same test scheme. -/
def commutant (F : SubgroupFunctor G) : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | ∀ (T' : Over S) (a : T' ⟶ T) (h : T' ⟶ G.X), h ∈ F.carrier T' →
        Commute (a ≫ g) h}
      mul_mem' := by
        intro g g' hg hg' T' a h hh
        rw [MonObj.comp_mul]
        exact (hg T' a h hh).mul_left (hg' T' a h hh)
      one_mem' := by
        intro T' a h _
        rw [MonObj.comp_one]
        exact Commute.one_left h
      inv_mem' := by
        intro g hg T' a h hh
        rw [GrpObj.comp_inv]
        exact (hg T' a h hh).inv_left }
  comp_mem a g hg T'' b h hh := by
    rw [← Category.assoc]
    exact hg T'' (b ≫ a) h hh

theorem mem_commutant {F : SubgroupFunctor G} {T : Over S} {g : T ⟶ G.X} :
    g ∈ (commutant F).carrier T ↔
      ∀ (T' : Over S) (a : T' ⟶ T) (h : T' ⟶ G.X), h ∈ F.carrier T' → Commute (a ≫ g) h :=
  Iff.rfl

/-- A point of the commutant commutes with every point of the subgroup functor over the same
test scheme. -/
theorem commute_of_mem_commutant {F : SubgroupFunctor G} {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ (commutant F).carrier T) {h : T ⟶ G.X} (hh : h ∈ F.carrier T) :
    Commute g h := by
  simpa only [Category.id_comp] using hg T (𝟙 T) h hh

/-- Being contained in the commutant is symmetric. -/
theorem le_commutant_comm {F F' : SubgroupFunctor G} (h : F ≤ commutant F') :
    F' ≤ commutant F := by
  intro T x hx T' a y hy
  exact (commute_of_mem_commutant (h T' hy) (F'.comp_mem a hx)).symm

/-- The range of a homomorphism lies in the commutant exactly when its points commute with
the points of the subgroup functor. -/
theorem range_le_commutant_iff (n : K ⟶ G) (F : SubgroupFunctor G) :
    SubgroupFunctor.range n ≤ commutant F ↔
      ∀ (T : Over S) (x : T ⟶ K.X) (y : T ⟶ G.X), y ∈ F.carrier T →
        Commute (x ≫ n.hom.hom) y := by
  constructor
  · intro h T x y hy
    exact commute_of_mem_commutant (h T (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)) hy
  · intro h T g hg T' a y hy
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    rw [← Category.assoc]
    exact h T' (a ≫ x) y hy

/-- Commutant containment of a range descends along a quasi-compact, flat, surjective
homomorphism onto the source. -/
theorem range_le_commutant_of_comp (fac : P ⟶ B) [QuasiCompact fac.hom.hom.left]
    [Flat fac.hom.hom.left] [Surjective fac.hom.hom.left] (inc : B ⟶ G)
    (F : SubgroupFunctor G) (h : SubgroupFunctor.range (fac ≫ inc) ≤ commutant F) :
    SubgroupFunctor.range inc ≤ commutant F := by
  rw [range_le_commutant_iff] at h ⊢
  intro T x y hy
  obtain ⟨W, w, z, h1, h2, h3, hwz⟩ := exists_refinement_lift fac.hom.hom x
  have : Epi w.left := inferInstance
  apply commute_of_epi w
  have hz : w ≫ x ≫ inc.hom.hom = z ≫ (fac ≫ inc).hom.hom := by
    rw [← Category.assoc, hwz, Grp.comp_hom_hom, Category.assoc]
  rw [hz]
  exact h W z (w ≫ y) (F.comp_mem w hy)

/-- Range containment in a monomorphic subgroup descends along a quasi-compact, flat,
surjective homomorphism onto the source. -/
theorem range_le_of_comp_le (fac : P ⟶ B) [QuasiCompact fac.hom.hom.left]
    [Flat fac.hom.hom.left] [Surjective fac.hom.hom.left] (inc : B ⟶ G)
    (n : K ⟶ G) [Mono n.hom.hom]
    (h : SubgroupFunctor.range (fac ≫ inc) ≤ SubgroupFunctor.range n) :
    SubgroupFunctor.range inc ≤ SubgroupFunctor.range n := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨W, w, z, h1, h2, h3, hwz⟩ := exists_refinement_lift fac.hom.hom x
  apply SubgroupFunctor.mem_range_of_comp_mem_range n w
  have hz : w ≫ x ≫ inc.hom.hom = z ≫ (fac ≫ inc).hom.hom := by
    rw [← Category.assoc, hwz, Grp.comp_hom_hom, Category.assoc]
  rw [hz]
  exact h W (SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩)

/-- The image of a normal subgroup under a quasi-compact, flat, surjective homomorphism is
normal: if `fac ≫ inc = r ≫ mul` with `r` of normal range, `mul` and `fac` quasi-compact,
flat and surjective, and `inc` monomorphic, then `inc` has normal range. -/
theorem isNormal_range_of_image (mul : P ⟶ G) [QuasiCompact mul.hom.hom.left]
    [Flat mul.hom.hom.left] [Surjective mul.hom.hom.left] (fac : P' ⟶ B)
    [QuasiCompact fac.hom.hom.left] [Flat fac.hom.hom.left] [Surjective fac.hom.hom.left]
    (r : P' ⟶ P) (hr : (SubgroupFunctor.range r).IsNormal) (inc : B ⟶ G) [Mono inc.hom.hom]
    (h : fac ≫ inc = r ≫ mul) : (SubgroupFunctor.range inc).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨W₁, w₁, y', q₁, f₁, s₁, h₁⟩ := exists_refinement_lift fac.hom.hom y
  obtain ⟨W₂, w₂, z, q₂, f₂, s₂, h₂⟩ := exists_refinement_lift mul.hom.hom (w₁ ≫ g)
  have := effectiveEpi_comp_left w₁ w₂
  apply SubgroupFunctor.mem_range_of_comp_mem_range inc (w₂ ≫ w₁)
  have hx' : (w₂ ≫ w₁) ≫ y ≫ inc.hom.hom = (w₂ ≫ y' ≫ r.hom.hom) ≫ mul.hom.hom := by
    have hh := congrArg (fun f => f.hom.hom) h
    simp only [Grp.comp_hom_hom] at hh
    rw [Category.assoc, ← Category.assoc w₁, h₁]
    simp only [Category.assoc]
    rw [hh]
  have hg' : (w₂ ≫ w₁) ≫ g = z ≫ mul.hom.hom := by rw [Category.assoc, h₂]
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hg', hx', ← MonObj.mul_comp,
    ← GrpObj.inv_comp, ← MonObj.mul_comp]
  obtain ⟨y'', hy''⟩ := SubgroupFunctor.mem_range.mp
    (hr W₂ z (w₂ ≫ y' ≫ r.hom.hom) (Subgroup.mem_top _)
      (SubgroupFunctor.mem_range.mpr ⟨w₂ ≫ y', Category.assoc _ _ _⟩))
  refine SubgroupFunctor.mem_range.mpr ⟨y'' ≫ fac.hom.hom, ?_⟩
  have hh := congrArg (fun f => f.hom.hom) h
  simp only [Grp.comp_hom_hom] at hh
  rw [← hy'', Category.assoc, hh, Category.assoc]

/-- Ranges of composites with equal-range homomorphisms agree. -/
theorem range_comp_eq_of_range_eq {n : K ⟶ B} {n' : H ⟶ B} (inc : B ⟶ G)
    (h : SubgroupFunctor.range n = SubgroupFunctor.range n') :
    SubgroupFunctor.range (n ≫ inc) = SubgroupFunctor.range (n' ≫ inc) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  simp only [SubgroupFunctor.mem_range, Grp.comp_hom_hom]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≫ n.hom.hom ∈ (SubgroupFunctor.range n').carrier T := by
      rw [← h]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp hy
    exact ⟨y', by rw [← Category.assoc, hy', Category.assoc]⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≫ n'.hom.hom ∈ (SubgroupFunctor.range n).carrier T := by
      rw [h]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := SubgroupFunctor.mem_range.mp hy
    exact ⟨y', by rw [← Category.assoc, hy', Category.assoc]⟩

/-- A range contained in the range of a composite with a monomorphism comes from the
source. -/
theorem range_comp_le_iff (a : K ⟶ B) (b : B ⟶ G) (F : SubgroupFunctor G) :
    SubgroupFunctor.range (a ≫ b) ≤ F ↔ SubgroupFunctor.range a ≤ F.comap b := by
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

/-- The commutant reverses inclusions. -/
theorem commutant_anti {F F' : SubgroupFunctor G} (h : F ≤ F') : commutant F' ≤ commutant F :=
  fun _ _ hg T' a y hy => hg T' a y (h T' hy)

/-- The range of a composite lies in the range of its second factor. -/
theorem range_comp_le_range (a : K ⟶ B) (b : B ⟶ G) :
    SubgroupFunctor.range (a ≫ b) ≤ SubgroupFunctor.range b := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  exact SubgroupFunctor.mem_range.2 ⟨y ≫ a.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩

/-- The range of a homomorphism out of a group with total derived subgroup lies in a closed
subgroup as soon as the images of all commutators do. -/
theorem range_le_of_derivedSubgroup_eq_top (n : K ⟶ G) (hK : derivedSubgroup K = ⊤)
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (h : ∀ (T : Over S) (x y : T ⟶ K.X),
      (x * y * x⁻¹ * y⁻¹) ≫ n.hom.hom ∈ (SubgroupFunctor.range b).carrier T) :
    SubgroupFunctor.range n ≤ SubgroupFunctor.range b := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  have hx : x ∈ (derivedSubgroup K).carrier T := by
    rw [hK]
    exact Subgroup.mem_top _
  have hrange := range_subgroupIntersectionFst_eq_comap n b
  have hc : (SubgroupFunctor.range (subgroupIntersectionFst n b)).ContainsCommutators := by
    rw [hrange]
    intro U a c
    rw [SubgroupFunctor.mem_comap]
    exact h U a c
  have hmem := hx _ _ (isClosedSubgroup_subgroupIntersectionFst n hb) hc
  rw [hrange, SubgroupFunctor.mem_comap] at hmem
  exact hmem

end Commutant

/-- In a group, commutators are unchanged by factors that commute appropriately:
`[g c, h d] = [g, h]` when `c` commutes with `h d` and `d` commutes with `g`. -/
theorem commutator_mul_mul_eq {M : Type*} [Group M] (g c h d : M) (hc : Commute c (h * d))
    (hd : Commute d g) :
    g * c * (h * d) * (g * c)⁻¹ * (h * d)⁻¹ = g * h * g⁻¹ * h⁻¹ := by
  calc g * c * (h * d) * (g * c)⁻¹ * (h * d)⁻¹
      = g * (c * (h * d)) * c⁻¹ * g⁻¹ * (h * d)⁻¹ := by group
    _ = g * ((h * d) * c) * c⁻¹ * g⁻¹ * (h * d)⁻¹ := by rw [hc.eq]
    _ = g * h * (d * g⁻¹) * d⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * d) * d⁻¹ * h⁻¹ := by rw [hd.inv_right.eq]
    _ = g * h * g⁻¹ * h⁻¹ := by group

section Pi

variable {I : Type u} [Finite I] (A : I → GroupScheme S) {G : GroupScheme S}

/-- The range of a subproduct followed by a homomorphism lies in a subgroup functor exactly
when the images of the selected factors do. -/
theorem range_piSubsetInclusionHom_comp_le_iff (φ : pi A ⟶ G) (s : Set I)
    (F : SubgroupFunctor G) :
    SubgroupFunctor.range (piSubsetInclusionHom A s ≫ φ) ≤ F ↔
      ∀ i ∈ s, SubgroupFunctor.range (piFactorInclusionHom A i ≫ φ) ≤ F := by
  simp only [range_comp_le_iff, range_piSubsetInclusionHom_le_iff]

/-- The range of a homomorphism out of a finite product lies in a subgroup functor when the
images of all factors do. -/
theorem range_le_of_forall_factor (φ : pi A ⟶ G) (F : SubgroupFunctor G)
    (h : ∀ i, SubgroupFunctor.range (piFactorInclusionHom A i ≫ φ) ≤ F) :
    SubgroupFunctor.range φ ≤ F := by
  have hs := (range_piSubsetInclusionHom_comp_le_iff A φ Set.univ F).mpr
    (fun i _ => h i)
  intro T x hx
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hz : z ∈ (SubgroupFunctor.range (piSubsetInclusionHom A Set.univ)).carrier T :=
    (mem_range_piSubsetInclusionHom_iff A Set.univ z).mpr (fun i hi => (hi trivial).elim)
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  have := hs T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  simpa only [Grp.comp_hom_hom, Category.assoc] using this

/-- A subproduct projection followed by the subproduct inclusion keeps the selected
coordinates. -/
theorem piSubset_points_mem (s : Set I) {T : Over S} (u : T ⟶ (pi A).X) (l : I)
    (hl : l ∈ s) :
    (u ≫ (piSubsetProjectionHom A s ≫ piSubsetInclusionHom A s).hom.hom) ≫
      (Pi.π A l).hom.hom = u ≫ (Pi.π A l).hom.hom := by
  have h : piSubsetInclusionHom A s ≫ Pi.π A l = Pi.π (fun j : s => A j) ⟨l, hl⟩ :=
    piSubsetInclusionHom_π_mem A s ⟨l, hl⟩
  have h' : piSubsetProjectionHom A s ≫ Pi.π (fun j : s => A j) ⟨l, hl⟩ = Pi.π A l := by
    simp [piSubsetProjectionHom]
  rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc, h, h']

/-- A subproduct projection followed by the subproduct inclusion kills the other
coordinates. -/
theorem piSubset_points_notMem (s : Set I) {T : Over S} (u : T ⟶ (pi A).X) (l : I)
    (hl : l ∉ s) :
    (u ≫ (piSubsetProjectionHom A s ≫ piSubsetInclusionHom A s).hom.hom) ≫
      (Pi.π A l).hom.hom = 1 := by
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact piSubsetInclusionHom_points_notMem A s l hl _

/-- Every point of a finite product is the product of its restrictions to a subset of
coordinates and to the complementary subset. -/
theorem pi_point_eq_mul_compl (s : Set I) {T : Over S} (u : T ⟶ (pi A).X) :
    u = (u ≫ (piSubsetProjectionHom A s ≫ piSubsetInclusionHom A s).hom.hom) *
      (u ≫ (piSubsetProjectionHom A sᶜ ≫ piSubsetInclusionHom A sᶜ).hom.hom) := by
  apply (piPointsEquiv A T).injective
  funext l
  simp only [piPointsEquiv_apply]
  rw [MonObj.mul_comp]
  by_cases hl : l ∈ s
  · rw [piSubset_points_mem A s u l hl,
      piSubset_points_notMem A sᶜ u l (fun h => h hl), mul_one]
  · rw [piSubset_points_notMem A s u l hl,
      piSubset_points_mem A sᶜ u l hl, one_mul]

/-- The image of a point of a finite product splits as the product of an image of a point of
the subproduct on `s` and an image of a point of the subproduct on the complement. -/
theorem exists_mul_mem_range_piSubset (φ : pi A ⟶ G) (s : Set I) {T : Over S}
    (u : T ⟶ (pi A).X) :
    ∃ a c : T ⟶ G.X, u ≫ φ.hom.hom = a * c ∧
      a ∈ (SubgroupFunctor.range (piSubsetInclusionHom A s ≫ φ)).carrier T ∧
      c ∈ (SubgroupFunctor.range (piSubsetInclusionHom A sᶜ ≫ φ)).carrier T := by
  refine ⟨(u ≫ (piSubsetProjectionHom A s ≫ piSubsetInclusionHom A s).hom.hom) ≫ φ.hom.hom,
    (u ≫ (piSubsetProjectionHom A sᶜ ≫ piSubsetInclusionHom A sᶜ).hom.hom) ≫ φ.hom.hom,
    ?_, ?_, ?_⟩
  · rw [← MonObj.mul_comp, ← pi_point_eq_mul_compl A s u]
  · refine SubgroupFunctor.mem_range.2 ⟨u ≫ (piSubsetProjectionHom A s).hom.hom, ?_⟩
    simp only [Grp.comp_hom_hom, Category.assoc]
  · refine SubgroupFunctor.mem_range.2 ⟨u ≫ (piSubsetProjectionHom A sᶜ).hom.hom, ?_⟩
    simp only [Grp.comp_hom_hom, Category.assoc]

/-- Points of distinct factors of a finite product commute. -/
theorem commute_piFactorInclusionHom {i j : I} (h : i ≠ j) {T : Over S}
    (x : T ⟶ (A i).X) (y : T ⟶ (A j).X) :
    Commute (x ≫ (piFactorInclusionHom A i).hom.hom)
      (y ≫ (piFactorInclusionHom A j).hom.hom) := by
  change _ * _ = _ * _
  apply (piPointsEquiv A T).injective
  funext l
  simp only [piPointsEquiv_apply]
  rw [MonObj.mul_comp, MonObj.mul_comp]
  by_cases hl : i = l
  · subst hl
    rw [piFactorInclusionHom_points_ne A j i (Ne.symm h), mul_one, one_mul]
  · rw [piFactorInclusionHom_points_ne A i l hl, mul_one, one_mul]

/-- A factor inclusion of a subproduct followed by the subproduct inclusion is the factor
inclusion of the whole product. -/
theorem piFactorInclusionHom_comp_piSubsetInclusionHom (s : Set I) (i : s) :
    piFactorInclusionHom (fun j : s => A j) i ≫ piSubsetInclusionHom A s =
      piFactorInclusionHom A i := by
  apply hom_ext_points
  intro T x
  apply (piPointsEquiv A T).injective
  funext l
  simp only [piPointsEquiv_apply]
  rw [Grp.comp_hom_hom, ← Category.assoc]
  by_cases hl : l ∈ s
  · have h : piSubsetInclusionHom A s ≫ Pi.π A l = Pi.π (fun j : s => A j) ⟨l, hl⟩ :=
      piSubsetInclusionHom_π_mem A s ⟨l, hl⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, h]
    by_cases hil : (i : I) = l
    · obtain ⟨i, hi⟩ := i
      subst hil
      rw [piFactorInclusionHom_points_self A]
      exact piFactorInclusionHom_points_self (fun j : s => A j) ⟨i, hi⟩ x
    · have hne : i ≠ ⟨l, hl⟩ := fun he => hil (congrArg Subtype.val he)
      rw [piFactorInclusionHom_points_ne (fun j : s => A j) i ⟨l, hl⟩ hne,
        piFactorInclusionHom_points_ne A i l hil]
  · have hil : (i : I) ≠ l := fun he => hl (he ▸ i.property)
    rw [piSubsetInclusionHom_points_notMem A s l hl, piFactorInclusionHom_points_ne A i l hil]

end Pi

end Langlands.GroupScheme.SimpleFactor
