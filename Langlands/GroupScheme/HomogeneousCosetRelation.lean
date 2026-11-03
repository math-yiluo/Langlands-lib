import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The actual smooth closed right-coset relation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousCosetRelation

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)

/-- The actual scheme of right-coset arrows. -/
abbrev arrows (_i : H ⟶ G) : Over S := G.X ⊗ H.X

/-- An arrow `(g,h)` starts at `g`. -/
def source : arrows i ⟶ G.X := fst G.X H.X

/-- An arrow `(g,h)` ends at `g * i(h)`. -/
def target : arrows i ⟶ G.X := fst G.X H.X * (snd G.X H.X ≫ i.hom.hom)

/-- The map displaying the coset relation inside the product of `G` with itself. -/
def inclusion : arrows i ⟶ G.X ⊗ G.X := lift (source i) (target i)

/-- The right difference `(g,h) ↦ g⁻¹ * h`. -/
def difference : G.X ⊗ G.X ⟶ G.X := (fst G.X G.X)⁻¹ * snd G.X G.X

@[simp] theorem lift_source {T : Over S} (g : T ⟶ G.X) (h : T ⟶ H.X) :
    lift g h ≫ source i = g := by simp [source]

@[simp] theorem lift_target {T : Over S} (g : T ⟶ G.X) (h : T ⟶ H.X) :
    lift g h ≫ target i = g * (h ≫ i.hom.hom) := by
  simp [target, MonObj.comp_mul]

@[simp] theorem inclusion_fst : inclusion i ≫ fst G.X G.X = source i := by
  simp [inclusion]

@[simp] theorem inclusion_snd : inclusion i ≫ snd G.X G.X = target i := by
  simp [inclusion]

@[simp] theorem lift_difference {T : Over S} (g h : T ⟶ G.X) :
    lift g h ≫ difference (G := G) = g⁻¹ * h := by
  simp [difference, MonObj.comp_mul, GrpObj.comp_inv]

/-- On every test scheme the arrow relation is exactly the published range subgroup. -/
theorem exists_arrow_iff {T : Over S} (g h : T ⟶ G.X) :
    (∃ a : T ⟶ arrows i, a ≫ source i = g ∧ a ≫ target i = h) ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  constructor
  · rintro ⟨a, rfl, rfl⟩
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨a ≫ snd G.X H.X, ?_⟩
    simp [source, target, MonObj.comp_mul]
  · intro hgh
    obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hgh
    refine ⟨lift g a, by simp, ?_⟩
    rw [lift_target, ha, mul_inv_cancel_left]

/-- A monomorphic subgroup has at most one arrow between two points, on all tests. -/
theorem arrow_unique [Mono i.hom.hom] {T : Over S} {a b : T ⟶ arrows i}
    (hs : a ≫ source i = b ≫ source i) (ht : a ≫ target i = b ≫ target i) : a = b := by
  apply hom_ext
  · exact hs
  · apply (cancel_mono i.hom.hom).mp
    change a ≫ fst G.X H.X = b ≫ fst G.X H.X at hs
    simp only [target, MonObj.comp_mul] at ht
    rw [hs] at ht
    simpa only [Category.assoc] using mul_left_cancel ht

/-- The relation is the scheme-theoretic inverse image of the subgroup under right difference. -/
theorem inclusion_isPullback :
    IsPullback (snd G.X H.X) (inclusion i) i.hom.hom (difference (G := G)) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift (c.snd ≫ fst G.X G.X) c.fst) ?_ ?_ ?_⟩⟩
  · simp [inclusion, difference, source, target, MonObj.comp_mul, GrpObj.comp_inv]
  · intro c
    simp
  · intro c
    apply hom_ext
    · simp [inclusion, source]
    · have hc := c.condition
      simp only [difference, MonObj.comp_mul, GrpObj.comp_inv] at hc
      simp only [Category.assoc, inclusion_snd, lift_target]
      rw [hc, mul_inv_cancel_left]
  · intro c m hm₁ hm₂
    apply hom_ext
    · have h := congrArg (fun a => a ≫ fst G.X G.X) hm₂
      simpa [Category.assoc, inclusion, source] using h
    · simpa using hm₁

/-- A closed subgroup gives a closed immersion of the actual relation into `G × G`. -/
theorem inclusion_isClosedImmersion (hi : IsClosedSubgroup i) :
    IsClosedImmersion (inclusion i).left := by
  exact MorphismProperty.of_isPullback
    ((inclusion_isPullback i).map (Over.forget S)) hi

/-- Right multiplication gives an automorphism of the arrow scheme, with fixed subgroup point. -/
def translationIso : arrows i ≅ arrows i where
  hom := lift (target i) (snd G.X H.X)
  inv := lift (fst G.X H.X * ((snd G.X H.X ≫ i.hom.hom)⁻¹)) (snd G.X H.X)
  hom_inv_id := by
    apply hom_ext <;> simp [target, MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
  inv_hom_id := by
    apply hom_ext <;> simp [target, MonObj.comp_mul, mul_assoc]

/-- The target projection is the source projection after an actual scheme automorphism. -/
theorem translationIso_hom_source : (translationIso i).hom ≫ source i = target i := by
  simp [translationIso, source]

/-- The source projection is smooth whenever the subgroup is smooth over the base. -/
theorem source_smooth (hH : Smooth H.X.hom) : Smooth (source i).left := by
  let : Smooth H.X.hom := hH
  change Smooth (pullback.fst G.X.hom H.X.hom)
  infer_instance

/-- The target projection is smooth by translation and smoothness of the source projection. -/
theorem target_smooth (hH : Smooth H.X.hom) : Smooth (target i).left := by
  let : Smooth (source i).left := source_smooth i hH
  let : IsIso (translationIso i).hom.left :=
    (Over.forget S).map_isIso (translationIso i).hom
  rw [← translationIso_hom_source, Over.comp_left]
  infer_instance

/-- The full all-test coset criterion follows from an actual kernel-pair square. -/
theorem fibers_of_isPullback {Q : Over S} (q : G.X ⟶ Q)
    (hq : IsPullback (source i) (target i) q q)
    (T : Over S) (g h : T ⟶ G.X) :
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  rw [← exists_arrow_iff]
  constructor
  · intro hgh
    exact ⟨hq.lift g h hgh, hq.lift_fst _ _ _, hq.lift_snd _ _ _⟩
  · rintro ⟨a, rfl, rfl⟩
    simpa only [Category.assoc] using congrArg (fun b => a ≫ b) hq.w

end Langlands.GroupScheme.HomogeneousCosetRelation
