import Langlands.GroupScheme.Reductive.RelativeDerivedInputs

/-! # Descent and group operations for fppf-local commutator membership -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeDerived

variable {S : Scheme.{u}} {G : GroupScheme S} {T U : Over S}

/-- Restriction of points preserves the abstract commutator subgroup. -/
theorem commutator_precomp (a : U ⟶ T) {x : T ⟶ G.X}
    (hx : x ∈ _root_.commutator (T ⟶ G.X)) :
    a ≫ x ∈ _root_.commutator (U ⟶ G.X) := by
  let f : (T ⟶ G.X) →* (U ⟶ G.X) :=
    { toFun := fun x => a ≫ x
      map_one' := MonObj.comp_one a
      map_mul' := MonObj.comp_mul a }
  have hm : f x ∈ (_root_.commutator (T ⟶ G.X)).map f :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hle : (_root_.commutator (T ⟶ G.X)).map f ≤ _root_.commutator (U ⟶ G.X) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact hle hm

/-- Abstract commutator membership implies fppf-local membership. -/
theorem LocallyCommutator.of_mem {x : T ⟶ G.X}
    (hx : x ∈ _root_.commutator (T ⟶ G.X)) : LocallyCommutator x := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun _ => ⟨inferInstance, inferInstance⟩⟩
  refine ⟨Scheme.coverOfIsIso (P := @Flat ⊓ @LocallyOfFinitePresentation) (𝟙 T.left), ?_⟩
  intro i
  exact commutator_precomp _ hx

/-- Fppf-local commutator membership is preserved by every restriction of the test scheme. -/
theorem LocallyCommutator.restrict {x : T ⟶ G.X} (hx : LocallyCommutator x)
    (a : U ⟶ T) : LocallyCommutator (a ≫ x) := by
  obtain ⟨𝒰, h𝒰⟩ := hx
  refine ⟨𝒰.pullback₁ a.left, fun i => ?_⟩
  let b : Over.mk (pullback.fst a.left (𝒰.f i) ≫ U.hom) ⟶
      Over.mk (𝒰.f i ≫ T.hom) :=
    Over.homMk (pullback.snd a.left (𝒰.f i)) (by
      change pullback.snd a.left (𝒰.f i) ≫ (𝒰.f i ≫ T.hom) =
        pullback.fst a.left (𝒰.f i) ≫ U.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc, a.w])
  have hb := commutator_precomp b (h𝒰 i)
  change (Over.homMk (pullback.fst a.left (𝒰.f i)) rfl :
    Over.mk (pullback.fst a.left (𝒰.f i) ≫ U.hom) ⟶ U) ≫ (a ≫ x) ∈
      _root_.commutator (Over.mk (pullback.fst a.left (𝒰.f i) ≫ U.hom) ⟶ G.X)
  have he : (Over.homMk (pullback.fst a.left (𝒰.f i)) rfl :
      Over.mk (pullback.fst a.left (𝒰.f i) ≫ U.hom) ⟶ U) ≫ (a ≫ x) =
      b ≫ (Over.homMk (𝒰.f i) rfl) ≫ x := by
    apply Over.OverMorphism.ext
    change pullback.fst a.left (𝒰.f i) ≫ (a.left ≫ x.left) =
      pullback.snd a.left (𝒰.f i) ≫ (𝒰.f i ≫ x.left)
    rw [← Category.assoc, pullback.condition, Category.assoc]
  rw [he]
  exact hb

/-- Membership on all members of an fppf cover descends to the original test scheme. -/
theorem LocallyCommutator.of_cover {x : T ⟶ G.X}
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left)
    (h : ∀ i, LocallyCommutator
      ((Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ x)) :
    LocallyCommutator x := by
  classical
  choose 𝒱 h𝒱 using h
  refine ⟨𝒰.bind 𝒱, fun ij => ?_⟩
  rcases ij with ⟨i, j⟩
  change (Over.homMk ((𝒱 i).f j ≫ 𝒰.f i) rfl :
    Over.mk (((𝒱 i).f j ≫ 𝒰.f i) ≫ T.hom) ⟶ T) ≫ x ∈
      _root_.commutator (Over.mk (((𝒱 i).f j ≫ 𝒰.f i) ≫ T.hom) ⟶ G.X)
  let a : Over.mk (((𝒱 i).f j ≫ 𝒰.f i) ≫ T.hom) ⟶
      Over.mk ((𝒱 i).f j ≫ (𝒰.f i ≫ T.hom)) :=
    Over.homMk (𝟙 _) (by
      change (𝟙 _) ≫ ((𝒱 i).f j ≫ (𝒰.f i ≫ T.hom)) =
        (((𝒱 i).f j ≫ 𝒰.f i) ≫ T.hom)
      simp only [Category.id_comp, Category.assoc])
  have ha := commutator_precomp a (h𝒱 i j)
  have he : (Over.homMk ((𝒱 i).f j ≫ 𝒰.f i) rfl :
      Over.mk (((𝒱 i).f j ≫ 𝒰.f i) ≫ T.hom) ⟶ T) ≫ x =
      a ≫ (Over.homMk ((𝒱 i).f j) rfl) ≫ (Over.homMk (𝒰.f i) rfl) ≫ x := by
    apply Over.OverMorphism.ext
    change ((𝒱 i).f j ≫ 𝒰.f i) ≫ x.left =
      (𝟙 _) ≫ ((𝒱 i).f j ≫ (𝒰.f i ≫ x.left))
    simp only [Category.id_comp, Category.assoc]
  rw [he]
  exact ha

/-- The identity point belongs to the fppf-local commutator subgroup. -/
theorem LocallyCommutator.one : LocallyCommutator (1 : T ⟶ G.X) :=
  .of_mem (Subgroup.one_mem _)

/-- Fppf-local commutator membership is closed under inversion. -/
theorem LocallyCommutator.inv {x : T ⟶ G.X} (hx : LocallyCommutator x) :
    LocallyCommutator x⁻¹ := by
  obtain ⟨𝒰, h𝒰⟩ := hx
  refine ⟨𝒰, fun i => ?_⟩
  rw [GrpObj.comp_inv]
  exact Subgroup.inv_mem _ (h𝒰 i)

/-- Fppf-local commutator membership is closed under products. -/
theorem LocallyCommutator.mul {x y : T ⟶ G.X}
    (hx : LocallyCommutator x) (hy : LocallyCommutator y) : LocallyCommutator (x * y) := by
  obtain ⟨𝒰, h𝒰⟩ := hx
  apply LocallyCommutator.of_cover 𝒰
  intro i
  let a : Over.mk (𝒰.f i ≫ T.hom) ⟶ T := Over.homMk (𝒰.f i) rfl
  obtain ⟨𝒱, h𝒱⟩ := hy.restrict a
  refine ⟨𝒱, fun j => ?_⟩
  rw [MonObj.comp_mul, MonObj.comp_mul]
  exact Subgroup.mul_mem _ (commutator_precomp _ (h𝒰 i)) (h𝒱 j)

/-- The fppf-local commutator points form a subgroup on every test scheme. -/
def locallyCommutatorSubgroup (T : Over S) : Subgroup (T ⟶ G.X) where
  carrier := LocallyCommutator
  one_mem' := LocallyCommutator.one
  mul_mem' := LocallyCommutator.mul
  inv_mem' := LocallyCommutator.inv

end Langlands.GroupScheme.RelativeDerived
