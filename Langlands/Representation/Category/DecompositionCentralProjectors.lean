import Langlands.Representation.Category.CoproductCompression
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Mathlib.CategoryTheory.Center.Preadditive
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.BigOperators.Finprod

/-! # Central projectors of an arbitrary smooth category decomposition -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe uG uV uI

namespace Langlands.SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} [DecidableEq I]
  {A : I → SmoothRep.{0, uG, uV} ℂ G} {X : SmoothRep.{0, uG, uV} ℂ G}
  {ι : ∀ i, A i ⟶ X}

/-- Projection associated to a supplied actual coproduct. -/
def cofanProjection (hc : IsColimit (Cofan.mk X ι)) (i : I) : X ⟶ A i :=
  Cofan.IsColimit.desc hc (fun j => if h : j = i then eqToHom (congrArg A h) else 0)

@[simp] theorem inj_cofanProjection_self (hc : IsColimit (Cofan.mk X ι)) (i : I) :
    ι i ≫ cofanProjection hc i = 𝟙 _ := by
  change (Cofan.mk X ι).inj i ≫ Cofan.IsColimit.desc hc _ = _
  rw [Cofan.IsColimit.fac]
  simp

@[simp] theorem inj_cofanProjection_ne (hc : IsColimit (Cofan.mk X ι))
    {i j : I} (h : j ≠ i) : ι j ≫ cofanProjection hc i = 0 := by
  change (Cofan.mk X ι).inj j ≫ Cofan.IsColimit.desc hc _ = _
  rw [Cofan.IsColimit.fac]
  simp [h]

/-- The categorical projection is the actual direct-sum coordinate map. -/
theorem cofanProjection_directSumMap (hc : IsColimit (Cofan.mk X ι)) (i : I)
    (x : ⨁ j, A j) :
    hom (cofanProjection hc i) (cofanDirectSumMap A (Cofan.mk X ι) x) = x i := by
  have hlin : (hom (cofanProjection hc i)).toLinearMap.comp
      (cofanDirectSumMap A (Cofan.mk X ι)).toLinearMap =
      DirectSum.component ℂ I (fun j => A j) i := by
    apply DirectSum.linearMap_ext
    intro j
    ext v
    change hom (cofanProjection hc i)
      (cofanDirectSumMap A (Cofan.mk X ι) (DirectSum.lof ℂ I (fun j => A j) j v)) = _
    rw [cofanDirectSumMap_lof]
    change hom (ι j ≫ cofanProjection hc i) v = _
    by_cases h : j = i
    · subst j
      rw [inj_cofanProjection_self]
      simp
    · rw [inj_cofanProjection_ne hc h]
      simp [DirectSum.component.of, h]
      rfl
  exact LinearMap.congr_fun hlin x

/-- Actual smooth coproduct projections separate vectors, at arbitrary index universe. -/
theorem eq_of_cofanProjections (hc : IsColimit (Cofan.mk X ι)) {x y : X}
    (h : ∀ i, hom (cofanProjection hc i) x = hom (cofanProjection hc i) y) : x = y := by
  obtain ⟨a, rfl⟩ := cofanDirectSumMap_surjective A (Cofan.mk X ι) hc x
  obtain ⟨b, rfl⟩ := cofanDirectSumMap_surjective A (Cofan.mk X ι) hc y
  apply congrArg (cofanDirectSumMap A (Cofan.mk X ι))
  ext i
  simpa only [cofanProjection_directSumMap] using h i

/-- Actual smooth coproduct projections separate morphisms. -/
theorem hom_ext_cofanProjections (hc : IsColimit (Cofan.mk X ι))
    {W : SmoothRep.{0, uG, uV} ℂ G} {f g : W ⟶ X}
    (h : ∀ i, f ≫ cofanProjection hc i = g ≫ cofanProjection hc i) : f = g := by
  apply ObjectProperty.hom_ext
  ext w
  apply eq_of_cofanProjections hc
  intro i
  exact congrArg (fun k => hom k w) (h i)

variable {P : I → ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)}

/-- Every map from one block to a decomposed object lands in its corresponding summand. -/
theorem comp_cofanComponent (hP : Renard.OffDiagonalHomsZero P)
    (hA : ∀ i, P i (A i)) (hc : IsColimit (Cofan.mk X ι))
    {W : SmoothRep.{0, uG, uV} ℂ G} (g : W ⟶ X) (j : I) (hW : P j W) :
    g ≫ cofanProjection hc j ≫ ι j = g := by
  apply hom_ext_cofanProjections hc
  intro k
  by_cases h : j = k
  · subst k
    simp only [Category.assoc, inj_cofanProjection_self, Category.comp_id]
  · rw [Category.assoc, Category.assoc, inj_cofanProjection_ne hc h]
    rw [Limits.comp_zero, Limits.comp_zero]
    exact (hP j k h W (A k) hW (hA k) (g ≫ cofanProjection hc k)).symm

variable (hP : Renard.IsCategoryDecomposition P)

/-- The endomorphism projecting an object to a chosen block component. -/
def centralProjectorApp (i : I) (X : SmoothRep.{0, uG, uV} ℂ G) : X ⟶ X :=
  cofanProjection (hP.1 X).choose_spec.choose_spec.2.some i ≫
    (hP.1 X).choose_spec.choose i

/-- A block projector is the identity on incoming maps from that block and zero on others. -/
theorem comp_centralProjectorApp {X W : SmoothRep.{0, uG, uV} ℂ G}
    (g : W ⟶ X) (i j : I) (hW : P j W) :
    g ≫ centralProjectorApp hP i X = if j = i then g else 0 := by
  by_cases h : j = i
  · subst j
    rw [ite_eq_left rfl]
    exact comp_cofanComponent hP.2 (hP.1 X).choose_spec.choose_spec.1 _ g i hW
  · rw [ite_eq_right h]
    unfold centralProjectorApp
    rw [← Category.assoc]
    have hz := hP.2 j i h W ((hP.1 X).choose i) hW
      ((hP.1 X).choose_spec.choose_spec.1 i)
      (g ≫ cofanProjection (hP.1 X).choose_spec.choose_spec.2.some i)
    rw [hz]
    simp

/-- The central projector attached to one component of a smooth category decomposition. -/
def centralProjector (i : I) : CatCenter (SmoothRep.{0, uG, uV} ℂ G) where
  app X := centralProjectorApp hP i X
  naturality X Y f := by
    obtain ⟨A, ι, hA, hc⟩ := hP.1 X
    apply Cofan.IsColimit.hom_ext hc.some
    intro j
    change ι j ≫ f ≫ centralProjectorApp hP i Y =
      ι j ≫ centralProjectorApp hP i X ≫ f
    rw [← Category.assoc, comp_centralProjectorApp hP _ i j (hA j),
      ← Category.assoc, comp_centralProjectorApp hP _ i j (hA j)]
    split <;> simp

@[simp] theorem centralProjector_app_of_mem (i : I)
    (X : SmoothRep.{0, uG, uV} ℂ G) (hX : P i X) :
    (centralProjector hP i).app X = 𝟙 X := by
  have h := comp_centralProjectorApp hP (𝟙 X) i i hX
  simpa [centralProjector] using h

theorem centralProjector_app_of_ne (i j : I) (h : j ≠ i)
    (X : SmoothRep.{0, uG, uV} ℂ G) (hX : P j X) :
    (centralProjector hP i).app X = 0 := by
  have hh := comp_centralProjectorApp hP (𝟙 X) i j hX
  simpa [h, centralProjector] using hh

theorem centralProjector_idempotent (i : I) : IsIdempotentElem (centralProjector hP i) := by
  apply CatCenter.ext
  intro X
  obtain ⟨A, ι, hA, hc⟩ := hP.1 X
  rw [CatCenter.mul_app]
  apply Cofan.IsColimit.hom_ext hc.some
  intro j
  change ι j ≫ centralProjectorApp hP i X ≫ centralProjectorApp hP i X =
    ι j ≫ centralProjectorApp hP i X
  rw [← Category.assoc, comp_centralProjectorApp hP _ i j (hA j)]
  by_cases h : j = i
  · simp only [ite_eq_left h]
  · simpa only [ite_eq_right h, Limits.zero_comp] using
      (comp_centralProjectorApp hP (ι j) i j (hA j)).symm

/-- Every vector is the finite sum of its coproduct components. -/
theorem cofanComponents_finite_sum (hc : IsColimit (Cofan.mk X ι)) (v : X) :
    (Function.support fun i => hom (cofanProjection hc i ≫ ι i) v).Finite ∧
      ∑ᶠ i, hom (cofanProjection hc i ≫ ι i) v = v := by
  classical
  obtain ⟨x, rfl⟩ := cofanDirectSumMap_surjective A (Cofan.mk X ι) hc v
  have heq (i : I) : hom (cofanProjection hc i ≫ ι i)
      (cofanDirectSumMap A (Cofan.mk X ι) x) = hom (ι i) (x i) := by
    change hom (ι i) (hom (cofanProjection hc i) _) = _
    rw [cofanProjection_directSumMap]
  have hs : (Function.support fun i => hom (cofanProjection hc i ≫ ι i)
      (cofanDirectSumMap A (Cofan.mk X ι) x)) ⊆ (x.support : Set I) := by
    intro i hi
    by_contra hn
    have hx : x i = 0 := by simpa using hn
    apply hi
    change hom (cofanProjection hc i ≫ ι i) _ = 0
    rw [heq, hx]
    exact map_zero _
  refine ⟨x.support.finite_toSet.subset hs, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp_rw [heq]
  have hsum := congrArg (cofanDirectSumMap A (Cofan.mk X ι)) (DirectSum.sum_support_of x)
  have hmap (i : I) (v : A i) :
      cofanDirectSumMap A (Cofan.mk X ι) (DirectSum.of (fun j => A j) i v) =
        hom (ι i) v := cofanDirectSumMap_lof A (Cofan.mk X ι) i v
  simpa only [map_sum, hmap] using hsum

/-- The sum of the central block projectors is finite on each vector and equals the identity. -/
theorem centralProjector_finite_sum (X : SmoothRep.{0, uG, uV} ℂ G) (v : X) :
    (Function.support fun i => hom ((centralProjector hP i).app X) v).Finite ∧
      ∑ᶠ i, hom ((centralProjector hP i).app X) v = v :=
  cofanComponents_finite_sum (hP.1 X).choose_spec.choose_spec.2.some v

/-- The action on the blocks determines a central projector uniquely. -/
theorem centralProjector_unique (i : I) (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G))
    (hid : ∀ X, P i X → z.app X = 𝟙 X)
    (hzero : ∀ j, j ≠ i → ∀ X, P j X → z.app X = 0) :
    z = centralProjector hP i := by
  apply CatCenter.ext
  intro X
  obtain ⟨A, ι, hA, hc⟩ := hP.1 X
  apply Cofan.IsColimit.hom_ext hc.some
  intro j
  change ι j ≫ z.app X = ι j ≫ centralProjectorApp hP i X
  rw [CatCenter.naturality, comp_centralProjectorApp hP _ i j (hA j)]
  by_cases h : j = i
  · subst j
    simp [hid (A i) (hA i)]
  · simp [h, hzero j h (A j) (hA j)]

/-- Distinct block projectors are orthogonal. -/
theorem centralProjector_mul_of_ne (i j : I) (h : i ≠ j) :
    centralProjector hP i * centralProjector hP j = 0 := by
  apply CatCenter.ext
  intro X
  obtain ⟨A, ι, hA, hc⟩ := hP.1 X
  rw [CatCenter.mul_app]
  apply Cofan.IsColimit.hom_ext hc.some
  intro k
  change ι k ≫ centralProjectorApp hP i X ≫ centralProjectorApp hP j X = ι k ≫ 0
  rw [← Category.assoc, comp_centralProjectorApp hP _ i k (hA k)]
  by_cases hk : k = i
  · subst k
    rw [ite_eq_left rfl, comp_centralProjectorApp hP _ j i (hA i), ite_eq_right h]
    simp
  · simp [hk]

end Langlands.SmoothRep
