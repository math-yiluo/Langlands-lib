import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Shear coordinates and geometric smoothness for the Galois norm -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.GaloisNormSmoothnessGeometry

set_option backward.isDefEq.respectTransparency false

section Shear

variable {I : Type v} [Fintype I] [DecidableEq I] (i₀ : I)
variable {M : Type w} [CommGroup M]

private theorem prod_split (x : I → M) :
    ∏ i, x i = x i₀ * ∏ i : {i : I // i ≠ i₀}, x i := by
  classical
  let : Unique {i : I // i = i₀} :=
    ⟨⟨i₀, rfl⟩, fun i => Subtype.ext i.property⟩
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : I => i = i₀) x
  simpa only [Fintype.prod_unique, (default : {i : I // i = i₀}).property] using h.symm

/-- Replace one coordinate by the total product, retaining all other coordinates. -/
def shearEquiv : (I → M) ≃* (M × ({i : I // i ≠ i₀} → M)) := by
  classical
  exact
    { toFun := fun x => (∏ i, x i, fun i => x i)
      invFun := fun y i =>
        if h : i = i₀ then y.1 * (∏ j, y.2 j)⁻¹ else y.2 ⟨i, h⟩
      left_inv := by
        intro x
        funext i
        by_cases h : i = i₀
        · subst i
          simp only [dite_true, prod_split i₀, mul_inv_cancel_right]
        · simp only [h, dite_false]
      right_inv := by
        intro y
        apply Prod.ext
        · change
            (∏ i, if h : i = i₀ then y.1 * (∏ j, y.2 j)⁻¹ else y.2 ⟨i, h⟩) =
              y.1
          rw [prod_split i₀]
          simp only [dite_true]
          have hrest (i : {i : I // i ≠ i₀}) :
              (if h : (i : I) = i₀ then y.1 * (∏ j, y.2 j)⁻¹ else y.2 ⟨i, h⟩) =
                y.2 i := by
            simp only [i.property, dite_false]
          simp_rw [hrest]
          simp
        · funext i
          simp only [i.property, dite_false]
      map_mul' := by
        intro x y
        apply Prod.ext
        · exact Finset.prod_mul_distrib
        · rfl }

@[simp]
theorem shearEquiv_fst (x : I → M) :
    (shearEquiv i₀ x).1 = ∏ i, x i := rfl

@[simp]
theorem shearEquiv_snd (x : I → M) (i : {i : I // i ≠ i₀}) :
    (shearEquiv i₀ x).2 i = x i := rfl

/-- The shear commutes with every homomorphism of commutative groups. -/
theorem shearEquiv_naturality {N : Type*} [CommGroup N] (f : M →* N) (x : I → M) :
    shearEquiv i₀ (fun i => f (x i)) =
      (f (shearEquiv i₀ x).1, fun i => f ((shearEquiv i₀ x).2 i)) := by
  apply Prod.ext
  · exact (map_prod f x Finset.univ).symm
  · rfl

end Shear

section Geometry

variable {S : Scheme.{u}}

/-- Projection onto the first factor is smooth if the second factor is smooth over the base. -/
theorem smooth_fst (G H : GroupScheme S) (hH : Smooth H.X.hom) :
    Smooth (fst G.X H.X).left := by
  let : Smooth H.X.hom := hH
  change Smooth (pullback.fst G.X.hom H.X.hom)
  infer_instance

/-- A map is smooth if an isomorphism identifies it with a smooth product projection. -/
theorem smooth_of_iso_fst {W G H : GroupScheme S}
    (e : W.X ≅ (G ⊗ H).X) (f : W.X ⟶ G.X)
    (he : e.hom.left ≫ (fst G.X H.X).left = f.left)
    (hH : Smooth H.X.hom) : Smooth f.left := by
  let : Smooth (fst G.X H.X).left := smooth_fst G H hH
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← he]
  infer_instance

/-- The other coordinates of a finite product of smooth groups form a smooth group. -/
theorem smooth_complement {I : Type u} [Finite I] (i₀ : I)
    (G : GroupScheme S) (hG : Smooth G.X.hom) :
    Smooth (pi (fun _ : {i : I // i ≠ i₀} => G)).X.hom :=
  smooth_pi _ (fun _ => hG)

/-- Smoothness of an actual group-scheme morphism descends under fpqc base change. -/
theorem smooth_of_baseChange {S' : Scheme.{u}} (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b] {W G : GroupScheme S}
    (f : W ⟶ G) (hf : Smooth ((GroupScheme.baseChange b).map f).hom.hom.left) :
    Smooth f.hom.hom.left := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.snd G.X.hom b)
      (pullback.fst W.X.hom b) b (f.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback W.X.hom b).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst W.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hf

/-- Smoothness of an actual group morphism can be checked after a field extension. -/
theorem smooth_of_field_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {W G : GroupScheme (Spec (CommRingCat.of k))} (f : W ⟶ G)
    (hf : Smooth ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).hom.hom.left) :
    Smooth f.hom.hom.left := by
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc k K
  let : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := h₁
  let : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := h₂
  let : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K))) := h₃
  exact smooth_of_baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K))) f hf

end Geometry

end Langlands.GroupScheme.GaloisNormSmoothnessGeometry
