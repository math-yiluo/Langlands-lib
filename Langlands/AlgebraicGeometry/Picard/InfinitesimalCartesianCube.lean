import Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenSquare

/-! # Sections of cartesian cubes over affine open immersions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalCartesianCube

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual base projection of a scheme mapping to the relative space over `R`. -/
def baseProjection {T : Scheme.{u}}
    (t : T ⟶ (relativeSpace f).obj (affineBase k R)) :
    T ⟶ (affineBase k R).left :=
  t ≫ (relativeProjection f).app (affineBase k R)

instance baseProjection_flat {T : Scheme.{u}}
    (t : T ⟶ (relativeSpace f).obj (affineBase k R)) [IsOpenImmersion t] :
    Flat (baseProjection f t) := by
  dsimp [baseProjection, relativeProjection]
  infer_instance

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

include h in
/-- Every cartesian cube over an affine open immersion has the actual ring pullback. -/
theorem cartesianCube_appTop_isPullback {T T₀ T₁ T₂ : Scheme.{u}}
    (t : T ⟶ (relativeSpace f).obj (affineBase k R)) [IsOpenImmersion t] [IsAffine T]
    (s₁ : T₁ ⟶ T) (s₂ : T₂ ⟶ T) (ι₁ : T₀ ⟶ T₁) (ι₂ : T₀ ⟶ T₂)
    (g₁ : T₁ ⟶ (relativeSpace f).obj (affineBase k A))
    (g₂ : T₂ ⟶ (relativeSpace f).obj (affineBase k B))
    (g₀ : T₀ ⟶ (relativeSpace f).obj (affineBase k C))
    (P₁ : IsPullback g₁ s₁ ((relativeSpace f).map (affineBaseMap p)) t)
    (P₂ : IsPullback g₂ s₂ ((relativeSpace f).map (affineBaseMap q)) t)
    (P₀ : IsPullback g₀ ι₁ ((relativeSpace f).map (affineBaseMap a)) g₁)
    (k₂ : ι₂ ≫ g₂ = g₀ ≫ (relativeSpace f).map (affineBaseMap b))
    (wT : ι₁ ≫ s₁ = ι₂ ≫ s₂) :
    IsPullback s₁.appTop s₂.appTop ι₁.appTop ι₂.appTop := by
  let π₀ := (relativeProjection f).app (affineBase k C)
  let π₁ := (relativeProjection f).app (affineBase k A)
  let π₂ := (relativeProjection f).app (affineBase k B)
  let : IsAffine (affineBase k R).left := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  let : IsAffine (affineBase k A).left := by
    change IsAffine (Spec (CommRingCat.of A))
    infer_instance
  let : IsAffine (affineBase k B).left := by
    change IsAffine (Spec (CommRingCat.of B))
    infer_instance
  let : IsAffine (affineBase k C).left := by
    change IsAffine (Spec (CommRingCat.of C))
    infer_instance
  have hΓ : IsPullback (Spec.map (CommRingCat.ofHom p.toRingHom)).appTop
      (Spec.map (CommRingCat.ofHom q.toRingHom)).appTop
      (Spec.map (CommRingCat.ofHom a.toRingHom)).appTop
      (Spec.map (CommRingCat.ofHom b.toRingHom)).appTop :=
    h.of_iso (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
      (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
      (Scheme.ΓSpecIso_inv_naturality _) (Scheme.ΓSpecIso_inv_naturality _)
      (Scheme.ΓSpecIso_inv_naturality _) (Scheme.ΓSpecIso_inv_naturality _)
  apply InfinitesimalAffineOpenSquare.affineCube_appTop_isPullback
    ι₁ ι₂ s₁ s₂
    (affineBaseMap a).left (affineBaseMap b).left
    (affineBaseMap p).left (affineBaseMap q).left
    (g₀ ≫ π₀) (g₁ ≫ π₁) (g₂ ≫ π₂) (baseProjection f t) hΓ
    (P₁.flip.paste_vert (relativeProjection_isPullback f (affineBaseMap p)))
    (P₂.flip.paste_vert (relativeProjection_isPullback f (affineBaseMap q)))
  · exact (P₀.paste_vert P₁).flip.paste_vert
      ((relativeProjection_isPullback f (affineBaseMap a)).paste_horiz
        (relativeProjection_isPullback f (affineBaseMap p)))
  · change ι₁ ≫ (g₁ ≫ π₁) = (g₀ ≫ π₀) ≫ (affineBaseMap a).left
    rw [← Category.assoc, ← P₀.w, Category.assoc,
      (relativeProjection f).naturality (affineBaseMap a), Category.assoc]
    rfl
  · change ι₂ ≫ (g₂ ≫ π₂) = (g₀ ≫ π₀) ≫ (affineBaseMap b).left
    rw [← Category.assoc, k₂, Category.assoc,
      (relativeProjection f).naturality (affineBaseMap b), Category.assoc]
    rfl
  · exact wT

end Langlands.AlgebraicGeometry.Picard.InfinitesimalCartesianCube
