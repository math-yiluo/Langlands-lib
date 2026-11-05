import Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineSquareSections

/-! # Sections of the actual square on arbitrary affine opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenSquare

/-- Flat base change of a ring pullback, with all maps supplied as actual ring maps. -/
lemma isPullback_of_flat_pushouts
    {R A B C S A' B' C' : CommRingCat.{u}}
    (p : R ⟶ A) (q : R ⟶ B) (a : A ⟶ C) (b : B ⟶ C)
    (h : IsPullback p q a b)
    (s : R ⟶ S) (hs : s.hom.Flat)
    (p' : S ⟶ A') (q' : S ⟶ B') (a' : A' ⟶ C') (b' : B' ⟶ C')
    (rA : A ⟶ A') (rB : B ⟶ B') (rC : C ⟶ C')
    (hA : IsPushout s p p' rA)
    (hB : IsPushout s q q' rB)
    (hC : IsPushout s (p ≫ a) (p' ≫ a') rC)
    (wa : rA ≫ a' = a ≫ rC) (wb : rB ≫ b' = b ≫ rC)
    (w : p' ≫ a' = q' ≫ b') :
    IsPullback p' q' a' b' := by
  let : Algebra R S := s.hom.toAlgebra
  let : Algebra R A := p.hom.toAlgebra
  let : Algebra R B := q.hom.toAlgebra
  let : Algebra R C := (p ≫ a).hom.toAlgebra
  let : Module.Flat R S := hs
  let pa : R →ₐ[R] A := { __ := p.hom, commutes' := fun _ ↦ rfl }
  let qa : R →ₐ[R] B := { __ := q.hom, commutes' := fun _ ↦ rfl }
  let aa : A →ₐ[R] C := { __ := a.hom, commutes' := fun _ ↦ rfl }
  let ba : B →ₐ[R] C :=
    { __ := b.hom, commutes' := fun r ↦ (ConcreteCategory.congr_hom h.w r).symm }
  exact InfinitesimalAffineSquareSections.isPullback_of_pushouts pa qa aa ba h
    p' q' a' b' (𝟙 _) s p' rA q' rB (p' ≫ a') rC
    IsPushout.of_id_snd hA hB hC
    (by simp) (by exact hA.w) (by simp) (by exact hB.w)
    rfl wa w.symm wb

section Cube

variable {Z₀ Z₁ Z₂ Z Y₀ Y₁ Y₂ Y : Scheme.{u}}
  [IsAffine Z₀] [IsAffine Z₁] [IsAffine Z₂] [IsAffine Z]
  [IsAffine Y]

/-- The actual sections square in an affine cartesian cube with flat total projection. -/
lemma affineCube_appTop_isPullback
    (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
    (a : Z₀ ⟶ Z₁) (b : Z₀ ⟶ Z₂) (p : Z₁ ⟶ Z) (q : Z₂ ⟶ Z)
    (π₀ : Y₀ ⟶ Z₀) (π₁ : Y₁ ⟶ Z₁) (π₂ : Y₂ ⟶ Z₂) (π : Y ⟶ Z)
    [Flat π]
    (h : IsPullback p.appTop q.appTop a.appTop b.appTop)
    (hA : IsPullback j₁ π₁ π p) (hB : IsPullback j₂ π₂ π q)
    (hC : IsPullback (i₁ ≫ j₁) π₀ π (a ≫ p))
    (wa : i₁ ≫ π₁ = π₀ ≫ a) (wb : i₂ ≫ π₂ = π₀ ≫ b)
    (w : i₁ ≫ j₁ = i₂ ≫ j₂) :
    IsPullback j₁.appTop j₂.appTop i₁.appTop i₂.appTop := by
  apply isPullback_of_flat_pushouts p.appTop q.appTop a.appTop b.appTop h
    π.appTop π.flat_appTop j₁.appTop j₂.appTop i₁.appTop i₂.appTop
    π₁.appTop π₂.appTop π₀.appTop
    (isPushout_appTop_of_isPullback hA) (isPushout_appTop_of_isPullback hB)
  · simpa only [Scheme.Hom.comp_appTop] using isPushout_appTop_of_isPullback hC
  · simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop wa
  · simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop wb
  · simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop w

end Cube

section Restrict

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}

/-- The first induced morphism on the common inverse image of an open. -/
def leftRestriction (i₁ : Y₀ ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (U : Y.Opens) :
    ((i₁ ≫ j₁) ⁻¹ᵁ U).toScheme ⟶ (j₁ ⁻¹ᵁ U).toScheme :=
  i₁.resLE (j₁ ⁻¹ᵁ U) ((i₁ ≫ j₁) ⁻¹ᵁ U) (by
    rw [Scheme.Hom.comp_preimage])

/-- The second induced morphism, using the equality of the two square composites. -/
def rightRestriction (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (w : i₁ ≫ j₁ = i₂ ≫ j₂) (U : Y.Opens) :
    ((i₁ ≫ j₁) ⁻¹ᵁ U).toScheme ⟶ (j₂ ⁻¹ᵁ U).toScheme :=
  i₂.resLE (j₂ ⁻¹ᵁ U) ((i₁ ≫ j₁) ⁻¹ᵁ U) (by
    rw [w, Scheme.Hom.comp_preimage])

@[reassoc (attr := simp)]
lemma leftRestriction_ι (i₁ : Y₀ ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (U : Y.Opens) :
    leftRestriction i₁ j₁ U ≫ (j₁ ⁻¹ᵁ U).ι = ((i₁ ≫ j₁) ⁻¹ᵁ U).ι ≫ i₁ :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma rightRestriction_ι (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (w : i₁ ≫ j₁ = i₂ ≫ j₂) (U : Y.Opens) :
    rightRestriction i₁ i₂ j₁ j₂ w U ≫ (j₂ ⁻¹ᵁ U).ι =
      ((i₁ ≫ j₁) ⁻¹ᵁ U).ι ≫ i₂ :=
  Scheme.Hom.resLE_comp_ι _ _

lemma restriction_comm (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (w : i₁ ≫ j₁ = i₂ ≫ j₂) (U : Y.Opens) :
    leftRestriction i₁ j₁ U ≫ (j₁ ∣_ U) =
      rightRestriction i₁ i₂ j₁ j₂ w U ≫ (j₂ ∣_ U) := by
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι, leftRestriction_ι_assoc,
    rightRestriction_ι_assoc]
  rw [w]

/-- Restricting an affine cartesian cube to any affine open retains the ring pullback. -/
lemma restricted_appTop_isPullback
    {Z₀ Z₁ Z₂ Z : Scheme.{u}}
    [IsAffine Z₀] [IsAffine Z₁] [IsAffine Z₂] [IsAffine Z]
    (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
    [IsAffineHom i₁] [IsAffineHom j₁] [IsAffineHom j₂]
    (a : Z₀ ⟶ Z₁) (b : Z₀ ⟶ Z₂) (p : Z₁ ⟶ Z) (q : Z₂ ⟶ Z)
    (π₀ : Y₀ ⟶ Z₀) (π₁ : Y₁ ⟶ Z₁) (π₂ : Y₂ ⟶ Z₂) (π : Y ⟶ Z)
    [Flat π]
    (h : IsPullback p.appTop q.appTop a.appTop b.appTop)
    (hA : IsPullback j₁ π₁ π p) (hB : IsPullback j₂ π₂ π q)
    (hC : IsPullback (i₁ ≫ j₁) π₀ π (a ≫ p))
    (wa : i₁ ≫ π₁ = π₀ ≫ a) (wb : i₂ ≫ π₂ = π₀ ≫ b)
    (w : i₁ ≫ j₁ = i₂ ≫ j₂) (U : Y.Opens) (hU : IsAffineOpen U) :
    IsPullback (j₁ ∣_ U).appTop (j₂ ∣_ U).appTop
      (leftRestriction i₁ j₁ U).appTop (rightRestriction i₁ i₂ j₁ j₂ w U).appTop := by
  let : IsAffine U.toScheme := hU
  have hcomp : leftRestriction i₁ j₁ U ≫ (j₁ ∣_ U) = (i₁ ≫ j₁) ∣_ U := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, morphismRestrict_ι, leftRestriction_ι_assoc]
  apply affineCube_appTop_isPullback
    (leftRestriction i₁ j₁ U) (rightRestriction i₁ i₂ j₁ j₂ w U) (j₁ ∣_ U) (j₂ ∣_ U)
    a b p q (((i₁ ≫ j₁) ⁻¹ᵁ U).ι ≫ π₀) ((j₁ ⁻¹ᵁ U).ι ≫ π₁)
    ((j₂ ⁻¹ᵁ U).ι ≫ π₂) (U.ι ≫ π) h
    ((isPullback_morphismRestrict j₁ U).paste_vert hA)
    ((isPullback_morphismRestrict j₂ U).paste_vert hB)
  · rw [hcomp]
    exact (isPullback_morphismRestrict (i₁ ≫ j₁) U).paste_vert hC
  · simp only [Category.assoc, leftRestriction_ι_assoc]
    rw [wa]
  · simp only [Category.assoc, rightRestriction_ι_assoc]
    rw [wb]
  · exact restriction_comm i₁ i₂ j₁ j₂ w U

end Restrict

section Relative

variable {k R A B C : Type u} [Field k] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
  (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))

/-- On every affine open of the actual relative square, actual sections form a pullback. -/
lemma appTop_isPullback
    (U : ((relativeSpace f).obj (affineBase k R)).Opens) (hU : IsAffineOpen U) :
    let i₁ := (relativeSpace f).map (affineBaseMap a)
    let i₂ := (relativeSpace f).map (affineBaseMap b)
    let j₁ := (relativeSpace f).map (affineBaseMap p)
    let j₂ := (relativeSpace f).map (affineBaseMap q)
    let w := PicardGroupoid.relativeSquare_comm f
      (affineBaseMap a) (affineBaseMap b) (affineBaseMap p) (affineBaseMap q)
      (PicardGroupoid.affineSquare_comm p q a b h)
    IsPullback (j₁ ∣_ U).appTop (j₂ ∣_ U).appTop
      (leftRestriction i₁ j₁ U).appTop (rightRestriction i₁ i₂ j₁ j₂ w U).appTop := by
  dsimp only
  let π₀ := (relativeProjection f).app (affineBase k C)
  let π₁ := (relativeProjection f).app (affineBase k A)
  let π₂ := (relativeProjection f).app (affineBase k B)
  let π := (relativeProjection f).app (affineBase k R)
  let : Flat π := by
    dsimp [π, relativeProjection]
    infer_instance
  let : IsAffineHom (affineBaseMap a).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom a.toRingHom))
    infer_instance
  let : IsAffineHom (affineBaseMap p).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom p.toRingHom))
    infer_instance
  let : IsAffineHom (affineBaseMap q).left := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom q.toRingHom))
    infer_instance
  let := relativeSpace_map_isAffineHom f (affineBaseMap a)
  let := relativeSpace_map_isAffineHom f (affineBaseMap p)
  let := relativeSpace_map_isAffineHom f (affineBaseMap q)
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
  exact restricted_appTop_isPullback _ _ _ _
    (affineBaseMap a).left (affineBaseMap b).left
    (affineBaseMap p).left (affineBaseMap q).left π₀ π₁ π₂ π hΓ
    (relativeProjection_isPullback f (affineBaseMap p))
    (relativeProjection_isPullback f (affineBaseMap q))
    ((relativeProjection_isPullback f (affineBaseMap a)).paste_horiz
      (relativeProjection_isPullback f (affineBaseMap p)))
    ((relativeProjection f).naturality (affineBaseMap a))
    ((relativeProjection f).naturality (affineBaseMap b))
    _ U hU

end Relative

end Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenSquare
