import Langlands.AlgebraicGeometry.Picard.FieldPicardInfinitesimalGluingProof

/-! # Infinitesimal gluing for actual Picard groupoids over a flat base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.FlatInfinitesimalGluing

open SquareGluingDescent CubeMap InfinitesimalAffineOpenSquare

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Flat f]

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
/-- Every cartesian cube over an affine open immersion into the base change of a
flat scheme has the actual ring pullback of global sections. -/
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

omit [Flat f] in
/-- The actual base change of an affine ring square. -/
@[simps]
def affineSq : Sq.{u} where
  X₀ := (relativeSpace f).obj (affineBase k C)
  X₁ := (relativeSpace f).obj (affineBase k A)
  X₂ := (relativeSpace f).obj (affineBase k B)
  X := (relativeSpace f).obj (affineBase k R)
  i₁ := (relativeSpace f).map (affineBaseMap a)
  i₂ := (relativeSpace f).map (affineBaseMap b)
  j₁ := (relativeSpace f).map (affineBaseMap p)
  j₂ := (relativeSpace f).map (affineBaseMap q)
  w := PicardGroupoid.relativeSquare_comm f _ _ _ _ (PicardGroupoid.affineSquare_comm p q a b h)

omit [Flat f] in
/-- The comparison functor of the base-changed square is the published affine
comparison. -/
lemma affineSq_C :
    (affineSq f p q a b h).C = PicardGroupoid.affineSquareComparison f p q a b h := rfl

/-- Every cartesian open cube into the base-changed square has ring pullbacks of
global sections over all affine opens of its total scheme. -/
lemma affineRestrictedCubes {T : Sq.{u}} (c : CubeMap (affineSq f p q a b h) T) (hc : c.Cart)
    [IsOpenImmersion c.t] :
    SquareGluingFullyFaithful.AffineRestrictedCubes T.i₁ T.i₂ T.j₁ T.j₂ := by
  intro U hU
  have : IsAffine U.toScheme := hU
  have hc' := (T.cart_restrictC U).comp hc
  refine ⟨(T.i₁ ≫ T.j₁) ⁻¹ᵁ U, leftRestriction T.i₁ T.j₁ U,
    rightRestriction T.i₁ T.i₂ T.j₁ T.j₂ T.w U, ((T.i₁ ≫ T.j₁) ⁻¹ᵁ U).ι,
    leftRestriction_ι T.i₁ T.j₁ U, rightRestriction_ι T.i₁ T.i₂ T.j₁ T.j₂ T.w U, ?_⟩
  exact cartesianCube_appTop_isPullback f p q a b h
    (U.ι ≫ c.t) (T.j₁ ∣_ U) (T.j₂ ∣_ U) (leftRestriction T.i₁ T.j₁ U)
    (rightRestriction T.i₁ T.i₂ T.j₁ T.j₂ T.w U)
    ((T.j₁ ⁻¹ᵁ U).ι ≫ c.g₁) ((T.j₂ ⁻¹ᵁ U).ι ≫ c.g₂) (((T.i₁ ≫ T.j₁) ⁻¹ᵁ U).ι ≫ c.g₀)
    hc'.1 hc'.2.1 hc'.2.2 (comp (T.restrictC U) c).k₂ (T.restrict U).w

/-- The comparison is full and faithful on every cartesian open cube into the
base-changed square. -/
lemma ffOnCart : FFOnCart (affineSq f p q a b h) := by
  intro T c hc hct
  have hR := affineRestrictedCubes f p q a b h c hc
  have hcov : SquareGluingFullyFaithful.CommonAffineTrivializingCovers T.X :=
    fun L L' ↦ LineBundle.exists_commonAffineTrivializingCover L L'
  exact ⟨SquareGluingFullyFaithful.full _ _ _ _ T.w hR hcov,
    SquareGluingFullyFaithful.faithful _ _ _ _ T.w hR hcov⟩

/-- Every actual gluing datum on the base-changed square is realized by an actual
line bundle. -/
lemma essSurj (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    (affineSq f p q a b h).C.EssSurj := by
  constructor
  intro D
  have E := fun x : (affineSq f p q a b h).X ↦
    InfinitesimalLocalEffectivity.affineSquareNeighborhood f p q a b h hb hn D ⊤ x
      (TopologicalSpace.Opens.mem_top x)
  exact (affineSq f p q a b h).exists_iso_of_effective (fun x ↦ (E x).opens)
    (fun x ↦ (E x).mem) (ffOnCart f p q a b h) (fun x ↦ (E x).effective)

/-- Over a flat scheme, the published affine comparison is an equivalence for every
ring pullback square one of whose maps is surjective with nilpotent kernel. -/
theorem affineSquareComparison_isEquivalence (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    (PicardGroupoid.affineSquareComparison f p q a b h).IsEquivalence := by
  have hS := ffOnCart f p q a b h _ (idC _) (cart_idC _)
    (inferInstanceAs (IsOpenImmersion (𝟙 _)))
  exact { faithful := hS.2, full := hS.1, essSurj := essSurj f p q a b h hb hn }

/-- The flat-base gluing equivalence: actual line bundles on `X_R` are equivalent,
through the published affine comparison functor, to actual gluing data on `X_A` and
`X_B` over `X_C`. -/
def affineSquareGluingEquivalence (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    PicardGroupoid ((relativeSpace f).obj (affineBase k R)) ≌
      PicardGroupoid.SquareGluingData ((relativeSpace f).map (affineBaseMap a))
        ((relativeSpace f).map (affineBaseMap b)) :=
  have := affineSquareComparison_isEquivalence f p q a b h hb hn
  (PicardGroupoid.affineSquareComparison f p q a b h).asEquivalence

/-- The functor of the gluing equivalence is the published affine comparison. -/
lemma affineSquareGluingEquivalence_functor (hb : Function.Surjective b)
    (hn : IsNilpotent (RingHom.ker b.toRingHom)) :
    (affineSquareGluingEquivalence f p q a b h hb hn).functor =
      PicardGroupoid.affineSquareComparison f p q a b h := rfl

end Langlands.AlgebraicGeometry.Picard.FlatInfinitesimalGluing
