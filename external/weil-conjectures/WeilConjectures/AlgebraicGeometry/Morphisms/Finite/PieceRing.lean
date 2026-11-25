/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitExists
public import WeilConjectures.Mathlib.RingTheory.Localization.Away.Idempotent
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineOpenAlgebra
public import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSection

/-!
# The ring of a piece of a split neighbourhood

For the split neighbourhood `Spec A'` of `y` given by an affine chart and a complete system of
orthogonal idempotents `e` of the ring `F` of `Spec A' ×_Y X`
(`AlgebraicGeometry.Scheme.Hom.Chart.split`), the `t`-th piece is the basic open of `e t`,
that is, `Spec` of the quotient `F ⧸ (1 - e t)` (`AlgebraicGeometry.Scheme.Hom.Chart.PieceRing`).
This ring is finite over `A'` and has a unique point over the point `φ'` of `A'`, namely the
one given by `(u, t)` (`AlgebraicGeometry.Scheme.Hom.Chart.piecePoint`).

For an étale `A'`-algebra `A''` with a point over `φ'`, the split neighbourhood pulled back to
`Spec A''` has `t`-th piece `Spec (A'' ⊗[A'] (F ⧸ (1 - e t)))`
(`AlgebraicGeometry.Scheme.Hom.Chart.pieceEmb`, `Chart.opensRange_pieceEmb`).

This is the dictionary through which the ring-theoretic section result
`Algebra.exists_etale_algHom_tensor_comp_eq` produces morphisms out of pieces.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct RingHom

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] affineAlgebra Chart.algebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

omit [IsFinite f] [IsAlgClosed Ω] in
/-- The image of an open under an isomorphism is the preimage under the inverse. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.image_hom_eq_preimage_inv {X Y : Scheme.{u}} (e : X ≅ Y)
    (U : X.Opens) : e.hom ''ᵁ U = e.inv ⁻¹ᵁ U := by
  conv_rhs => rw [← e.hom.preimage_image_eq U, ← Scheme.Hom.comp_preimage, e.inv_hom_id,
    Scheme.Hom.id_preimage]

namespace Chart

variable {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀) (hy : y default ∈ Y₀) {c : Nbhd y}
  (ch : Chart y Y₀ c) (A' : Type u) [CommRing A'] [Algebra ch.Ring A'] [Algebra.Etale ch.Ring A']
  (φ' : A' →+* Ω) (hφ' : φ'.comp (algebraMap ch.Ring A') = ch.point)
  [Fintype (PointsOver ch.point (ch.Fiber f))] [DecidableEq (PointsOver ch.point (ch.Fiber f))]
  (e : PointsOver ch.point (ch.Fiber f) → ch.RefineFiber f A')
  (he : CompleteOrthogonalIdempotents e)
  (hval : ∀ t t' : PointsOver ch.point (ch.Fiber f),
    t'.tensor hφ' (e t) = if t' = t then 1 else 0)
  (t : GeometricFiber f y)

/-- The idempotent of the ring of `Spec A' ×_Y X` cutting out the `t`-th piece. -/
abbrev pieceIdem : ch.RefineFiber f A' := e (ch.basePoint f hY₀ hy t)

/-- The ring of the `t`-th piece of the split neighbourhood: the quotient of the ring of
`Spec A' ×_Y X` by `1 - e t`. -/
abbrev PieceRing : Type u :=
  ch.RefineFiber f A' ⧸ Ideal.span {1 - ch.pieceIdem f hY₀ hy A' e t}

omit [Algebra.Etale ch.Ring A'] [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
include he in
theorem isLocalization_pieceRing :
    IsLocalization.Away (ch.pieceIdem f hY₀ hy A' e t) (ch.PieceRing f hY₀ hy A' e t) :=
  IsLocalization.Away.quotient_span_one_sub (he.idem _)

instance finite_pieceRing : Module.Finite A' (ch.PieceRing f hY₀ hy A' e t) :=
  have := ch.finite_fiber f hY₀
  have : Module.Finite A' (ch.RefineFiber f A') := Module.Finite.base_change _ _ _
  Module.Finite.quotient_span_one_sub A'

omit [Algebra.Etale ch.Ring A'] [Fintype (PointsOver ch.point (ch.Fiber f))]
  [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
/-- The idempotent `e t` becomes `1` in the ring of the `t`-th piece. -/
lemma algebraMap_pieceIdem :
    algebraMap (ch.RefineFiber f A') (ch.PieceRing f hY₀ hy A' e t)
      (ch.pieceIdem f hY₀ hy A' e t) = 1 := by
  rw [Ideal.Quotient.algebraMap_eq, ← sub_eq_zero,
    ← map_one (Ideal.Quotient.mk (Ideal.span {1 - ch.pieceIdem f hY₀ hy A' e t})), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨-1, by ring⟩

omit [Algebra.Etale ch.Ring A'] [Fintype (PointsOver ch.point (ch.Fiber f))] in
include hval in
lemma fiberPoint_pieceIdem :
    ch.fiberPoint f hY₀ hy A' φ' hφ' t (ch.pieceIdem f hY₀ hy A' e t) = 1 := by
  change (ch.basePoint f hY₀ hy t).tensor hφ' (e (ch.basePoint f hY₀ hy t)) = 1
  rw [hval, ite_eq_left rfl]

/-- The point of the ring of the `t`-th piece given by `(u, t)`. -/
def piecePoint : PointsOver φ' (ch.PieceRing f hY₀ hy A' e t) :=
  ⟨Ideal.Quotient.lift _ (ch.fiberPoint f hY₀ hy A' φ' hφ' t).1 (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_sub, map_one, ch.fiberPoint_pieceIdem f hY₀ hy A' φ' hφ' e hval t,
      sub_self, zero_mul]), by
    ext a
    exact (ch.fiberPoint f hY₀ hy A' φ' hφ' t).apply_algebraMap a⟩

omit [Algebra.Etale ch.Ring A'] [Fintype (PointsOver ch.point (ch.Fiber f))] in
lemma piecePoint_comp_algebraMap :
    (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t).1.comp
      (algebraMap (ch.RefineFiber f A') (ch.PieceRing f hY₀ hy A' e t)) =
      (ch.fiberPoint f hY₀ hy A' φ' hφ' t).1 :=
  RingHom.ext fun _ ↦ rfl

omit [Algebra.Etale ch.Ring A'] [Fintype (PointsOver ch.point (ch.Fiber f))] in
include hval in
/-- The ring of the `t`-th piece has a unique point over `φ'`. -/
theorem subsingleton_pointsOver_pieceRing :
    Subsingleton (PointsOver φ' (ch.PieceRing f hY₀ hy A' e t)) := by
  constructor
  intro ψ₁ ψ₂
  -- both restrict to points of `F` over `φ'` not vanishing at `e t`, hence to the point `(u, t)`
  have key : ∀ ψ : PointsOver φ' (ch.PieceRing f hY₀ hy A' e t),
      ψ.1.comp (algebraMap (ch.RefineFiber f A') (ch.PieceRing f hY₀ hy A' e t)) =
        (ch.fiberPoint f hY₀ hy A' φ' hφ' t).1 := by
    intro ψ
    obtain ⟨t', ht'⟩ := (PointsOver.tensorEquiv hφ').symm.surjective
      (ψ.restrictScalars (B := ch.RefineFiber f A') φ')
    rw [PointsOver.tensorEquiv_symm_apply] at ht'
    have h1 : (ψ.restrictScalars (B := ch.RefineFiber f A') φ')
        (ch.pieceIdem f hY₀ hy A' e t) = 1 := by
      rw [PointsOver.restrictScalars_apply, ch.algebraMap_pieceIdem f hY₀ hy A' e t, map_one]
    have h2 := hval (ch.basePoint f hY₀ hy t) t'
    rw [ht', h1] at h2
    split_ifs at h2 with h
    · subst h
      exact congrArg Subtype.val ht'.symm
    · exact absurd h2 one_ne_zero
  exact PointsOver.ext fun b ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact (RingHom.congr_fun (key ψ₁) b).trans (RingHom.congr_fun (key ψ₂) b).symm
section Spec

/-- The open immersion `Spec` of the ring of the `t`-th piece into `Spec` of the ring of
`Spec A' ×_Y X`. -/
def pieceSpecι : Spec (.of (ch.PieceRing f hY₀ hy A' e t)) ⟶ Spec (.of (ch.RefineFiber f A')) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

omit [Algebra.Etale ch.Ring A'] [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
include he in
theorem isOpenImmersion_pieceSpecι : IsOpenImmersion (ch.pieceSpecι f hY₀ hy A' e t) :=
  have := ch.isLocalization_pieceRing f hY₀ hy A' e he t
  IsOpenImmersion.of_isLocalization (ch.pieceIdem f hY₀ hy A' e t)

omit [Algebra.Etale ch.Ring A'] [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
include he in
theorem opensRange_pieceSpecι :
    haveI := ch.isOpenImmersion_pieceSpecι f hY₀ hy A' e he t
    (ch.pieceSpecι f hY₀ hy A' e t).opensRange =
      PrimeSpectrum.basicOpen (ch.pieceIdem f hY₀ hy A' e t) :=
  have := ch.isLocalization_pieceRing f hY₀ hy A' e he t
  opensRange_SpecMap_algebraMap (S := ch.PieceRing f hY₀ hy A' e t) _

include he in
/-- The `t`-th piece of the split neighbourhood `Spec A'` is the range of
`Spec (F ⧸ (1 - e t)) ⟶ Spec F ≅ Spec A' ×_Y X`. -/
lemma opensRange_pieceSpecι_comp_refineIso_hom :
    haveI := ch.isOpenImmersion_pieceSpecι f hY₀ hy A' e he t
    (ch.pieceSpecι f hY₀ hy A' e t ≫ (ch.refineIso f hY₀ A' φ' hφ').hom).opensRange =
      (ch.split f hY₀ hy A' φ' hφ' e he hval).piece t := by
  have := ch.isOpenImmersion_pieceSpecι f hY₀ hy A' e he t
  rw [split_piece, ← ch.opensRange_pieceSpecι f hY₀ hy A' e he t, Scheme.Hom.opensRange_comp,
    Scheme.Hom.image_hom_eq_preimage_inv]

/-- The structure morphism `Spec (F ⧸ (1 - e t)) ⟶ X` of the `t`-th piece. -/
def pieceSpecToX : Spec (.of (ch.PieceRing f hY₀ hy A' e t)) ⟶ X :=
  ch.pieceSpecι f hY₀ hy A' e t ≫ (ch.refineIso f hY₀ A' φ' hφ').hom ≫
    pullback.snd (ch.refine hY₀ A' φ' hφ').1.hom f

/-- The point `(u, t)` of `Spec (F ⧸ (1 - e t))`. -/
def pieceSpecPt : Spec (.of Ω) ⟶ Spec (.of (ch.PieceRing f hY₀ hy A' e t)) :=
  Spec.map (CommRingCat.ofHom (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t).1)

omit [Algebra.Etale ch.Ring A'] [Fintype (PointsOver ch.point (ch.Fiber f))] in
lemma pieceSpecPt_comp_pieceSpecι :
    ch.pieceSpecPt f hY₀ hy A' φ' hφ' e hval t ≫ ch.pieceSpecι f hY₀ hy A' e t =
      Spec.map (CommRingCat.ofHom (ch.fiberPoint f hY₀ hy A' φ' hφ' t).1) := by
  rw [pieceSpecPt, pieceSpecι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun r ↦ Spec.map (CommRingCat.ofHom r))
    (ch.piecePoint_comp_algebraMap f hY₀ hy A' φ' hφ' e hval t)

omit [Fintype (PointsOver ch.point (ch.Fiber f))] in
/-- The point `(u, t)` of the `t`-th piece lies over the geometric point `t` of `X`. -/
@[reassoc (attr := simp)]
lemma pieceSpecPt_comp_pieceSpecToX :
    ch.pieceSpecPt f hY₀ hy A' φ' hφ' e hval t ≫ ch.pieceSpecToX f hY₀ hy A' φ' hφ' e t =
      t.1 := by
  rw [pieceSpecToX, ← Category.assoc, pieceSpecPt_comp_pieceSpecι, ← Category.assoc,
    ← ch.basePt_refine f hY₀ hy A' φ' hφ' t, basePt_snd]

end Spec
section Refine₂

/-!
### Pulling back along a further étale algebra

For an étale `A'`-algebra `A''` with a point `φ''` over `φ'`, `Spec A''` is a pointed étale
neighbourhood of `y` refining `Spec A'`, and the `t`-th piece of the pulled back split
neighbourhood is `Spec (A'' ⊗[A'] (F ⧸ (1 - e t)))`.
-/

variable (A'' : Type u) [CommRing A''] [Algebra A' A''] [Algebra.Etale A' A'']
  (φ'' : A'' →+* Ω) (hφ'' : φ''.comp (algebraMap A' A'') = φ')

/-- `Spec A''`, pointed by `φ''`, as a pointed étale neighbourhood of `y`. -/
def refine₂ : Nbhd y :=
  have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap A' A''))) :=
    HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  Functor.elementsMk _ (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap A' A'')) ≫
    (ch.refine hY₀ A' φ' hφ').1.hom)) (CategoryTheory.Over.homMk
    (Spec.map (CommRingCat.ofHom φ'')) (by
      change Spec.map (CommRingCat.ofHom φ'') ≫ Spec.map (CommRingCat.ofHom (algebraMap A' A'')) ≫
        (ch.refine hY₀ A' φ' hφ').1.hom = y
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ'']
      exact CategoryTheory.Over.w (ch.refine hY₀ A' φ' hφ').2))

@[simp]
lemma refine₂_fst_hom : (ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'').1.hom =
    Spec.map (CommRingCat.ofHom (algebraMap A' A'')) ≫ (ch.refine hY₀ A' φ' hφ').1.hom := rfl

@[simp]
lemma refine₂_snd_left :
    (ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'').2.left = Spec.map (CommRingCat.ofHom φ'') := rfl

/-- The refinement `Spec A'' ⟶ Spec A'` of pointed étale neighbourhoods. -/
def refine₂Map : ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'' ⟶ ch.refine hY₀ A' φ' hφ' :=
  Functor.Elements.homMk
    (MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A' A''))) rfl)
    (CategoryTheory.Over.OverMorphism.ext (by
      change Spec.map (CommRingCat.ofHom φ'') ≫ Spec.map (CommRingCat.ofHom (algebraMap A' A'')) =
        Spec.map (CommRingCat.ofHom φ')
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ'']))

@[simp]
lemma refine₂Map_val_left : (ch.refine₂Map hY₀ A' φ' hφ' A'' φ'' hφ'').val.left =
    Spec.map (CommRingCat.ofHom (algebraMap A' A'')) := rfl

omit [Fintype (PointsOver ch.point (ch.Fiber f))]
  [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
/-- `Spec (A'' ⊗[A'] F)` is the fibre product `Spec A'' ×_Y X`. -/
lemma isPullback_refine₂ :
    IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := A') (A := A'') (B := ch.RefineFiber f A'))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A')
        (A := A'') (B := ch.RefineFiber f A')).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ch.Ring)
          (A := A') (B := ch.Fiber f)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Γ(Y, Y₀))
          (A := ch.Ring) (B := Γ(X, f ⁻¹ᵁ Y₀))).toRingHom) ≫ (hY₀.preimage f).fromSpec)
      (ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'').1.hom f :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A' A'' (ch.RefineFiber f A'))).paste_vert
    (ch.isPullback_refine f hY₀ A' φ' hφ')

/-- The isomorphism `Spec (A'' ⊗[A'] F) ≅ Spec A'' ×_Y X`. -/
def refine₂Iso :
    Spec (.of (A'' ⊗[A'] ch.RefineFiber f A')) ≅
      pullback (ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'').1.hom f :=
  (ch.isPullback_refine₂ f hY₀ A' φ' hφ' A'' φ'' hφ'').isoPullback

omit [Fintype (PointsOver ch.point (ch.Fiber f))]
  [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
/-- The base change `Spec A'' ×_Y X ⟶ Spec A' ×_Y X` is `Spec` of `F ⟶ A'' ⊗[A'] F`. -/
lemma refine₂Iso_hom_comp_etale_map_left :
    (ch.refine₂Iso f hY₀ A' φ' hφ' A'' φ'' hφ'').hom ≫
      (f.Etale.map (ch.refine₂Map hY₀ A' φ' hφ' A'' φ'' hφ'').val).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A')
        (A := A'') (B := ch.RefineFiber f A')).toRingHom) ≫ (ch.refineIso f hY₀ A' φ' hφ').hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Hom.etale_map_left_comp_fst, refine₂Iso, ← Category.assoc,
      IsPullback.isoPullback_hom_fst, Category.assoc, refineIso, IsPullback.isoPullback_hom_fst,
      refine₂Map_val_left, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply,
      Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
    rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
    congr 1
  · rw [Category.assoc, Hom.etale_map_left_comp_snd, refine₂Iso, IsPullback.isoPullback_hom_snd,
      Category.assoc, refineIso, IsPullback.isoPullback_hom_snd]
/-- The ring of the `t`-th piece of the split neighbourhood pulled back to `Spec A''`. -/
abbrev PieceRing₂ : Type u := A'' ⊗[A'] ch.PieceRing f hY₀ hy A' e t

/-- The ring of the pulled back piece as an algebra over the ring of `Spec A'' ×_Y X`. -/
@[instance_reducible]
def pieceRing₂Algebra :
    Algebra (A'' ⊗[A'] ch.RefineFiber f A') (ch.PieceRing₂ f hY₀ hy A' e t A'') :=
  IsLocalization.Away.tensorQuotientAlgebra

attribute [local instance] pieceRing₂Algebra

omit [Algebra.Etale ch.Ring A'] [DecidableEq (PointsOver ch.point (ch.Fiber f))]
  [Algebra.Etale A' A''] in
include he in
theorem isLocalization_pieceRing₂ :
    IsLocalization.Away (Algebra.TensorProduct.includeRight (ch.pieceIdem f hY₀ hy A' e t) :
      A'' ⊗[A'] ch.RefineFiber f A') (ch.PieceRing₂ f hY₀ hy A' e t A'') :=
  IsLocalization.Away.tensor_quotient_span_one_sub (he.idem _)

/-- The open immersion `Spec (A'' ⊗ (F ⧸ (1 - e t))) ⟶ Spec (A'' ⊗ F)`. -/
def pieceSpec₂ι :
    Spec (.of (ch.PieceRing₂ f hY₀ hy A' e t A'')) ⟶ Spec (.of (A'' ⊗[A'] ch.RefineFiber f A')) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

omit [Algebra.Etale ch.Ring A'] [DecidableEq (PointsOver ch.point (ch.Fiber f))]
  [Algebra.Etale A' A''] in
include he in
theorem isOpenImmersion_pieceSpec₂ι : IsOpenImmersion (ch.pieceSpec₂ι f hY₀ hy A' e t A'') :=
  have := ch.isLocalization_pieceRing₂ f hY₀ hy A' e he t A''
  IsOpenImmersion.of_isLocalization
    (Algebra.TensorProduct.includeRight (ch.pieceIdem f hY₀ hy A' e t) :
      A'' ⊗[A'] ch.RefineFiber f A')

omit [Algebra.Etale ch.Ring A'] [DecidableEq (PointsOver ch.point (ch.Fiber f))]
  [Algebra.Etale A' A''] in
include he in
theorem opensRange_pieceSpec₂ι :
    haveI := ch.isOpenImmersion_pieceSpec₂ι f hY₀ hy A' e he t A''
    (ch.pieceSpec₂ι f hY₀ hy A' e t A'').opensRange =
      PrimeSpectrum.basicOpen (Algebra.TensorProduct.includeRight
        (ch.pieceIdem f hY₀ hy A' e t) : A'' ⊗[A'] ch.RefineFiber f A') :=
  have := ch.isLocalization_pieceRing₂ f hY₀ hy A' e he t A''
  opensRange_SpecMap_algebraMap (S := ch.PieceRing₂ f hY₀ hy A' e t A'') _

/-- The embedding of `Spec (A'' ⊗ (F ⧸ (1 - e t)))` into `Spec A'' ×_Y X`, as the `t`-th piece
of the pulled back split neighbourhood. -/
def pieceEmb : Spec (.of (ch.PieceRing₂ f hY₀ hy A' e t A'')) ⟶
    pullback (ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'').1.hom f :=
  ch.pieceSpec₂ι f hY₀ hy A' e t A'' ≫ (ch.refine₂Iso f hY₀ A' φ' hφ' A'' φ'' hφ'').hom

omit [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
include he in
theorem isOpenImmersion_pieceEmb :
    IsOpenImmersion (ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'') :=
  have := ch.isOpenImmersion_pieceSpec₂ι f hY₀ hy A' e he t A''
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

set_option backward.isDefEq.respectTransparency.types false in
include he in
/-- The range of `pieceEmb` is the `t`-th piece of the pulled back split neighbourhood. -/
lemma opensRange_pieceEmb :
    haveI := ch.isOpenImmersion_pieceEmb f hY₀ hy A' φ' hφ' e he t A'' φ'' hφ''
    (ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'').opensRange =
      ((ch.split f hY₀ hy A' φ' hφ' e he hval).pullbackDec
        (ch.refine₂Map hY₀ A' φ' hφ' A'' φ'' hφ'')).piece t := by
  have := ch.isOpenImmersion_pieceSpec₂ι f hY₀ hy A' e he t A''
  have key : (f.Etale.map (ch.refine₂Map hY₀ A' φ' hφ' A'' φ'' hφ'').val).left ≫
      (ch.refineIso f hY₀ A' φ' hφ').inv =
      (ch.refine₂Iso f hY₀ A' φ' hφ' A'' φ'' hφ'').inv ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A')
          (A := A'') (B := ch.RefineFiber f A')).toRingHom) := by
    rw [Iso.eq_inv_comp, ← Category.assoc]
    exact (congrArg (· ≫ (ch.refineIso f hY₀ A' φ' hφ').inv)
      (ch.refine₂Iso_hom_comp_etale_map_left f hY₀ A' φ' hφ' A'' φ'' hφ'')).trans
      (by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  change (ch.pieceSpec₂ι f hY₀ hy A' e t A'' ≫
    (ch.refine₂Iso f hY₀ A' φ' hφ' A'' φ'' hφ'').hom).opensRange = _
  rw [SplitNbhd.pullbackDec_piece, split_piece, Scheme.Hom.opensRange_comp,
    Scheme.Hom.image_hom_eq_preimage_inv, ch.opensRange_pieceSpec₂ι f hY₀ hy A' e he t A'',
    ← Scheme.Hom.comp_preimage, key, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
  rfl

omit [Fintype (PointsOver ch.point (ch.Fiber f))]
  [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
@[reassoc]
lemma pieceEmb_comp_fst :
    ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'' ≫ pullback.fst _ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A') (A := A'')
        (B := ch.PieceRing f hY₀ hy A' e t))) := by
  rw [pieceEmb, Category.assoc, refine₂Iso, IsPullback.isoPullback_hom_fst, pieceSpec₂ι,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

omit [Fintype (PointsOver ch.point (ch.Fiber f))]
  [DecidableEq (PointsOver ch.point (ch.Fiber f))] in
@[reassoc]
lemma pieceEmb_comp_snd :
    ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'' ≫ pullback.snd _ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A') (A := A'')
        (B := ch.PieceRing f hY₀ hy A' e t)).toRingHom) ≫
        ch.pieceSpecToX f hY₀ hy A' φ' hφ' e t := by
  have h : ch.pieceSpec₂ι f hY₀ hy A' e t A'' ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A')
        (A := A'') (B := ch.RefineFiber f A')).toRingHom) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A') (A := A'')
        (B := ch.PieceRing f hY₀ hy A' e t)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ch.RefineFiber f A')
          (ch.PieceRing f hY₀ hy A' e t))) := by
    rw [pieceSpec₂ι, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun r ↦ Spec.map (CommRingCat.ofHom r)) (RingHom.ext fun a ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply,
        RingHom.algebraMap_toAlgebra]
      change Algebra.TensorProduct.map (AlgHom.id A' A'') (Ideal.Quotient.mkₐ A' _) _ = _
      rw [Algebra.TensorProduct.map_tmul]
      rfl)
  rw [pieceEmb, Category.assoc, refine₂Iso, IsPullback.isoPullback_hom_snd, pieceSpecToX,
    pieceSpecι, refineIso]
  slice_rhs 3 4 => rw [IsPullback.isoPullback_hom_snd]
  slice_lhs 1 2 => rw [h]
  simp only [Category.assoc]

/-- The point `(u, t)` of the pulled back piece. -/
def piecePoint₂ : PointsOver φ'' (ch.PieceRing₂ f hY₀ hy A' e t A'') :=
  PointsOver.tensor (A' := A'') (B := ch.PieceRing f hY₀ hy A' e t) hφ''
    (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t)

omit [Fintype (PointsOver ch.point (ch.Fiber f))] in
/-- The point `(u, t)` of `Spec A'' ×_Y X` is `Spec` of `piecePoint₂`. -/
lemma SpecMap_piecePoint₂_comp_pieceEmb :
    Spec.map (CommRingCat.ofHom (ch.piecePoint₂ f hY₀ hy A' φ' hφ' e hval t A'' φ'' hφ'').1) ≫
      ch.pieceEmb f hY₀ hy A' φ' hφ' e t A'' φ'' hφ'' =
      basePt f (ch.refine₂ hY₀ A' φ' hφ' A'' φ'' hφ'') t := by
  apply pullback.hom_ext
  · rw [Category.assoc, pieceEmb_comp_fst, basePt_fst, refine₂_snd_left, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun r ↦ Spec.map (CommRingCat.ofHom r))
      (ch.piecePoint₂ f hY₀ hy A' φ' hφ' e hval t A'' φ'' hφ'').comp_algebraMap
  · rw [Category.assoc, pieceEmb_comp_snd, basePt_snd, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← ch.pieceSpecPt_comp_pieceSpecToX f hY₀ hy A' φ' hφ' e hval t,
      pieceSpecPt]
    congr 3
    exact PointsOver.tensor_comp_includeRight hφ'' (ch.piecePoint f hY₀ hy A' φ' hφ' e hval t)

end Refine₂

end Chart

end AlgebraicGeometry.Scheme.Hom

end
