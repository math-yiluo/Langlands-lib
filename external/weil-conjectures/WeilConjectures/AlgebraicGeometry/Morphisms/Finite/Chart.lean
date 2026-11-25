/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitNeighborhood

/-!
# Affine charts of pointed étale neighbourhoods, for a finite morphism

Let `f : X ⟶ Y` be a finite morphism, `y : Spec Ω ⟶ Y` a geometric point lying in an affine
open `Y₀ = Spec R`, and `(U, u)` a pointed étale neighbourhood of `y`. An *affine chart* of
`(U, u)` is an affine open `U₁ = Spec R'` of `U` containing `u` and mapping into `Y₀`. In such a
chart, `R'` is an étale `R`-algebra with a point `R' →+* Ω` over the point of `R` given by `y`,
and the base change `U₁ ×_Y X` is `Spec (R' ⊗[R] S)`, where `S = Γ(X, f ⁻¹ᵁ Y₀)` is finite over
`R`. More generally, for an étale `R'`-algebra `A'` with a point over the point of `R'`, the
étale `Y`-scheme `Spec A'` is a pointed étale neighbourhood of `y` refining `(U, u)`
(`AlgebraicGeometry.Scheme.Hom.Chart.nbhd`), and `Spec A' ×_Y X` is `Spec (A' ⊗[R'] (R' ⊗[R] S))`
(`AlgebraicGeometry.Scheme.Hom.Chart.isPullback`), compatibly with the geometric points `(u, t)`
(`AlgebraicGeometry.Scheme.Hom.Chart.basePt_nbhd`).

This is the dictionary through which the ring-theoretic results of
`WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting` and `FiniteSection` are transported
to the small étale sites.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct RingHom

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀) (hy : y default ∈ Y₀)

variable (Y₀) in
/-- An affine chart of a pointed étale neighbourhood `(U, u)` of `y`: an affine open `U₁` of `U`
containing the marked point and mapping into the affine open `Y₀` of `Y`. -/
structure Chart (c : Nbhd y) where
  /-- The affine open of `U`. -/
  U₁ : c.1.left.Opens
  isAffineOpen : IsAffineOpen U₁
  mem : c.2.left (default : Spec (.of Ω)) ∈ U₁
  le : U₁ ≤ c.1.hom ⁻¹ᵁ Y₀

include hy in
/-- Every pointed étale neighbourhood has an affine chart. -/
lemma Chart.nonempty (c : Nbhd y) : Nonempty (Chart y Y₀ c) := by
  obtain ⟨U₁, hU₁, hu, hle⟩ := exists_isAffineOpen_mem_and_subset (X := c.1.left)
    (x := c.2.left (default : Spec (.of Ω))) (U := c.1.hom ⁻¹ᵁ Y₀) (by
      have : c.2.left ≫ c.1.hom = y := CategoryTheory.Over.w c.2
      change (c.2.left ≫ c.1.hom) (default : Spec (.of Ω)) ∈ Y₀
      rw [this]
      exact hy)
  exact ⟨⟨U₁, hU₁, hu, hle⟩⟩

namespace Chart

variable {y} {c : Nbhd y} (ch : Chart y Y₀ c)

attribute [local instance] affineAlgebra

/-- The ring of the chart, `Γ(U, U₁)`. -/
abbrev Ring : CommRingCat.{u} := Γ(c.1.left, ch.U₁)

/-- The structure map `Γ(Y, Y₀) ⟶ Γ(U, U₁)` of the chart. -/
def map : Γ(Y, Y₀) ⟶ ch.Ring := c.1.hom.appLE Y₀ ch.U₁ ch.le

/-- The `Γ(Y, Y₀)`-algebra structure on the ring of the chart. -/
@[instance_reducible]
def algebra : Algebra Γ(Y, Y₀) ch.Ring := ch.map.hom.toAlgebra

attribute [local instance] algebra

lemma algebraMap_eq : algebraMap Γ(Y, Y₀) ch.Ring = ch.map.hom := rfl

include hY₀ in
/-- The ring of the chart is étale over `Γ(Y, Y₀)`. -/
theorem etale : Algebra.Etale Γ(Y, Y₀) ch.Ring :=
  RingHom.etale_algebraMap.mp
    (HasRingHomProperty.appLE (P := @AlgebraicGeometry.Etale) (Q := RingHom.Etale) c.1.hom
      inferInstance
      ⟨Y₀, hY₀⟩ ⟨ch.U₁, ch.isAffineOpen⟩ ch.le)

/-- The point of the ring of the chart given by the marked point `u`. -/
def point : ch.Ring →+* Ω := affinePoint c.2.left ch.isAffineOpen ch.mem

/-- The square expressing `U₁` as an open of `U` over `Y₀`. -/
lemma SpecMap_map_fromSpec : Spec.map ch.map ≫ hY₀.fromSpec = ch.isAffineOpen.fromSpec ≫ c.1.hom :=
  IsAffineOpen.SpecMap_appLE_fromSpec c.1.hom hY₀ ch.isAffineOpen ch.le

include hy in
/-- The point of the chart lies over the point of `Γ(Y, Y₀)` given by `y`. -/
lemma point_comp_map : ch.point.comp ch.map.hom = affinePoint y hY₀ hy := by
  have key : Spec.map (CommRingCat.ofHom (ch.point.comp ch.map.hom)) =
      Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom]
    apply (cancel_mono hY₀.fromSpec).mp
    rw [Category.assoc, SpecMap_map_fromSpec, ← Category.assoc]
    change (Spec.map (CommRingCat.ofHom (affinePoint c.2.left ch.isAffineOpen ch.mem)) ≫
      ch.isAffineOpen.fromSpec) ≫ c.1.hom = _
    have : c.2.left ≫ c.1.hom = y := CategoryTheory.Over.w c.2
    rw [SpecMap_affinePoint_fromSpec, this, SpecMap_affinePoint_fromSpec]
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  simpa using this

/-- The finite `Γ(U, U₁)`-algebra `Γ(U, U₁) ⊗ Γ(X, f ⁻¹ᵁ Y₀)`, the ring of `U₁ ×_Y X`. -/
abbrev Fiber : Type u := ch.Ring ⊗[Γ(Y, Y₀)] Γ(X, f ⁻¹ᵁ Y₀)

include hY₀ in
theorem finite_fiber : Module.Finite ch.Ring (ch.Fiber f) :=
  have := finite_affineAlgebra f hY₀
  Module.Finite.base_change _ _ _

include hy in
/-- The point of `Γ(U, U₁) ⊗ Γ(X, f ⁻¹ᵁ Y₀)` given by a geometric point of the fibre. -/
def basePoint (t : GeometricFiber f y) : PointsOver ch.point (ch.Fiber f) :=
  (geometricFiberEquivPointsOver f y hY₀ hy t).tensor (ch.point_comp_map hY₀ hy)

/-- `Spec (Γ(U, U₁) ⊗ Γ(X, f ⁻¹ᵁ Y₀))` is the fibre product `U₁ ×_Y X`. -/
lemma isPullback_fiber :
    IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Γ(Y, Y₀)) (A := ch.Ring) (B := Γ(X, f ⁻¹ᵁ Y₀)))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Γ(Y, Y₀))
        (A := ch.Ring) (B := Γ(X, f ⁻¹ᵁ Y₀))).toRingHom) ≫ (hY₀.preimage f).fromSpec)
      (Spec.map ch.map ≫ hY₀.fromSpec) f :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(Y, Y₀) ch.Ring Γ(X, f ⁻¹ᵁ Y₀))).paste_vert
    (isPullback_SpecMap_app_fromSpec f hY₀)
/-- The marked point of the chart, as a morphism `Spec Ω ⟶ U₁`. -/
lemma SpecMap_point_fromSpec :
    Spec.map (CommRingCat.ofHom ch.point) ≫ ch.isAffineOpen.fromSpec = c.2.left :=
  SpecMap_affinePoint_fromSpec c.2.left ch.isAffineOpen ch.mem

section Refine

/-!
### Refinements given by étale algebras over the chart

For an étale `Γ(U, U₁)`-algebra `A'` with a point over the point of the chart, `Spec A'` is a
pointed étale neighbourhood of `y` refining `(U, u)`.
-/

variable (A' : Type u) [CommRing A'] [Algebra ch.Ring A'] [Algebra.Etale ch.Ring A']
  (φ'' : A' →+* Ω) (hφ'' : φ''.comp (algebraMap ch.Ring A') = ch.point)

include hY₀ in
theorem etale_SpecMap_map : AlgebraicGeometry.Etale (Spec.map ch.map) :=
  HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale).mpr
    (RingHom.etale_algebraMap.mpr (ch.etale hY₀))

/-- The structure morphism of `Spec A'` as a `Y`-scheme. -/
def refineHom : Spec (.of A') ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap ch.Ring A')) ≫ Spec.map ch.map ≫ hY₀.fromSpec

include hY₀ in
theorem etale_refineHom : AlgebraicGeometry.Etale (ch.refineHom hY₀ A') := by
  have := ch.etale_SpecMap_map hY₀
  have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap ch.Ring A'))) :=
    HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  unfold refineHom
  infer_instance

/-- `Spec A'`, pointed by `φ''`, as a pointed étale neighbourhood of `y`. -/
def refine : Nbhd y :=
  have := ch.etale_refineHom hY₀ A'
  Functor.elementsMk _ (Scheme.Etale.mk (ch.refineHom hY₀ A')) (CategoryTheory.Over.homMk
    (Spec.map (CommRingCat.ofHom φ'')) (by
      change Spec.map (CommRingCat.ofHom φ'') ≫ ch.refineHom hY₀ A' = y
      rw [refineHom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ'',
        SpecMap_map_fromSpec, ← Category.assoc, SpecMap_point_fromSpec]
      exact CategoryTheory.Over.w c.2))

@[simp]
lemma refine_fst_hom : (ch.refine hY₀ A' φ'' hφ'').1.hom = ch.refineHom hY₀ A' := rfl

@[simp]
lemma refine_snd_left :
    (ch.refine hY₀ A' φ'' hφ'').2.left = Spec.map (CommRingCat.ofHom φ'') := rfl

/-- The refinement `Spec A' ⟶ U` of pointed étale neighbourhoods. -/
def refineMap : ch.refine hY₀ A' φ'' hφ'' ⟶ c :=
  Functor.Elements.homMk
    (MorphismProperty.Over.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap ch.Ring A')) ≫ ch.isAffineOpen.fromSpec) (by
        change (Spec.map (CommRingCat.ofHom (algebraMap ch.Ring A')) ≫ ch.isAffineOpen.fromSpec) ≫
          c.1.hom = ch.refineHom hY₀ A'
        rw [refineHom, Category.assoc, SpecMap_map_fromSpec]))
    (CategoryTheory.Over.OverMorphism.ext (by
      change Spec.map (CommRingCat.ofHom φ'') ≫
        Spec.map (CommRingCat.ofHom (algebraMap ch.Ring A')) ≫ ch.isAffineOpen.fromSpec = c.2.left
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ'',
        SpecMap_point_fromSpec]))

@[simp]
lemma refineMap_val_left : (ch.refineMap hY₀ A' φ'' hφ'').val.left =
    Spec.map (CommRingCat.ofHom (algebraMap ch.Ring A')) ≫ ch.isAffineOpen.fromSpec := rfl

/-- The ring of `Spec A' ×_Y X`. -/
abbrev RefineFiber : Type u := A' ⊗[ch.Ring] ch.Fiber f

/-- `Spec (A' ⊗ Γ(U, U₁) ⊗ Γ(X, f ⁻¹ᵁ Y₀))` is the fibre product `Spec A' ×_Y X`. -/
lemma isPullback_refine :
    IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ch.Ring) (A := A') (B := ch.Fiber f))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ch.Ring)
        (A := A') (B := ch.Fiber f)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Γ(Y, Y₀))
          (A := ch.Ring) (B := Γ(X, f ⁻¹ᵁ Y₀))).toRingHom) ≫ (hY₀.preimage f).fromSpec)
      (ch.refine hY₀ A' φ'' hφ'').1.hom f :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ch.Ring A' (ch.Fiber f))).paste_vert
    (ch.isPullback_fiber f hY₀)

/-- The isomorphism `Spec (A' ⊗ Γ(U, U₁) ⊗ Γ(X, f ⁻¹ᵁ Y₀)) ≅ Spec A' ×_Y X`. -/
def refineIso : Spec (.of (ch.RefineFiber f A')) ≅ pullback (ch.refine hY₀ A' φ'' hφ'').1.hom f :=
  (ch.isPullback_refine f hY₀ A' φ'' hφ'').isoPullback

include hy in
/-- The point of `Γ(X, f ⁻¹ᵁ Y₀)` given by a geometric point of the fibre, base changed to
the ring of `Spec A' ×_Y X`. -/
def fiberPoint (t : GeometricFiber f y) : PointsOver φ'' (ch.RefineFiber f A') :=
  (ch.basePoint f hY₀ hy t).tensor hφ''

/-- The geometric points of the fibre are in bijection with the points of the ring of
`U₁ ×_Y X` over the point of the chart. -/
lemma bijective_basePoint : Function.Bijective (ch.basePoint f hY₀ hy) :=
  (PointsOver.tensorEquiv (ch.point_comp_map hY₀ hy)).symm.bijective.comp
    (geometricFiberEquivPointsOver f y hY₀ hy).bijective

/-- The point `(u, t)` of `Spec A' ×_Y X` is `Spec` of `fiberPoint`. -/
lemma basePt_refine (t : GeometricFiber f y) :
    basePt f (ch.refine hY₀ A' φ'' hφ'') t =
      Spec.map (CommRingCat.ofHom (ch.fiberPoint f hY₀ hy A' φ'' hφ'' t).1) ≫
        (ch.refineIso f hY₀ A' φ'' hφ'').hom := by
  apply pullback.hom_ext
  · rw [basePt_fst, Category.assoc, refineIso, IsPullback.isoPullback_hom_fst, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, refine_snd_left]
    congr 2
    exact (ch.fiberPoint f hY₀ hy A' φ'' hφ'' t).comp_algebraMap.symm
  · rw [basePt_snd, Category.assoc, refineIso, IsPullback.isoPullback_hom_snd, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    have ht := geometricFiberEquivPointsOver_symm_apply_coe f y hY₀ hy
      (geometricFiberEquivPointsOver f y hY₀ hy t)
    rw [Equiv.symm_apply_apply] at ht
    rw [ht]
    congr 3
    rw [fiberPoint, PointsOver.tensor_comp_includeRight, basePoint,
      PointsOver.tensor_comp_includeRight]

end Refine

end Chart

end AlgebraicGeometry.Scheme.Hom

end
