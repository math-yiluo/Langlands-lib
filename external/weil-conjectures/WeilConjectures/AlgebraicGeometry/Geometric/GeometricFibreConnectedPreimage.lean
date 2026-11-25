/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-! # Connected geometric inverse images of purely inseparable singleton fibres

Source: Stacks Project, More on Morphisms, Tag 0BUI, Stein splitting paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- The residue-field point covers every point of this base change. Its composite
-- to the base is radicial, so its own base change has at most one point.
private theorem subsingleton_pullback_of_unique_fibre
    {W U Y : Scheme.{u}} (f : W ⟶ U) (g : Y ⟶ U) [Subsingleton Y]
    (v : W) (hg : ∀ y : Y, g y = f v)
    (hv : ∀ w : W, f w = f v → w = v)
    (hp : (f.residueFieldMap v).hom.IsPurelyInseparable) :
    Subsingleton ↥(pullback (C := Scheme.{u}) f g) := by
  let a := W.fromSpecResidueField v
  have ha : UniversallyInjective (a ≫ f) := by
    rw [← f.SpecMap_residueFieldMap_fromSpecResidueField v]
    let := (f.residueFieldMap v).hom.toAlgebra
    have : IsPurelyInseparable (U.residueField (f v)) (W.residueField v) := hp
    have : UniversallyInjective (Spec.map (f.residueFieldMap v)) :=
      (Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable
        (U.residueField (f v)) (W.residueField v)).isUniversalHomeomorphism.toUniversallyInjective
    exact MorphismProperty.comp_mem _ _ _ this inferInstance
  have hb : UniversallyInjective (pullback.snd (a ≫ f) g) :=
    MorphismProperty.pullback_snd _ _ ha
  have hsmall : Subsingleton ↥(pullback (C := Scheme.{u}) (a ≫ f) g) :=
    ⟨fun x y ↦ (pullback.snd (a ≫ f) g).injective (Subsingleton.elim _ _)⟩
  let e := pullbackRightPullbackFstIso f g a
  have hsmall' : Subsingleton ↥(pullback (C := Scheme.{u}) a (pullback.fst f g)) :=
    e.hom.homeomorph.subsingleton_congr.mpr hsmall
  have hsurj : Function.Surjective (pullback.snd a (pullback.fst f g)) := by
    intro z
    have hz : pullback.fst f g z = v := by
      apply hv
      calc
        f (pullback.fst f g z) = g (pullback.snd f g z) :=
          congrArg (fun k : pullback f g ⟶ U ↦ k z) pullback.condition
        _ = f v := hg _
    obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := a) (g := pullback.fst f g) (IsLocalRing.closedPoint (W.residueField v)) z
      (by simpa [a] using hz.symm)
    exact ⟨w, hw⟩
  exact ⟨fun x y ↦ by
    obtain ⟨x', rfl⟩ := hsurj x
    obtain ⟨y', rfl⟩ := hsurj y
    rw [Subsingleton.elim x' y']⟩

/-- Pulling one purely inseparable singleton fibre back along a geometrically connected
map gives a connected nonempty geometric fibre. No properness, etaleness, or finite
partition is assumed here.

Source: Stacks Project, More on Morphisms, Tag 0BUI, sentence "Then the schemes
X_{s_i'} are geometrically connected over κ(s)".
(blueprint: lem-weil-pbc-geometric-fibre-connected-preimage)

Proof: Let W be V.toScheme and f its map to U. The residue-field point
Spec κ(v) → W has universally injective composite to U: this factors through the
purely inseparable map Spec κ(v) → Spec κ(u) and the monomorphism Spec κ(u) → U.
After pullback to the geometric point its source has at most one point. Pullback
point-surjectivity and uniqueness of v show that this source surjects onto W_Ω,
so W_Ω has at most one point too. Another application of point-surjectivity gives
a point of W_Ω. Its image under the open-immersion pullback map is precisely the
inverse image of V in T_Ω, hence this inverse image is a singleton. The base change
of q to T_Ω is geometrically connected, and its inverse image of this singleton
is connected and nonempty by Scheme.Hom.isConnected_preimage_singleton. The
projection identities identify it with the displayed subset of X_Ω.
-/
theorem Scheme.Hom.isConnected_geometricFibre_preimage
    {X T U : Scheme.{u}} (q : X ⟶ T) [GeometricallyConnected q]
    (r : T ⟶ U) (p : X ⟶ U) (h : q ≫ r = p) (u : U) (V : T.Opens)
    (hv : ∃ v : V.toScheme, (V.ι ≫ r) v = u ∧
      (∀ w : V.toScheme, (V.ι ≫ r) w = u → w = v) ∧
      @IsPurelyInseparable (U.residueField ((V.ι ≫ r) v))
        (V.toScheme.residueField v) _ _ ((V.ι ≫ r).residueFieldMap v).hom.toAlgebra) :
    _root_.IsConnected
      ((pullback.fst p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (U.residueField u) (AlgebraicClosure (U.residueField u)))) ≫
            U.fromSpecResidueField u)) ⁻¹' (q ⁻¹' (V : Set T))) := by
  classical
  subst p
  obtain ⟨v, hvu, hv, hp⟩ := hv
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (U.residueField u) (AlgebraicClosure (U.residueField u)))) ≫
      U.fromSpecResidueField u
  have hg (y : Spec (.of (AlgebraicClosure (U.residueField u)))) : g y = u := by
    exact U.fromSpecResidueField_apply u _
  let f := V.ι ≫ r
  have hsmall : Subsingleton ↥(pullback (C := Scheme.{u}) f g) :=
    subsingleton_pullback_of_unique_fibre f g v (fun y ↦ (hg y).trans hvu.symm)
      (fun w hw ↦ hv w (hw.trans hvu)) hp
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) v (IsLocalRing.closedPoint _) (hvu.trans (hg _).symm)
  -- The open part of the geometric fibre of T is the image of V's geometric fibre.
  let j := pullback.map f g r g V.ι (𝟙 _) (𝟙 U) (by simp [f]) (by simp)
  have hj : Set.range j = (pullback.fst r g) ⁻¹' (V : Set T) := by
    dsimp only [j]
    rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι]
    simp
  have hsingle : (pullback.fst r g) ⁻¹' (V : Set T) = {j z} := by
    rw [← hj]
    ext t
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim w z]
      rfl
    · rintro rfl
      exact ⟨z, rfl⟩
  let b : pullback (q ≫ r) g ⟶ pullback r g :=
    pullback.lift (pullback.fst (q ≫ r) g ≫ q) (pullback.snd (q ≫ r) g)
      (by simp [Category.assoc, pullback.condition])
  have hb₁ : b ≫ pullback.fst r g = pullback.fst (q ≫ r) g ≫ q := by simp [b]
  have hb₂ : b ≫ pullback.snd r g = pullback.snd (q ≫ r) g := by simp [b]
  have hsquare : IsPullback (pullback.fst (q ≫ r) g) b q (pullback.fst r g) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd r g) (v₂₂ := r) (h₃₁ := g)
    · rw [hb₂]
      exact IsPullback.of_hasPullback (q ≫ r) g
    · exact hb₁.symm
    · exact IsPullback.of_hasPullback r g
  have : GeometricallyConnected b := MorphismProperty.of_isPullback hsquare inferInstance
  have heq : (pullback.fst (q ≫ r) g) ⁻¹' (q ⁻¹' (V : Set T)) = b ⁻¹' {j z} := by
    rw [← hsingle]
    ext x
    change q (pullback.fst (q ≫ r) g x) ∈ V ↔ pullback.fst r g (b x) ∈ V
    change (pullback.fst (q ≫ r) g ≫ q) x ∈ V ↔
      (b ≫ pullback.fst r g) x ∈ V
    rw [hb₁]
  change _root_.IsConnected ((pullback.fst (q ≫ r) g) ⁻¹' (q ⁻¹' (V : Set T)))
  rw [heq]
  exact b.isConnected_preimage_singleton (j z)

end AlgebraicGeometry
