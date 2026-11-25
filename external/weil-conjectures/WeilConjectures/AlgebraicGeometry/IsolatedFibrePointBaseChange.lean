/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Points isolated in their fibre stay isolated after base change

Source: literature/stacks-project/morphisms.tex, Lemma 01TM (1)
(blueprint: lem-weil-pbc-isolated-fibre-point-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isOpen_singleton_of_field_pullback
    {k K : Type u} [Field k] [Field K] {F T : Scheme.{u}}
    (p : F ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (q : Spec (.of K) ⟶ Spec (.of k)) (h : T ⟶ F) (b : T ⟶ Spec (.of K))
    (hp : IsPullback h b p q) (z : T) (hz : IsOpen ({h z} : Set F)) :
    IsOpen ({z} : Set T) := by
  let U : F.Opens := ⟨{h z}, hz⟩
  have : Subsingleton U.toScheme := by
    change Subsingleton ↥({h z} : Set F)
    infer_instance
  -- The open singleton is locally of finite type and has at most one point in each fibre.
  have : LocallyQuasiFinite (U.ι ≫ p) :=
    LocallyQuasiFinite.of_injective (fun a a' _ ↦ Subsingleton.elim a a')
  -- Its open inverse image is its base change, hence locally Artinian over the field K.
  have hpU := (isPullback_morphismRestrict h U).paste_vert hp
  have : LocallyQuasiFinite ((h ⁻¹ᵁ U).ι ≫ b) :=
    MorphismProperty.of_isPullback hpU inferInstance
  have : IsLocallyArtinian (h ⁻¹ᵁ U).toScheme :=
    IsLocallyArtinian.of_locallyQuasiFinite ((h ⁻¹ᵁ U).ι ≫ b)
  let zU : (h ⁻¹ᵁ U).toScheme := ⟨z, Set.mem_singleton _⟩
  simpa [Set.image_singleton, zU] using
    (h ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap ({zU} : Set (h ⁻¹ᵁ U).toScheme)
      (isOpen_discrete _)

/-- Source: literature/stacks-project/morphisms.tex, Lemmas 01TM (1) and 01TH (1)-(2);
literature/stacks-project/algebra.tex, proof of Lemma 00PP (1).
(blueprint: lem-weil-pbc-isolated-fibre-point-base-change).
If a point is isolated in the fibre of a locally finite type morphism, then
any point above it after base change is isolated in the new fibre.

Proof:
1. By `lem-weil-pbc-fibre-of-base-change`, identify the new fibre with the base change
   of the old fibre along the residue field extension. Its map to the old fibre sends
   the new fibre point to the old one: use commutativity of the fibre projections and
   their injectivity (`def-pc-scheme-fibre`). The old singleton is open by hypothesis.
2. Let W be the open subscheme consisting of this singleton (`def-weil-open-immersion`).
   Its inclusion is locally of finite type by `lem-weil-pbc-immersion-base-change-lft` (2).
   The old fibre is locally of finite type over its residue field by
   `lem-weil-pbc-lft-base-change`; composition with the inclusion is locally of finite
   type by `lem-weil-pbc-proper-fp-permanence` (e). The one-point space W is discrete.
3. By `lem-weil-pbc-discrete-field-base-change-artinian`, the base change of W along
   the residue field extension is discrete. By `lem-weil-pbc-open-fibre-product`, its
   map into the new fibre is an open immersion (`def-weil-open-immersion`) whose image
   is the inverse image of W. Thus this inverse image is both open and discrete.
4. The chosen new fibre point belongs to this inverse image. Its singleton is open
   there by discreteness, and hence is open in the whole new fibre.
-/
theorem isolated_fiber_point_base_change
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (x' : ↥(pullback f g))
    (hx : IsOpen ({f.asFiber (pullback.fst f g x')} :
      Set (f.fiber (f (pullback.fst f g x'))))) :
    IsOpen ({(pullback.snd f g).asFiber x'} :
      Set ((pullback.snd f g).fiber ((pullback.snd f g) x'))) := by
  let y := pullback.snd f g x'
  let h : (pullback.snd f g).fiber y ⟶ f.fiber (g y) :=
    pullback.map (pullback.snd f g) (S'.fromSpecResidueField y) f
      (S.fromSpecResidueField (g y)) (pullback.fst f g)
      (Spec.map (g.residueFieldMap y)) g (pullback.condition.symm) (by simp)
  have hp := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y
  have hc : f (pullback.fst f g x') = g y := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun a : pullback f g ⟶ S ↦ a x') pullback.condition
  have hz : IsOpen ({h ((pullback.snd f g).asFiber x')} : Set (f.fiber (g y))) := by
    have hxo : IsOpen ({⟨pullback.fst f g x', rfl⟩} :
        Set (f ⁻¹' {f (pullback.fst f g x')})) := by
      simpa [Set.image_singleton, Scheme.Hom.asFiber] using
        (f.fiberHomeo (f (pullback.fst f g x'))).isOpenMap _ hx
    rw [← (f.fiberHomeo (g y)).isOpen_image, Set.image_singleton]
    have hi : f.fiberι (g y) (h ((pullback.snd f g).asFiber x')) =
        pullback.fst f g x' := by
      have hh : h ≫ f.fiberι (g y) =
          (pullback.snd f g).fiberι y ≫ pullback.fst f g := pullback.lift_fst _ _ _
      simpa only [y, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using
        congrArg (fun a : (pullback.snd f g).fiber y ⟶ X ↦
          a ((pullback.snd f g).asFiber x')) hh
    have hpoint : f.fiberHomeo (g y) (h ((pullback.snd f g).asFiber x')) =
        ⟨pullback.fst f g x', hc⟩ := Subtype.ext hi
    rw [hpoint]
    let e := Homeomorph.setCongr
      (show f ⁻¹' {f (pullback.fst f g x')} = f ⁻¹' {g y} by rw [hc])
    have hepoint : e ⟨pullback.fst f g x', rfl⟩ = ⟨pullback.fst f g x', hc⟩ := by
      apply Subtype.ext
      simp [e, Homeomorph.setCongr]
    simpa only [Set.image_singleton, hepoint] using e.isOpenMap _ hxo
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g y))))
  exact isOpen_singleton_of_field_pullback (f.fiberToSpecResidueField (g y))
    (Spec.map (g.residueFieldMap y)) h ((pullback.snd f g).fiberToSpecResidueField y)
    hp ((pullback.snd f g).asFiber x') hz

end AlgebraicGeometry
