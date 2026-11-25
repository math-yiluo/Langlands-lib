/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension

/-!
# Fibre dimension after base change

Source: Stacks Project, Tag 02FY (lemma-dimension-fibre-after-base-change), part (1)
(blueprint: lem-sc-fibre-dimension-after-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An open embedding preserves the local topological Krull dimension at each point.
The open neighbourhoods inside its range are cofinal among all open neighbourhoods
of the image point, and the embedding identifies their dimensions. -/
private theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  apply le_antisymm
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens X := ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩
    refine (iInf₂_le V hx).trans ?_
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun p : V ↦ (⟨f p.1, p.2⟩ : U))
      (.of_comp (g := Subtype.val) (by fun_prop) ?_ ?_)
    · exact continuous_subtype_val
    · exact hf.toIsInducing.comp Topology.IsInducing.subtypeVal
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens Y := ⟨f '' U, hf.isOpenMap _ U.isOpen⟩
    let g : U → Y := fun p ↦ f p.1
    have hg : Topology.IsEmbedding g := hf.toIsEmbedding.comp
      Topology.IsEmbedding.subtypeVal
    have hr : Set.range g = (V : Set Y) := by
      ext y
      simp [g, V, Set.mem_image]
    refine (iInf₂_le V ⟨x, hx, rfl⟩).trans_eq ?_
    rw [hg.topologicalKrullDim_eq_range, hr]
    rfl

-- Reduce the scheme comparison to the declared affine tensor-product comparison.
private theorem localDim_field_extension
    {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    topologicalKrullDimAt (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) y) = topologicalKrullDimAt y := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let x := pullback.fst f g y
  obtain ⟨R, a, ha, ⟨z, hz⟩, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : IsOpenImmersion a := ha
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ f)
  have hft : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
  have hft' : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp hft
  let : Algebra k R := φ.hom.toAlgebra
  let : Algebra.FiniteType k R := hft'
  have hy : y ∈ Set.range (pullback.snd a (pullback.fst f g)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    change pullback.fst f g y ∈ Set.range a
    exact ⟨z, hz⟩
  obtain ⟨w, hw⟩ := hy
  let e := pullbackRightPullbackFstIso f g a ≪≫ pullback.congrHom hφ.symm rfl ≪≫
    pullbackSpecIso k R K
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K))) =
        pullback.fst a (pullback.fst f g) := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, Category.assoc, pullbackSpecIso_hom_fst]
    change (pullbackRightPullbackFstIso f g a).hom ≫
      (pullback.congrHom hφ.symm rfl).hom ≫ pullback.fst (Spec.map φ) g = _
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst]
  have hwz : pullback.fst a (pullback.fst f g) w = z := by
    apply a.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw, hz]
  have hd := topologicalKrullDimAt_spec_tensorProduct_field_extension (e.hom w)
  have hew : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K))
      (e.hom w) = z := by
    change (e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K)))) w = z
    rw [he]
    exact hwz
  rw [hew] at hd
  calc
    topologicalKrullDimAt x = topologicalKrullDimAt z :=
      hz ▸ (localDim_openEmbedding a.isOpenEmbedding z).symm
    _ = topologicalKrullDimAt (e.hom w) := hd
    _ = topologicalKrullDimAt w :=
      (localDim_openEmbedding e.hom.isOpenEmbedding w).symm
    _ = topologicalKrullDimAt y :=
      hw ▸ localDim_openEmbedding (pullback.snd a (pullback.fst f g)).isOpenEmbedding w

private theorem localDim_fiber_point {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) (x : X) (hy : f.fiberι s y = x) :
    topologicalKrullDimAt y = topologicalKrullDimAt (f.asFiber x) := by
  have hx : f x = s := by
    rw [← hy, ← Scheme.Hom.comp_apply, f.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst s
  congr 1
  apply (f.fiberι (f x)).isEmbedding.injective
  simpa using hy

/--
Source: Stacks Project, Tag 02FY (lemma-dimension-fibre-after-base-change), part (1)
(blueprint: lem-sc-fibre-dimension-after-base-change).
The fibre `(X')_{s'}` is identified with `X_s ×_{κ(s)} κ(s')` by an isomorphism
compatible with the maps to `X_s` and to `Spec κ(s')` (the base change of `X_s` along
`κ(s) → κ(s')`); `f x = s` is the cartesian-square relation `s = g(s') = f(x)`.
Proof: `Spec κ(s') → S' → S` factors through `Spec κ(s) → S` via the residue-field map,
so pullback pasting gives the fibre identification. `X_s` is locally of finite type over
`κ(s)` by base change; the dimension at a point is local, so on an affine neighbourhood
the field-extension dimension lemma (Tag 00P4) gives `dim_{x'} (X')_{s'} = dim_x X_s`.
-/
theorem fibre_dimension_after_base_change {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S)
    (x' : ↥(Limits.pullback f g)) :
    let f' : Limits.pullback f g ⟶ S' := Limits.pullback.snd f g
    let x : X := Limits.pullback.fst f g x'
    let s' : S' := f' x'
    let s : S := g s'
    (∃ e : f'.fiber s' ≅
        Limits.pullback (f.fiberToSpecResidueField s) (Spec.map (g.residueFieldMap s')),
      e.hom ≫ Limits.pullback.fst _ _ ≫ f.fiberι s =
          f'.fiberι s' ≫ Limits.pullback.fst f g ∧
        e.hom ≫ Limits.pullback.snd _ _ = f'.fiberToSpecResidueField s') ∧
      f x = s ∧
      topologicalKrullDimAt (f'.asFiber x') = topologicalKrullDimAt (f.asFiber x) := by
  let f' : pullback f g ⟶ S' := pullback.snd f g
  let x : X := pullback.fst f g x'
  let s' : S' := f' x'
  let s : S := g s'
  have h := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) s'
  let e := h.isoPullback
  have he₁ : e.hom ≫ pullback.fst _ _ ≫ f.fiberι s =
      f'.fiberι s' ≫ pullback.fst f g := by
    rw [← Category.assoc, h.isoPullback_hom_fst]
    simp only [pullback.map, Scheme.Hom.fiberι, s, f', pullback.lift_fst]
  have he₂ : e.hom ≫ pullback.snd _ _ = f'.fiberToSpecResidueField s' :=
    h.isoPullback_hom_snd
  refine ⟨⟨e, he₁, he₂⟩, ?_, ?_⟩
  · change (pullback.fst f g ≫ f) x' = (pullback.snd f g ≫ g) x'
    rw [pullback.condition]
  · let : Algebra (S.residueField s) (S'.residueField s') :=
      (g.residueFieldMap s').hom.toAlgebra
    have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    let y := e.hom (f'.asFiber x')
    have hd := localDim_field_extension (k := S.residueField s)
      (K := S'.residueField s') (f.fiberToSpecResidueField s) y
    have hp : f.fiberι s (pullback.fst (f.fiberToSpecResidueField s)
        (Spec.map (g.residueFieldMap s')) y) = x := by
      change (e.hom ≫ pullback.fst _ _ ≫ f.fiberι s) (f'.asFiber x') = x
      rw [he₁, Scheme.Hom.comp_apply]
      change pullback.fst f g (f'.fiberι (f' x') (f'.asFiber x')) = x
      rw [Scheme.Hom.fiberι_asFiber]
    exact ((localDim_openEmbedding e.hom.isOpenEmbedding (f'.asFiber x')).trans
      hd.symm).trans (localDim_fiber_point f s _ x hp)

end AlgebraicGeometry
