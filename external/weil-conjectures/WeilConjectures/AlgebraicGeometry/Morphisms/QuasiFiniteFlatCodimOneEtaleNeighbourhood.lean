/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The pointwise ramification criterion for a flat quasi-finite morphism

## References

* Stacks Project, Lemma 58.21.2 (Tag 0BJH)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A flat morphism that is quasi-finite at a positive-dimensional source point
is etale near that point if it is unramified at its dimension-one generalizations. -/
theorem exists_etale_neighbourhood_of_flat_of_quasiFiniteAt_of_codimension_one
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (x : X)
    (hq : f.QuasiFiniteAt x)
    (hpos : (0 : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x))
    (hunram : ∀ x' : X, Specializes x' x →
      ringKrullDim (X.presheaf.stalk x') = 1 →
      ∃ V : X.Opens, x' ∈ V ∧ FormallyUnramified (V.ι ≫ f)) :
    ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f) := by
  obtain ⟨T, b, -, hb, -, -, V, hfinite, v, -, -, hv, -⟩ :=
    exists_etale_finite_open_of_isolated_fiber_point f x hq.isClopen_singleton_asFiber.isOpen
  have : Etale b := hb
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian b
  let a : V.toScheme ⟶ X := V.ι ≫ CategoryTheory.Limits.pullback.fst f b
  let g : V.toScheme ⟶ T := V.ι ≫ CategoryTheory.Limits.pullback.snd f b
  have : IsFinite g := hfinite
  have : Flat g := by dsimp [g]; infer_instance
  have : Etale a := by dsimp [a]; infer_instance
  have hcomm : a ≫ f = g ≫ b := by
    simp only [a, g, Category.assoc, CategoryTheory.Limits.pullback.condition]
  have hav : a v = x := hv
  have hdim (z : V) :
      ringKrullDim (X.presheaf.stalk (a z)) = ringKrullDim (V.toScheme.presheaf.stalk z) := by
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
    exact congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) (a.coheight_apply_of_flat z)
  have hposV : (0 : WithBot ℕ∞) < ringKrullDim (V.toScheme.presheaf.stalk v) := by
    rw [← hdim v, hav]
    exact hpos
  have hunramV : ∀ z : V, Specializes z v →
      ringKrullDim (V.toScheme.presheaf.stalk z) = 1 →
      ∃ W : V.toScheme.Opens, z ∈ W ∧ FormallyUnramified (W.ι ≫ g) := by
    intro z hz hd
    obtain ⟨W, hzW, hW⟩ := hunram (a z) (by simpa only [hav] using hz.map a.continuous)
      ((hdim z).trans hd)
    have : FormallyUnramified (W.ι ≫ f) := hW
    let W' := a ⁻¹ᵁ W
    have : FormallyUnramified ((a ∣_ W) ≫ (W.ι ≫ f)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
    have : FormallyUnramified ((W'.ι ≫ g) ≫ b) := by
      rw [Category.assoc, ← hcomm, ← Category.assoc,
        ← morphismRestrict_ι, Category.assoc]
      infer_instance
    exact ⟨W', hzW, FormallyUnramified.of_comp (W'.ι ≫ g) b⟩
  obtain ⟨B, hvB, hB⟩ :=
    exists_etale_neighbourhood_of_finite_flat_of_codimension_one g v hposV hunramV
  have : Etale (B.ι ≫ g) := hB
  let e := B.ι ≫ a
  have : Etale e := by dsimp [e]; infer_instance
  have : Etale (e ≫ f) := by
    simpa only [e, Category.assoc, hcomm] using
      (inferInstance : Etale ((B.ι ≫ g) ≫ b))
  let U : X.Opens := ⟨Set.range e, e.isOpenMap.isOpen_range⟩
  have hxU : x ∈ U := ⟨⟨v, hvB⟩, hv⟩
  let q : B.toScheme ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι e (by rw [Opens.range_ι]; exact Set.Subset.rfl)
  have hqfac : q ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
  have : Etale q := by
    have : Etale (q ≫ U.ι) := hqfac.symm ▸ inferInstance
    exact Etale.of_comp q U.ι
  have : Surjective q := by
    constructor
    intro z
    obtain ⟨w, hw⟩ := z.property
    refine ⟨w, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hqfac]
    exact hw
  have : Smooth (q ≫ (U.ι ≫ f)) := by
    rw [← Category.assoc, hqfac]
    infer_instance
  have hsm : Smooth (U.ι ≫ f) := Smooth.of_comp_of_flat_of_surjective q (U.ι ≫ f)
  have hzero : topologicalKrullDimAt (f.asFiber x) = 0 := by
    let W : (f.fiber (f x)).Opens := ⟨{f.asFiber x}, hq.isClopen_singleton_asFiber.isOpen⟩
    apply le_antisymm
    · have : Subsingleton W := inferInstanceAs (Subsingleton ({f.asFiber x} :
          Set (f.fiber (f x))))
      exact (iInf₂_le W (show f.asFiber x ∈ W from Set.mem_singleton _)).trans
        (topologicalKrullDim_zero_of_discreteTopology W)
    · apply le_iInf₂
      intro W hxW
      exact Order.krullDim_nonneg_iff.mpr
        ⟨⟨closure {⟨f.asFiber x, hxW⟩},
          isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨U', -, hxU', hU'⟩ :=
    exists_etale_open_of_smooth_of_fibre_dimension_zero f x U hxU hsm hzero
  exact ⟨U', hxU', hU'⟩

end AlgebraicGeometry.Scheme
