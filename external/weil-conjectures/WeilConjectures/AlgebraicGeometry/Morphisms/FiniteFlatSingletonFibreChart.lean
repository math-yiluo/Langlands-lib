/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import WeilConjectures.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# A finite flat chart with a singleton fibre

## References

* Stacks Project, Tags 02LK and 0BJH
* Stacks Project, Tag 02LK, first proof
  paragraph
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Etale localization separates the selected point from the other points of its fibre. -/
theorem exists_finite_flat_singleton_fibre_chart
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X) :
    ∃ (Z T : Scheme.{u}) (a : Z ⟶ X) (b : T ⟶ Y) (g : Z ⟶ T) (z : Z),
      Etale a ∧ Etale b ∧ IsFinite g ∧ Flat g ∧
      IsLocallyNoetherian Z ∧ IsLocallyNoetherian T ∧
      a ≫ f = g ≫ b ∧ a z = x ∧
      (∀ w : Z, g w = g z → w = z) ∧
      (∀ w : Z, (∃ V : Z.Opens, w ∈ V ∧ Etale (V.ι ≫ g)) ↔
        ∃ V : X.Opens, a w ∈ V ∧ Etale (V.ι ≫ f)) := by
  obtain ⟨T, b, t, hb, -, -, V, hfinite, z, hzt, huniq, hzx, -⟩ :=
    exists_etale_finite_open_of_isolated_fiber_point f x
      (f.quasiFiniteAt x).isClopen_singleton_asFiber.isOpen
  have : Etale b := hb
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian b
  let a : V.toScheme ⟶ X := V.ι ≫ CategoryTheory.Limits.pullback.fst f b
  let g : V.toScheme ⟶ T := V.ι ≫ CategoryTheory.Limits.pullback.snd f b
  have : IsFinite g := hfinite
  have : Flat g := by dsimp [g]; infer_instance
  have : Etale a := by dsimp [a]; infer_instance
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian a
  have hcomm : a ≫ f = g ≫ b := by
    simp only [a, g, Category.assoc, CategoryTheory.Limits.pullback.condition]
  refine ⟨V.toScheme, T, a, b, g, z, inferInstance, hb, hfinite, inferInstance,
    inferInstance, inferInstance, hcomm, hzx, ?_, ?_⟩
  · intro w hw
    exact huniq w (hw.trans hzt)
  · intro w
    constructor
    · rintro ⟨B, hwB, hB⟩
      have : Etale (B.ι ≫ g) := hB
      let e := B.ι ≫ a
      have : Etale e := by dsimp [e]; infer_instance
      have : Etale (e ≫ f) := by
        simpa only [e, Category.assoc, hcomm] using
          (inferInstance : Etale ((B.ι ≫ g) ≫ b))
      let U : X.Opens := ⟨Set.range e, e.isOpenMap.isOpen_range⟩
      have hawU : a w ∈ U := ⟨⟨w, hwB⟩, rfl⟩
      let q : B.toScheme ⟶ U.toScheme :=
        IsOpenImmersion.lift U.ι e (by rw [Opens.range_ι]; exact Set.Subset.rfl)
      have hqfac : q ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
      have : Etale q := by
        have : Etale (q ≫ U.ι) := hqfac.symm ▸ inferInstance
        exact Etale.of_comp q U.ι
      have : Surjective q := by
        constructor
        intro y
        obtain ⟨v, hv⟩ := y.property
        refine ⟨v, ?_⟩
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hqfac]
        exact hv
      have : Smooth (q ≫ (U.ι ≫ f)) := by
        rw [← Category.assoc, hqfac]
        infer_instance
      have hsm : Smooth (U.ι ≫ f) := Smooth.of_comp_of_flat_of_surjective q (U.ι ≫ f)
      have hzero : topologicalKrullDimAt (f.asFiber (a w)) = 0 := by
        let W : (f.fiber (f (a w))).Opens :=
          ⟨{f.asFiber (a w)}, (f.quasiFiniteAt (a w)).isClopen_singleton_asFiber.isOpen⟩
        apply le_antisymm
        · have : Subsingleton W := inferInstanceAs
            (Subsingleton ({f.asFiber (a w)} : Set (f.fiber (f (a w)))))
          exact (iInf₂_le W (show f.asFiber (a w) ∈ W from Set.mem_singleton _)).trans
            (topologicalKrullDim_zero_of_discreteTopology W)
        · apply le_iInf₂
          intro W hwW
          exact Order.krullDim_nonneg_iff.mpr
            ⟨⟨closure {⟨f.asFiber (a w), hwW⟩},
              isIrreducible_singleton.closure, isClosed_closure⟩⟩
      obtain ⟨U', -, hwU', hU'⟩ :=
        exists_etale_open_of_smooth_of_fibre_dimension_zero f (a w) U hawU hsm hzero
      exact ⟨U', hwU', hU'⟩
    · rintro ⟨U, hwU, hU⟩
      have : Etale (U.ι ≫ f) := hU
      let W := a ⁻¹ᵁ U
      have : Etale ((a ∣_ U) ≫ (U.ι ≫ f)) := inferInstance
      have : Etale ((W.ι ≫ g) ≫ b) := by
        rw [Category.assoc, ← hcomm, ← Category.assoc,
          ← morphismRestrict_ι, Category.assoc]
        infer_instance
      exact ⟨W, hwU, Etale.of_comp (W.ι ≫ g) b⟩

end AlgebraicGeometry.Scheme
