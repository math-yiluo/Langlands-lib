/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # Finite connected-component decomposition of a smooth curve

Source: blueprint theorem-cohomology-curves--6, first step.
-/

@[expose] public section

universe u
open CategoryTheory Limits TopologicalSpace
namespace AlgebraicGeometry

/-- A qc separated smooth curve of relative dimension one is a finite coproduct
of connected smooth curves, compatibly with its structure map.
Source: blueprint theorem-cohomology-curves--6, first step.
(blueprint: lem-sc-smooth-curve-connected-coproduct)

Proof: Finite type over the field makes C Noetherian. Its connected components
are finitely many clopen subsets. Give each its open subscheme structure and
restrict f. The restricted morphisms remain separated, of finite type, and
smooth of relative dimension one. Each component is connected and nonempty,
so the dimension theorem for nonempty smooth schemes gives dimension exactly
one. Disjointness and coverage give the coproduct universal property. If C is
empty the component index set is empty and the same universal property applies. -/
theorem exists_smoothCurveConnectedCoproduct
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] :
    ∃ (I : Type u) (_ : Finite I) (D : I → Scheme.{u})
      (g : ∀ i, D i ⟶ Spec (.of k)) (ι : ∀ i, D i ⟶ C),
      (∀ i, IsConnectedCurve (g i) ∧ Smooth (g i)) ∧
      (∀ i, ι i ≫ f = g i) ∧ Nonempty (IsColimit (Cofan.mk C ι)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := {}
  let U (c : ConnectedComponents C) : C.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {c}, (isOpen_discrete {c}).preimage
      ConnectedComponents.continuous_coe⟩
  have hU : _root_.Pairwise (fun c d => Disjoint (U c) (U d)) := fun c d hcd =>
    Opens.coe_disjoint.mp ((Set.disjoint_singleton.mpr hcd).preimage ConnectedComponents.mk)
  have hcover : ⨆ c, U c = ⊤ := eq_top_iff.mpr fun x _ =>
    Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  refine ⟨ConnectedComponents C, inferInstance, fun c => (U c).toScheme,
    fun c => (U c).ι ≫ f, fun c => (U c).ι, ?_, fun _ => rfl, ?_⟩
  · intro c
    have : ConnectedSpace (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      have he : (U (ConnectedComponents.mk x) : Set C) = connectedComponent x :=
        connectedComponents_preimage_singleton
      exact isConnected_iff_connectedSpace.mp (he ▸ isConnected_connectedComponent)
    have : SmoothOfRelativeDimension 1 ((U c).ι ≫ f) := by
      simpa using (inferInstance : SmoothOfRelativeDimension (0 + 1) ((U c).ι ≫ f))
    have : Smooth ((U c).ι ≫ f) := SmoothOfRelativeDimension.smooth 1 _
    have : QuasiCompact (U c).ι := inferInstance
    refine ⟨{ toIsCurve := { krullDim_le_one := ?_ }
              connectedSpace := inferInstance
              krullDim_eq_one := ?_ }, inferInstance⟩
    · exact topologicalKrullDim_le_of_smoothOfRelativeDimension ((U c).ι ≫ f) 1
    · exact topologicalKrullDim_eq_of_smoothOfRelativeDimension ((U c).ι ≫ f) 1
  · apply nonempty_isColimit_cofanMk_of
    · simpa using hcover
    · intro c d hcd
      simpa using hU hcd

end AlgebraicGeometry
