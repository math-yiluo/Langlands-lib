/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.GenericSmoothness
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Connected regular pieces of schemes of finite type over a perfect field

Let `q : P ⟶ D` be an immersion with open range, `D` with noetherian underlying space and `P`
nonempty and locally of finite type over a perfect field `k`. Then there is a nonempty open `V`
of `D`, contained in the range of `q`, and a surjective closed immersion `c : E ⟶ V` factoring
through `q`, with `E` a connected regular noetherian scheme
(`AlgebraicGeometry.exists_isRegular_isClosedImmersion_of_perfectField`).

Indeed, by generic smoothness
(`AlgebraicGeometry.exists_dense_isClosedImmersion_smooth_of_perfectField`) a dense open of
`P` is, up to a surjective closed immersion, smooth over `k`, hence regular; a noetherian
regular scheme is a finite disjoint union of open integral subschemes
(`AlgebraicGeometry.IsRegular.exists_isClopen_isIntegral`), and we take one of them.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Connected regular pieces**: let `q : P ⟶ D` be an immersion with open range from a
nonempty scheme `P` locally of finite type over a perfect field `k` to a scheme `D` with
noetherian underlying space. There are a nonempty open `V` of `D` and a surjective closed
immersion `c : E ⟶ V` from a connected regular noetherian scheme `E`, factoring through `q`. -/
theorem exists_isRegular_isClosedImmersion_of_perfectField {k : Type u} [Field k]
    [PerfectField k] {P D : Scheme.{u}} [TopologicalSpace.NoetherianSpace D] [Nonempty P]
    (aP : P ⟶ Spec (.of k)) [LocallyOfFiniteType aP] (q : P ⟶ D) [IsImmersion q]
    (hq : IsOpen (Set.range q.base)) :
    ∃ (V : D.Opens) (E : Scheme.{u}) (c : E ⟶ V) (e : E ⟶ P), (V : Set D).Nonempty ∧
      IsClosedImmersion c ∧ Surjective c ∧ c ≫ V.ι = e ≫ q ∧ IsNoetherian E ∧ IsRegular E ∧
      ConnectedSpace E := by
  obtain ⟨W, Z, z, hW, _, _, _⟩ := exists_dense_isClosedImmersion_smooth_of_perfectField aP
  have : IsRegular Z := IsRegular.of_smooth (z ≫ W.ι ≫ aP)
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (z ≫ W.ι ≫ aP)
  have : TopologicalSpace.NoetherianSpace Z :=
    (z ≫ W.ι ≫ q).isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian Z := {}
  obtain ⟨n, U, -, -, hU, hUi⟩ := IsRegular.exists_isClopen_isIntegral Z
  obtain ⟨w, hw⟩ := hW.nonempty
  obtain ⟨z₀, -⟩ := z.surjective ⟨w, hw⟩
  obtain ⟨a, ha⟩ : ∃ a, z₀ ∈ U a := by
    have : z₀ ∈ ⨆ a, U a := hU ▸ trivial
    simpa using this
  have := (hUi a).1
  let f := (U a).ι ≫ z ≫ W.ι ≫ q
  have hz : IsOpenMap z.base :=
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨z.isEmbedding, z.surjective⟩).isOpenMap
  have hf : IsOpenMap f.base :=
    (Topology.IsOpenEmbedding.isOpenMap ⟨q.isEmbedding, hq⟩).comp
      (W.ι.isOpenEmbedding.isOpenMap.comp (hz.comp (U a).ι.isOpenEmbedding.isOpenMap))
  let V : D.Opens := ⟨Set.range f.base, hf.isOpen_range⟩
  have hfV : Set.range f.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact subset_rfl
  let c := IsOpenImmersion.lift V.ι f hfV
  have hc : c ≫ V.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsImmersion (c ≫ V.ι) := hc ▸ inferInstance
  have : IsImmersion c := IsImmersion.of_comp c V.ι
  have : Surjective c := ⟨fun v ↦ by
    obtain ⟨x, hx⟩ := v.2
    refine ⟨x, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hc]
    exact hx⟩
  have : IsLocallyNoetherian (U a).toScheme := inferInstance
  have : TopologicalSpace.NoetherianSpace (U a).toScheme :=
    f.isEmbedding.isInducing.noetherianSpace
  refine ⟨V, U a, c, (U a).ι ≫ z ≫ W.ι, ⟨f.base ⟨z₀, ha⟩, ⟨z₀, ha⟩, rfl⟩,
    IsClosedImmersion.iff_isPreimmersion.mpr
      ⟨inferInstance, by rw [Set.range_eq_univ.mpr c.surjective]; exact isClosed_univ⟩,
    inferInstance, ?_, {},
    IsRegular.of_smooth ((U a).ι ≫ z ≫ W.ι ≫ aP), inferInstance⟩
  rw [hc]
  simp [f]

end AlgebraicGeometry
