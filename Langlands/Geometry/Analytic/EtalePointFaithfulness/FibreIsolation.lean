import Langlands.Geometry.Analytic.EtaleSite
import Mathlib.Topology.Separation.Basic

/-! # Isolation of points in analytic étale fibres -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Set Filter Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem t1Space_of_locallyHausdorff {Y : Type v} [TopologicalSpace Y]
    (h : ∀ y : Y, ∃ H : Set Y, H ∈ 𝓝 y ∧ T2Space H) : T1Space Y := by
  apply t1Space_iff_specializes_imp_eq.2
  intro x y hxy
  obtain ⟨H, hH, hT⟩ := h y
  let := hT
  have hx : x ∈ H := hxy.pure_le_nhds hH
  have hy : y ∈ H := mem_of_mem_nhds hH
  exact congrArg Subtype.val
    ((subtype_specializes_iff (⟨x, hx⟩ : H) ⟨y, hy⟩).2 hxy).eq

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, v} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- A point of a quasifinite analytic map has an open neighborhood containing
no other point in the same fibre. -/
theorem IsQuasifinite.exists_open_fibreIsolation (hg : g.IsQuasifinite) (y : A.space) :
    ∃ V : Set A.space, IsOpen V ∧ y ∈ V ∧
      ∀ z ∈ V, g.baseMap z = g.baseMap y → z = y := by
  let : T1Space A.space := t1Space_of_locallyHausdorff A.atlas.locallyHausdorff
  obtain ⟨V, U, hV, hU, hy, hfin⟩ := hg y
  have hxU : g.baseMap y ∈ U := hfin.1 ⟨y, hy, rfl⟩
  obtain ⟨I, -, hI, hIN⟩ :=
    B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y) U (hU.mem_nhds hxU)
  obtain ⟨W, hWI, -⟩ := Set.mem_iUnion₂.1 (mem_of_mem_nhds hIN)
  have hF := hfin.finite_fibre W (hI W hWI).2 (hI W hWI).1
  let F : Set A.space := (V ∩ g.baseMap ⁻¹' {g.baseMap y}) \ {y}
  have hFc : IsClosed F := hF.sdiff.isClosed
  refine ⟨V \ F, hV.sdiff hFc, ⟨hy, ?_⟩, ?_⟩
  · rintro ⟨-, hyy⟩
    exact hyy rfl
  · intro z hz hzy
    by_contra hne
    exact hz.2 ⟨⟨hz.1, hzy⟩, hne⟩

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

/-- A point of a localized analytic étale map has an open neighborhood
containing no other point of the same underlying fibre. -/
theorem etale_exists_open_fibreIsolation
    {U X : LocalizedCategory.{u, v, v} (K := K)}
    (f : U ⟶ X) (hf : etale f) (y : localizedSpaceFunctor.obj U) :
    ∃ V : Set (localizedSpaceFunctor.obj U), IsOpen V ∧ y ∈ V ∧
      ∀ z ∈ V, localizedSpaceFunctor.map f z = localizedSpaceFunctor.map f y → z = y := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let a := localizedSpaceFunctor.map e.inv.left
  have ha : IsHomeomorph a := (TopCat.isIso_iff_isHomeomorph _).mp inferInstance
  obtain ⟨V, hV, hy, hiso⟩ :=
    hg.isEtale.isQuasifinite.exists_open_fibreIsolation (a y)
  refine ⟨a ⁻¹' V, hV.preimage ha.continuous, hy, ?_⟩
  intro z hz hzy
  apply ha.injective
  apply hiso (a z) hz
  have hw := congrArg (fun k => localizedSpaceFunctor.map k z) e.inv.w
  have hw' := congrArg (fun k => localizedSpaceFunctor.map k y) e.inv.w
  simp only [Functor.map_comp, TopCat.comp_app] at hw hw'
  exact hw.trans ((congrArg (localizedSpaceFunctor.map e.inv.right) hzy).trans hw'.symm)

end SaturatedAtlasPresentation
end Langlands.Analytic
