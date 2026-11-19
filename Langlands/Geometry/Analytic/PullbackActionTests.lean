import Langlands.Geometry.Analytic.ContinuousAnalyticAction

/-! # Local invariance of pullback chart patches -/

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G]
  {P U V : LocalizedCategory.{u, v, w} (K := K)}
  {σ : G →* Aut P} {σU : G →* Aut U} {σV : G →* Aut V}

/-- Near the group identity, an equivariant map pulls each chart of the
continuous target action back to a set preserved by the source action. -/
theorem IsContinuousAction.eventually_preimage_eq_of_equivariant
    (hU : IsContinuousAction σU) (p : P ⟶ U)
    (hp : ∀ a, (σ a).hom ≫ p = p ≫ (σU a).hom)
    (i : (presentationOf U).presentation.atlas.Index) :
    ∀ᶠ a in 𝓝 (1 : G), localizedSpaceFunctor.map (σ a).hom ⁻¹'
      (localizedSpaceFunctor.map p ⁻¹' range ((presentationOf U).presentation.atlas.chart i)) =
      localizedSpaceFunctor.map p ⁻¹' range ((presentationOf U).presentation.atlas.chart i) := by
  let τ : TestTriple (presentationOf U) := ⟨i, 0, 1, zero_lt_one⟩
  filter_upwards [hU τ] with a ha
  have hchart := (show IsNear τ (σU a).hom (𝟙 U) from ha).preimage_eq
  rw [CategoryTheory.Functor.map_id, TopCat.coe_id] at hchart
  change _ = τ.locus at hchart
  change localizedSpaceFunctor.map (σ a).hom ⁻¹' (localizedSpaceFunctor.map p ⁻¹' τ.locus) =
    localizedSpaceFunctor.map p ⁻¹' τ.locus
  calc
    _ = localizedSpaceFunctor.map ((σ a).hom ≫ p) ⁻¹' τ.locus := by
      rw [CategoryTheory.Functor.map_comp]
      rfl
    _ = localizedSpaceFunctor.map (p ≫ (σU a).hom) ⁻¹' τ.locus :=
      congrArg (fun k : P ⟶ U => localizedSpaceFunctor.map k ⁻¹' τ.locus) (hp a)
    _ = localizedSpaceFunctor.map p ⁻¹' τ.locus := by
      rw [CategoryTheory.Functor.map_comp]
      exact congrArg (localizedSpaceFunctor.map p ⁻¹' ·) hchart

/-- A basic pullback patch is preserved by all elements in some identity
neighbourhood, from the two factor actions and their projection equations. -/
theorem eventually_preimage_eq_pullback_patch
    (hU : IsContinuousAction σU) (hV : IsContinuousAction σV)
    (p : P ⟶ U) (q : P ⟶ V)
    (hp : ∀ a, (σ a).hom ≫ p = p ≫ (σU a).hom)
    (hq : ∀ a, (σ a).hom ≫ q = q ≫ (σV a).hom)
    (i : (presentationOf U).presentation.atlas.Index)
    (j : (presentationOf V).presentation.atlas.Index) :
    let patch := (localizedSpaceFunctor.map p ⁻¹' range ((presentationOf U).presentation.atlas.chart i)) ∩
      (localizedSpaceFunctor.map q ⁻¹' range ((presentationOf V).presentation.atlas.chart j))
    ∀ᶠ a in 𝓝 (1 : G), localizedSpaceFunctor.map (σ a).hom ⁻¹' patch = patch := by
  dsimp only
  filter_upwards [hU.eventually_preimage_eq_of_equivariant p hp i,
    hV.eventually_preimage_eq_of_equivariant q hq j] with a hi hj
  rw [preimage_inter, hi, hj]

end Langlands.Analytic.SaturatedAtlasPresentation
