import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.LocalizedEtalePullbackExistence
import Langlands.Geometry.Analytic.LocalizedPullbackPoints

/-! # Continuous map descent along localized étale coverings -/

noncomputable section

universe u i

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Compatible full localized arrows along a jointly surjective étale
family determine a unique continuous map of the underlying spaces. -/
def EtaleCoverContinuousDescentStatement : Prop :=
  ∀ {S T : LocalizedCategory.{u, u, u} (K := K)} {ι : Type i}
    {U : ι → LocalizedCategory.{u, u, u} (K := K)}
    (q : ∀ j, U j ⟶ S) (m : ∀ j, U j ⟶ T),
    (∀ j, etale (q j)) →
    (∀ s : localizedSpaceFunctor.obj S,
      ∃ j, s ∈ Set.range (localizedSpaceFunctor.map (q j))) →
    (∀ {P : LocalizedCategory.{u, u, u} (K := K)} (j k : ι)
      (a : P ⟶ U j) (b : P ⟶ U k),
      a ≫ q j = b ≫ q k → a ≫ m j = b ≫ m k) →
    ∃! l : localizedSpaceFunctor.obj S ⟶ localizedSpaceFunctor.obj T,
      ∀ j, localizedSpaceFunctor.map (q j) ≫ l = localizedSpaceFunctor.map (m j)

theorem etaleCoverContinuousDescent :
    EtaleCoverContinuousDescentStatement.{u, i} K := by
  intro S T ι U q m hEtale hCover hMatch
  have hfibre (j k : ι) (x : localizedSpaceFunctor.obj (U j))
      (y : localizedSpaceFunctor.obj (U k))
      (hxy : localizedSpaceFunctor.map (q j) x = localizedSpaceFunctor.map (q k) y) :
      localizedSpaceFunctor.map (m j) x = localizedSpaceFunctor.map (m k) y := by
    obtain ⟨P, a, b, hP⟩ := exists_localizedPullback_of_etale (q j) (q k) (hEtale j)
    obtain ⟨z, hz₁, hz₂⟩ := exists_point_of_isPullback a b (q j) (q k) hP x y hxy
    have hz := congrArg (fun f : P ⟶ T => localizedSpaceFunctor.map f z)
      (hMatch j k a b hP.w)
    simpa only [Functor.map_comp, TopCat.comp_app, hz₁, hz₂] using hz
  choose member point hpoint using hCover
  let l : localizedSpaceFunctor.obj S → localizedSpaceFunctor.obj T :=
    fun s => localizedSpaceFunctor.map (m (member s)) (point s)
  have hl (j : ι) (x : localizedSpaceFunctor.obj (U j)) :
      l (localizedSpaceFunctor.map (q j) x) = localizedSpaceFunctor.map (m j) x :=
    hfibre _ j _ x (hpoint (localizedSpaceFunctor.map (q j) x))
  have hContinuous : Continuous l := by
    refine continuous_def.2 fun W hW => ?_
    have hPre : l ⁻¹' W = ⋃ j, localizedSpaceFunctor.map (q j) ''
        (localizedSpaceFunctor.map (m j) ⁻¹' W) := by
      ext s
      constructor
      · intro hs
        exact Set.mem_iUnion.2 ⟨member s, point s, hs, hpoint s⟩
      · intro hs
        obtain ⟨j, x, hx, rfl⟩ := Set.mem_iUnion.1 hs
        change l (localizedSpaceFunctor.map (q j) x) ∈ W
        rw [hl]
        exact hx
    rw [hPre]
    exact isOpen_iUnion fun j =>
      etaleOpenMap K (q j) (hEtale j) _
        (hW.preimage (localizedSpaceFunctor.map (m j)).hom.continuous)
  refine ⟨TopCat.ofHom ⟨l, hContinuous⟩, fun j => TopCat.ext (hl j), ?_⟩
  intro l' hl'
  apply TopCat.ext
  intro s
  have heq := congrArg (fun f : localizedSpaceFunctor.obj (U (member s)) ⟶
    localizedSpaceFunctor.obj T => f (point s)) (hl' (member s))
  change l' (localizedSpaceFunctor.map (q (member s)) (point s)) = l s at heq
  rwa [hpoint s] at heq

end Langlands.Analytic.SaturatedAtlasPresentation
