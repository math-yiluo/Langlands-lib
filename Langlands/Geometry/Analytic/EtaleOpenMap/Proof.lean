import Langlands.Geometry.Analytic.EtaleOpenMap.Statement
import Langlands.Geometry.Analytic.EtaleOpenMap.StrongOpen

/-! # Étale morphisms of analytic spaces are open -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Every analytic étale morphism has an open underlying point map. -/
theorem etaleOpenMap (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    EtaleOpenMapStatement.{u, v} K := by
  intro U V f hf
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  have hleft : IsOpenMap (localizedSpaceFunctor.map e.inv.left) :=
    ((TopCat.isIso_iff_isHomeomorph _).mp inferInstance).isOpenMap
  have hright : IsOpenMap (localizedSpaceFunctor.map e.hom.right) :=
    ((TopCat.isIso_iff_isHomeomorph _).mp inferInstance).isOpenMap
  rw [Arrow.iso_w' e, Functor.map_comp, Functor.map_comp, localizedSpaceFunctor_map]
  exact hright.comp (hg.isOpenMap.comp hleft)

end Langlands.Analytic.SaturatedAtlasPresentation
