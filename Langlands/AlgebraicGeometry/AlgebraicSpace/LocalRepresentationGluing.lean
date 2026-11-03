import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing

/-! # Gluing representations over an open cover of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LocalRepresentation

variable {B : Scheme.{u}} {F : Presheaf B}

/-- The base open cover, viewed as a cover of the terminal object of the slice. -/
def baseCoverSieve (𝒰 : Scheme.OpenCover.{u} B) : Sieve (Over.mk (𝟙 B)) :=
  Sieve.ofArrows (fun i ↦ Over.mk (𝒰.f i))
    (fun i ↦ Over.homMk (𝒰.f i) (by simp))

lemma baseCoverSieve_mem (𝒰 : Scheme.OpenCover.{u} B) :
    baseCoverSieve 𝒰 ∈ (fppfTopology B) (Over.mk (𝟙 B)) := by
  change baseCoverSieve 𝒰 ∈ (Scheme.fppfTopology.over B) _
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ Scheme.fppfTopology _
  rw [Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono
    Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology

/-- Local representatives over a base open cover cover the original presheaf. -/
theorem charts_locallySurjective (𝒰 : Scheme.OpenCover.{u} B) (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology B)
      (Sigma.desc (fun i ↦ chart (𝒰.f i) (H i) (e i))) where
  imageSieve_mem {Z} x := by
    let q : Z ⟶ Over.mk (𝟙 B) := Over.homMk Z.hom (by simp)
    refine (fppfTopology B).superset_covering ?_
      ((fppfTopology B).pullback_stable q (baseCoverSieve_mem 𝒰))
    intro W k hk
    obtain ⟨i, α, _⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk
    obtain ⟨t, ht⟩ := (chartToProduct_bijective (𝒰.f i) (H i) (e i) W).surjective
      (F.map k.op x, ⟨α⟩)
    refine ⟨(Sigma.ι (fun i ↦ (schemeYoneda B).obj ((Over.map (𝒰.f i)).obj (H i))) i).app
      (op W) t, ?_⟩
    have hι := congrArg (fun η ↦ η.app (op W) t)
      (Sigma.ι_comp_desc (fun i ↦ chart (𝒰.f i) (H i) (e i)) i)
    exact hι.trans (congrArg Prod.fst ht)

/-- A sheaf with scheme representatives over an open cover is represented by a scheme. -/
theorem exists_representation (hF : Presheaf.IsSheaf (fppfTopology B) F)
    (𝒰 : Scheme.OpenCover.{u} B) (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F) :
    ∃ V : Over B, Nonempty ((schemeYoneda B).obj V ≅ F) := by
  let G : FppfSheaf B := ⟨F, hF⟩
  have := charts_locallySurjective 𝒰 H e
  exact SliceOpenGluing.exists_representation (G := G)
    (fun i ↦ chart_isOpenImmersion (𝒰.f i) (H i) (e i))

end LocalRepresentation

end Langlands.AlgebraicGeometry.AlgebraicSpace
