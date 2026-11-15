import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint
import Langlands.GroupScheme.Torus.Relative

/-! # Relative tori over strictly Henselian local rings are split -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An étale scheme over a strictly Henselian local ring that hits the closed point has a
section. -/
theorem exists_section_of_etale_of_isSepClosed (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Etale p] (hp : IsLocalRing.closedPoint R ∈ Set.range p) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ := by
  let κ := (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)
  have : IsSepClosed κ := isSepClosed_residueField_closedPoint R
  let f₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) :=
    (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)
  let P : Over (Spec (CommRingCat.of κ)) := Over.mk (pullback.snd p f₀)
  have : Etale P.hom := inferInstanceAs (Etale (pullback.snd p f₀))
  have : Nonempty P.left := by
    obtain ⟨x, hx⟩ := hp
    let y : Spec (CommRingCat.of κ) := IsLocalRing.closedPoint κ
    have hy : f₀ y = IsLocalRing.closedPoint R :=
      (Spec (CommRingCat.of R)).fromSpecResidueField_apply _ y
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x y (hx.trans hy.symm)
    exact ⟨z⟩
  obtain ⟨L, _, _, _, _, ⟨pt⟩⟩ := GaloisChartPoint.exists_separable_point P
  let φ : L →ₐ[κ] κ := IsSepClosed.lift
  let b : Spec (CommRingCat.of κ) ⟶ U :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ pt.left ≫ pullback.fst p f₀
  have hb : b ≫ p = f₀ := by
    have hpt : pt.left ≫ pullback.snd p f₀ = Spec.map (CommRingCat.ofHom (algebraMap κ L)) :=
      Over.w pt
    have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap κ L)) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext c
      exact φ.commutes c
    simp only [b, Category.assoc, pullback.condition]
    rw [reassoc_of% hpt, reassoc_of% hφ]
  obtain ⟨σ, hσ, -⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_etale p b hb
  exact ⟨σ, hσ⟩

/-- A relative torus over a strictly Henselian local ring is split. -/
theorem RelativeTorus.IsTorus.isSplitTorus_of_isSepClosed (R : Type u) [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : RelativeTorus.IsTorus G) :
    IsSplitTorus G := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  let i := 𝒰.idx (IsLocalRing.closedPoint R)
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isSepClosed R (𝒰.f i)
    (𝒰.covers (IsLocalRing.closedPoint R))
  exact IsSplitTorus.of_iso (sectionPullbackIso (𝒰.f i) σ hσ G).symm ((h𝒰 i).baseChange σ)

end Langlands.GroupScheme
