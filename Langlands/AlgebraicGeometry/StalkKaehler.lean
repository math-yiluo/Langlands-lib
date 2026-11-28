import Langlands.MathlibBase
import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-!
# Germs of differentials in the Kähler differentials of a local ring

For a scheme `Y` over `Spec κ`, a point `y` and an affine open `U ∋ y`, the map
`Γ(Ω¹_{Y/κ}, U) ≅ Ω[Γ(Y, U)⁄κ] → Ω[𝒪_{Y,y}⁄κ]`, sending `a db` to `a db`, compatible with
restriction to smaller affine opens; a free generator of `Ω¹_{Y/κ}` on `U` goes to a free generator
of `Ω[𝒪_{Y,y}⁄κ]`.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace KaehlerDifferential

namespace Langlands.AlgebraicGeometry.StalkKaehler

variable {κ : Type u} [CommRing κ] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of κ)) {y : Y}
  [Algebra κ (Y.presheaf.stalk y)]
  (hκ : ∀ (U : Y.Opens) (hy : y ∈ U),
    (Y.presheaf.germ U y hy).hom.comp (g.specStructureMap U).hom = algebraMap κ (Y.presheaf.stalk y))

/-- The compatibility hypothesis `hκ` holds on every open once it holds on `⊤`. -/
theorem germ_comp_specStructureMap_of_top
    (h : (Y.presheaf.germ ⊤ y trivial).hom.comp (g.specStructureMap ⊤).hom =
      algebraMap κ (Y.presheaf.stalk y)) (U : Y.Opens) (hy : y ∈ U) :
    (Y.presheaf.germ U y hy).hom.comp (g.specStructureMap U).hom =
      algebraMap κ (Y.presheaf.stalk y) := by
  rw [← h, ← g.specStructureMap_map (le_top : U ≤ ⊤), ← Y.presheaf.germ_res (homOfLE le_top) y hy]
  rfl

/-- The map `Γ(Ω¹_{Y/κ}, U) → Ω[𝒪_{Y,y}⁄κ]` for an affine open `U ∋ y`: the inverse of
`AlgebraicGeometry.Scheme.Hom.kaehlerSectionsEquiv` followed by
`KaehlerDifferential.map κ κ Γ(Y, U) 𝒪_{Y,y}`. -/
def toStalk (U : Y.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) :
    Γ(g.relativeDifferentials, U) → Ω[Y.presheaf.stalk y⁄κ] :=
  letI := (g.specStructureMap U).hom.toAlgebra
  letI := (Y.presheaf.germ U y hy).hom.toAlgebra
  haveI : IsScalarTower κ Γ(Y, U) (Y.presheaf.stalk y) :=
    .of_algebraMap_eq fun r ↦ (RingHom.congr_fun (hκ U hy) r).symm
  fun s ↦ map κ κ Γ(Y, U) (Y.presheaf.stalk y) ((g.kaehlerSectionsEquiv U rfl hU).symm s)

variable {g hκ}

theorem toStalk_add {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U)
    (s t : Γ(g.relativeDifferentials, U)) :
    toStalk g hκ U hU hy (s + t) = toStalk g hκ U hU hy s + toStalk g hκ U hU hy t := by
  simp only [toStalk, map_add]

theorem toStalk_zero {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U) :
    toStalk g hκ U hU hy 0 = 0 := by
  simp only [toStalk, map_zero]

theorem toStalk_smul {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U) (a : Γ(Y, U))
    (s : Γ(g.relativeDifferentials, U)) :
    toStalk g hκ U hU hy (a • s) = Y.presheaf.germ U y hy a • toStalk g hκ U hU hy s := by
  let := (g.specStructureMap U).hom.toAlgebra
  let := (Y.presheaf.germ U y hy).hom.toAlgebra
  have : IsScalarTower κ Γ(Y, U) (Y.presheaf.stalk y) :=
    .of_algebraMap_eq fun r ↦ (RingHom.congr_fun (hκ U hy) r).symm
  change map κ κ Γ(Y, U) (Y.presheaf.stalk y) ((g.kaehlerSectionsEquiv U rfl hU).symm (a • s)) =
    algebraMap Γ(Y, U) (Y.presheaf.stalk y) a •
      map κ κ Γ(Y, U) (Y.presheaf.stalk y) ((g.kaehlerSectionsEquiv U rfl hU).symm s)
  rw [LinearEquiv.map_smul, LinearMap.map_smul, algebraMap_smul]

theorem toStalk_sectionsD {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U) (a : Γ(Y, U)) :
    toStalk g hκ U hU hy (g.sectionsD U a) = D κ (Y.presheaf.stalk y) (Y.presheaf.germ U y hy a) := by
  let := (g.specStructureMap U).hom.toAlgebra
  let := (Y.presheaf.germ U y hy).hom.toAlgebra
  have : IsScalarTower κ Γ(Y, U) (Y.presheaf.stalk y) :=
    .of_algebraMap_eq fun r ↦ (RingHom.congr_fun (hκ U hy) r).symm
  change map κ κ Γ(Y, U) (Y.presheaf.stalk y) ((g.kaehlerSectionsEquiv U rfl hU).symm
    (g.sectionsD U a)) = D κ (Y.presheaf.stalk y) (algebraMap Γ(Y, U) (Y.presheaf.stalk y) a)
  rw [← g.kaehlerSectionsEquiv_D U rfl hU, LinearEquiv.symm_apply_apply, map_D]

/-- `toStalk` is compatible with restriction to a smaller affine open. -/
theorem toStalk_map {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (hy : y ∈ V) (s : Γ(g.relativeDifferentials, U)) :
    toStalk g hκ V hV hy (g.relativeDifferentials.presheaf.map (homOfLE h).op s) =
      toStalk g hκ U hU (h hy) s := by
  let := (g.specStructureMap U).hom.toAlgebra
  obtain ⟨ω, rfl⟩ := (g.kaehlerSectionsEquiv U rfl hU).surjective s
  have hω : ω ∈ Submodule.span Γ(Y, U) (Set.range (D κ Γ(Y, U))) := by
    rw [span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [g.kaehlerSectionsEquiv_D, ← g.sectionsD_map, toStalk_sectionsD, toStalk_sectionsD,
      TopCat.Presheaf.germ_res_apply]
  | zero => rw [map_zero, map_zero, toStalk_zero, toStalk_zero]
  | add x z _ _ hx hz => rw [map_add, map_add, toStalk_add, toStalk_add, hx, hz]
  | smul a x _ hx =>
    rw [LinearEquiv.map_smul, Scheme.Modules.map_smul, toStalk_smul, toStalk_smul, hx,
      TopCat.Presheaf.germ_res_apply]

/-- **A free generator goes to a free generator.** If `s` is a free generator of `Ω¹_{Y/κ}` on the
affine open `U ∋ y`, then `o ↦ o • toStalk s` is an isomorphism `𝒪_{Y,y} ≃ Ω[𝒪_{Y,y}⁄κ]`: the
stalk is a localization of `Γ(Y, U)`, so `Ω[𝒪_{Y,y}⁄κ] = 𝒪_{Y,y} ⊗ Ω[Γ(Y, U)⁄κ]`
(`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`). -/
theorem exists_linearEquiv_of_isFreeGenerator {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U)
    {s : Γ(g.relativeDifferentials, U)} (hs : Scheme.Modules.IsFreeGenerator s) :
    ∃ e : Y.presheaf.stalk y ≃ₗ[Y.presheaf.stalk y] Ω[Y.presheaf.stalk y⁄κ],
      e 1 = toStalk g hκ U hU hy s := by
  let := (g.specStructureMap U).hom.toAlgebra
  let := (Y.presheaf.germ U y hy).hom.toAlgebra
  have : IsScalarTower κ Γ(Y, U) (Y.presheaf.stalk y) :=
    .of_algebraMap_eq fun r ↦ (RingHom.congr_fun (hκ U hy) r).symm
  have := hU.isLocalization_stalk ⟨y, hy⟩
  have : Algebra.FormallyEtale Γ(Y, U) (Y.presheaf.stalk y) :=
    .of_isLocalization (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  set σ := (g.kaehlerSectionsEquiv U rfl hU).symm s with hσ_def
  have hσ : Function.Bijective (LinearMap.toSpanSingleton Γ(Y, U) _ σ) := by
    have : (LinearMap.toSpanSingleton Γ(Y, U) _ σ : Γ(Y, U) → Ω[Γ(Y, U)⁄κ]) =
        (g.kaehlerSectionsEquiv U rfl hU).symm ∘ fun r : Γ(Y, U) ↦ r • s := by
      ext r
      simp only [LinearMap.toSpanSingleton_apply, Function.comp_apply, LinearEquiv.map_smul, σ]
    rw [this]
    exact (g.kaehlerSectionsEquiv U rfl hU).symm.bijective.comp hs.bijective
  let eR : Γ(Y, U) ≃ₗ[Γ(Y, U)] Ω[Γ(Y, U)⁄κ] := LinearEquiv.ofBijective _ hσ
  refine ⟨(TensorProduct.AlgebraTensorModule.rid Γ(Y, U) (Y.presheaf.stalk y)
    (Y.presheaf.stalk y)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) eR ≪≫ₗ
    tensorKaehlerEquivOfFormallyEtale κ Γ(Y, U) (Y.presheaf.stalk y), ?_⟩
  simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.rid_symm_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, eR,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply]
  rfl

/-- The image of a free generator spans `Ω[𝒪_{Y,y}⁄κ]`. -/
theorem span_toStalk_eq_top {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U)
    {s : Γ(g.relativeDifferentials, U)} (hs : Scheme.Modules.IsFreeGenerator s) :
    Submodule.span (Y.presheaf.stalk y) {toStalk g hκ U hU hy s} = ⊤ := by
  obtain ⟨e, he⟩ := exists_linearEquiv_of_isFreeGenerator hU hy hs
  rw [← he, eq_top_iff]
  intro m _
  rw [Submodule.mem_span_singleton]
  exact ⟨e.symm m, by rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]⟩

end Langlands.AlgebraicGeometry.StalkKaehler
