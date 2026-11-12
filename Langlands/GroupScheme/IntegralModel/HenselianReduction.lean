import Langlands.GroupScheme.IntegralModelReduction
import Langlands.CommutativeAlgebra.HenselianSections

/-! # Generic injectivity and Henselian surjectivity of integral reduction

Integral sections of an actual affine model over a domain are determined by
their generic points, and over a Henselian local domain every residue-field
point of the special fibre of a smooth model lifts to an integral section.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

omit [IsDomain R] in
/-- The spectrum map of the fraction field is dominant. -/
theorem isDominant_specAlgebraMap : IsDominant (Spec.algebraMap R K) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap R K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
  exact bot_le

/-- Integral sections of an affine model over a domain are determined by their
generic points. -/
theorem integralPointMap_injective : Function.Injective M.integralPointMap := by
  intro x y hxy
  have hgen : baseChangeSectionHom (Spec.algebraMap R K) M.group x =
      baseChangeSectionHom (Spec.algebraMap R K) M.group y := by
    have h := congrArg (fun z => z ≫ M.genericIso.inv.hom.hom) hxy
    simpa only [integralPointMap, MonoidHom.comp_apply, rationalPoints.map_apply,
      Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id] using h
  have hx := baseChangeSectionHom_fst (Spec.algebraMap R K) M.group x
  have hy := baseChangeSectionHom_fst (Spec.algebraMap R K) M.group y
  rw [hgen] at hx
  have hb : Spec.algebraMap R K ≫ x.left = Spec.algebraMap R K ≫ y.left :=
    hx.symm.trans hy
  have : IsDominant (Spec.algebraMap R K) := isDominant_specAlgebraMap
  have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated M.group.X.hom
    ((Over.w x).trans (Over.w y).symm) (Spec.algebraMap R K) hb

/-- Smooth Henselian reduction: over a Henselian local domain, every
residue-field point of the special fibre of a smooth model lifts to an integral
section (KP Lemma 8.1.3, case `n = 1`). -/
theorem reduction_surjective [HenselianLocalRing R] (hM : M.IsSmooth) :
    Function.Surjective M.reduction := by
  intro y
  let : Smooth M.group.X.hom := hM
  have hK : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) :=
    IsLocalRing.residue_surjective
  have hy : y.left ≫ pullback.snd M.group.X.hom (residueBaseMap R) = 𝟙 _ := Over.w y
  let b : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ M.group.X.left :=
    y.left ≫ pullback.fst M.group.X.hom (residueBaseMap R)
  have hb : b ≫ M.group.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
    simp only [b, Category.assoc, pullback.condition]
    rw [← Category.assoc, hy]
    exact Category.id_comp (residueBaseMap R)
  obtain ⟨σ, hσ, hσb⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hK M.group.X.hom b hb
  refine ⟨Over.homMk σ (by simpa using hσ), ?_⟩
  apply Over.OverMorphism.ext
  rw [reduction_left]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact hσb
  · rw [pullback.lift_snd]
    exact hy.symm

end Langlands.GroupScheme.IntegralModel
