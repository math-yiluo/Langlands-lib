import Langlands.Global.AdelicSplitComponentTranslation
import Langlands.Global.AdelicConstantTermSplitComponent

/-! # Split-component points centralize the Levi factor and normalize the radical

For a compatible standard parabolic family, the image `b` in `G` of a point of the split component
`A_J` commutes with every point of `L_J` and normalizes `U_J`, on every test scheme. Hence the
translation formula of `AdelicSplitComponentTranslation` applies to `b`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Opposite
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

/-- The image in `G` of a point of the split component `A_J` commutes with every point of the
standard Levi `L_J`, on every test scheme. -/
theorem splitComponent_commute_standardLevi (J : Idx) (X : Over (Spec (CommRingCat.of F)))
    (a : X ⟶ (𝓕.A J).toGrp.X) {x : X ⟶ G.X}
    (hx : x ∈ (standardLevi 𝓕.i 𝓕.ν J.1).carrier X) :
    x * (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) = (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * x := by
  have hx' : x ∈ (SubgroupFunctor.range (𝓕.l J ≫ 𝓕.p J)).carrier X := by
    rw [(𝓕.isCompatible J).levi_eq]
    exact hx
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hx'
  have hc := (commute_of_mem_center ((𝓕.isCompatible J).splitComponent.1.2 X a) m).symm
  have hmap := hc.map (((yonedaGrp.map (𝓕.l J ≫ 𝓕.p J)).app (op X)).hom)
  change (m ≫ (𝓕.l J ≫ 𝓕.p J).hom.hom) *
      ((a ≫ (𝓕.a J).hom.hom) ≫ (𝓕.l J ≫ 𝓕.p J).hom.hom) =
    ((a ≫ (𝓕.a J).hom.hom) ≫ (𝓕.l J ≫ 𝓕.p J).hom.hom) *
      (m ≫ (𝓕.l J ≫ 𝓕.p J).hom.hom) at hmap
  rw [hm] at hmap
  simpa only [Grp.comp_hom_hom, Category.assoc] using hmap

/-- The image in `G` of a point of `A_J` lies in the standard parabolic `P_J`. -/
theorem splitComponent_mem_standardParabolic (J : Idx) (X : Over (Spec (CommRingCat.of F)))
    (a : X ⟶ (𝓕.A J).toGrp.X) :
    a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom ∈ (standardParabolic 𝓕.i 𝓕.ν J.1).carrier X := by
  rw [← (𝓕.isCompatible J).parabolic_eq]
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨a ≫ (𝓕.a J ≫ 𝓕.l J).hom.hom, ?_⟩
  simp only [Grp.comp_hom_hom, Category.assoc]

/-- The image of an `A_J` point normalizes `U_J`, on every test scheme. -/
theorem splitComponent_conj_mem (J : Idx) (X : Over (Spec (CommRingCat.of F)))
    (a : X ⟶ (𝓕.A J).toGrp.X) {w : X ⟶ G.X}
    (hw : w ∈ (standardUnipotent 𝓕.i 𝓕.ν J.1).carrier X) :
    (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * w * (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom)⁻¹ ∈
      (standardUnipotent 𝓕.i 𝓕.ν J.1).carrier X :=
  StandardConstantTerm.standardUnipotent_isNormalizedBy_standardParabolic 𝓕.i 𝓕.ν J.1 X _ w
    (𝓕.splitComponent_mem_standardParabolic J X a) hw

/-- The inverse of the image of an `A_J` point normalizes `U_J`, on every test scheme. -/
theorem splitComponent_conj_inv_mem (J : Idx) (X : Over (Spec (CommRingCat.of F)))
    (a : X ⟶ (𝓕.A J).toGrp.X) {w : X ⟶ G.X}
    (hw : w ∈ (standardUnipotent 𝓕.i 𝓕.ν J.1).carrier X) :
    (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom)⁻¹ * w * (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) ∈
      (standardUnipotent 𝓕.i 𝓕.ν J.1).carrier X := by
  have h := StandardConstantTerm.standardUnipotent_isNormalizedBy_standardParabolic 𝓕.i 𝓕.ν J.1 X
    _ w ((standardParabolic 𝓕.i 𝓕.ν J.1).carrier X |>.inv_mem
      (𝓕.splitComponent_mem_standardParabolic J X a)) hw
  rwa [inv_inv] at h

/-- **Translation by a split-component point.** For an adelic point `a` of `A_J` with image
`b ∈ G(𝔸)` and a measurable `φ ≥ 0` left-invariant under `P₀(F)` and `U_J(𝔸)`,
`∫_{D₀} φ(b g) dg = mulEquivHaarChar (conjugation by b on U_J(𝔸)) · ∫_{D₀} φ`. -/
theorem setLIntegral_splitComponent_mul_left_eq (J : Idx)
    (a : (algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) ⟶ (𝓕.A J).toGrp.X)
    {φ : AdelicGroupPoints F G → ℝ≥0∞} (hφ : Measurable φ)
    (hφΛ : ∀ l ∈ StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x)
    (hφU : ∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1), ∀ x, φ (w * x) = φ x) :
    haveI hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J.1
    haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1)) :=
      hcl.locallyCompactSpace
    ∫⁻ g in LeftCosetSpace.fundamentalDomain (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
        (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
        φ ((a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * g) ∂Measure.haar =
      (mulEquivHaarChar (StandardConstantTerm.conjPoints F G (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom)
          (fun _ hw => 𝓕.splitComponent_conj_mem J _ a hw)
          (fun _ hw => 𝓕.splitComponent_conj_inv_mem J _ a hw)) : ℝ≥0∞) *
        ∫⁻ g in LeftCosetSpace.fundamentalDomain
          (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), φ g ∂Measure.haar :=
  StandardConstantTerm.setLIntegral_mul_left_eq F G 𝓕.i 𝓕.ν (hG := 𝓕.connectedReductive)
    (hi := 𝓕.maximalSplit) (hν := 𝓕.generic) J.2 _
    (fun _ hx => (𝓕.splitComponent_commute_standardLevi J _ a hx).symm) _ _ hφ hφΛ hφU

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme AdelicSubgroupPoints

/-- **Statement form.** For a compatible standard parabolic family, a standard index `J` and an
adelic point `a` of the split component `A_J` with image `b` in `G(𝔸)`: `b` commutes with every
point of `L_J(𝔸)`, normalizes `U_J(𝔸)`, and for every measurable `φ ≥ 0` left-invariant under
`P₀(F)` and `U_J(𝔸)`, `∫_{D₀} φ(b g) dg = mulEquivHaarChar (conjugation by b on U_J(𝔸)) · ∫_{D₀} φ`. -/
def SplitComponentCentralizerStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (a : (algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) ⟶
        (𝓕.A J).toGrp.X),
    (∀ x ∈ adelicPoints F G (standardLevi 𝓕.i 𝓕.ν J.1),
      x * (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) = (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * x) ∧
    ∀ {φ : AdelicGroupPoints F G → ℝ≥0∞}, Measurable φ →
    (∀ l ∈ StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν, ∀ x, φ (l * x) = φ x) →
    (∀ w ∈ adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1), ∀ x, φ (w * x) = φ x) →
      haveI hcl := StandardConstantTerm.isClosed_adelicPoints_standardUnipotent F G 𝓕.i 𝓕.ν J.1
      haveI : LocallyCompactSpace (adelicPoints F G (standardUnipotent 𝓕.i 𝓕.ν J.1)) :=
        hcl.locallyCompactSpace
      ∫⁻ g in LeftCosetSpace.fundamentalDomain
          (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
          (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν),
          φ ((a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom) * g) ∂Measure.haar =
        (mulEquivHaarChar (StandardConstantTerm.conjPoints F G
            (a ≫ (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom)
            (fun _ hw => 𝓕.splitComponent_conj_mem J _ a hw)
            (fun _ hw => 𝓕.splitComponent_conj_inv_mem J _ a hw)) : ℝ≥0∞) *
          ∫⁻ g in LeftCosetSpace.fundamentalDomain
            (StandardConstantTerm.minimalParabolicImage F G 𝓕.i 𝓕.ν)
            (StandardConstantTerm.isDiscrete_minimalParabolicImage F G 𝓕.i 𝓕.ν), φ g ∂Measure.haar

/-- Proof of `SplitComponentCentralizerStatement`. -/
theorem splitComponentCentralizer : SplitComponentCentralizerStatement.{u} :=
  fun 𝓕 J a => ⟨fun _ hx => 𝓕.splitComponent_commute_standardLevi J _ a hx,
    fun hφ hφΛ hφU => 𝓕.setLIntegral_splitComponent_mul_left_eq J a hφ hφΛ hφU⟩

end Langlands.Global
