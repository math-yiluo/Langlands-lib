import Langlands.Geometry.Building.StandardLeviStrictUniformizerStatement
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.StandardLeviCentralImage
import Langlands.GroupScheme.Rational.SplitComponentCocharacters
import Langlands.GroupScheme.Rational.SubtorusIntertwiningRoots
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Strict uniformizer images of actual standard Levi split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.RealTorusSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Evaluation at the common uniformizer commutes with an actual torus map. -/
theorem map_latticeSection (f : A ⟶ T) (ζ : cocharacterLattice A) :
    rationalPoints.map (CommGroupScheme.groupHom f)
        (latticeSection F A (Multiplicative.ofAdd ζ)) =
      latticeSection F T (Multiplicative.ofAdd (cocharacterMapInt f ζ)) := by
  change
    (((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
      (SplitTorusValuation.uniformizerUnit F) ≫
        (CommGroupScheme.groupHom ζ).hom.hom) ≫
        (CommGroupScheme.groupHom f).hom.hom) = _
  exact Category.assoc _ _ _

/-- Strict norm inequalities on a common-uniformizer value are exactly positive
integral character pairings. -/
theorem characterNorm_latticeSection_lt_one_iff
    (α : characterLattice A) (ζ : cocharacterLattice A) :
    characterNorm F A α (latticeSection F A (Multiplicative.ofAdd ζ)) < 1 ↔
      0 < latticePairing A α ζ := by
  rw [characterNorm_latticeSection]
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  rw [zpow_lt_one_iff_right₀ hq, neg_lt_zero]

/-- The actual strict section has precisely the standard integral cocharacter
image in the ambient maximal split torus. -/
theorem standardLeviStrictImage : StandardLeviStrictImageStatement.{u} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro ν _ J hJ L j hjc hj A a ha f hf
  have : IsAffineHom L.X.hom := hjc.isAffineHom_source
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : LocallyOfFiniteType L.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let t := standardLeviTorusFactor i ν J hj
  have ht : t ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  have htmax : IsMaximalSplitTorus t :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc
  have : Mono t.hom.hom.left := htmax.1.2.mono
  have : Mono j.hom.hom := hj.1
  have hft : CommGroupScheme.groupHom f ≫ t = a := by
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    exact congrArg (fun q => q.hom.hom)
      (show (CommGroupScheme.groupHom f ≫ t) ≫ j = a ≫ j by
        rw [Category.assoc, ht, hf])
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨ζ, hζ⟩ := hy.1
    have hypos := hy.2
    subst y
    refine ⟨cocharacterMapInt f ζ.toAdd, ⟨hJ, ?_, ?_⟩, ?_⟩
    · intro α hα
      exact latticePairing_cocharacterMapInt_standardLevi_eq_zero
        dynamicLie i ν J hJ hjc hj a ha.1 f hf ζ.toAdd hα
    · intro α hα hαJ
      have hnorm := hypos (f ≫ α) ⟨α, ⟨hα, hαJ⟩, rfl⟩
      have hpos := (characterNorm_latticeSection_lt_one_iff
        (f ≫ α) ζ.toAdd).mp hnorm
      rwa [RelativeRoot.latticePairing_restrict_cocharacterMapInt] at hpos
    · exact (map_latticeSection f ζ.toAdd).symm
  · rintro x ⟨ξ, hξ, rfl⟩
    have hcentral : ξ ∈ centralCocharacters t :=
      hξ.isCentral_standardLeviTorusFactor i ν J hj
    have hrange : ξ ∈ (cocharacterMapInt f).range := by
      rw [ha.range_cocharacterMapInt_eq_centralCocharacters f hft]
      exact hcentral
    obtain ⟨ζ, hζ⟩ := hrange
    refine ⟨latticeSection F A (Multiplicative.ofAdd ζ), ⟨?_, ?_⟩, ?_⟩
    · exact ⟨Multiplicative.ofAdd ζ, rfl⟩
    · rintro χ ⟨α, ⟨hα, hαJ⟩, rfl⟩
      apply characterNorm_latticeSection_lt_one
      rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt, hζ]
      exact hξ.2.2 α hα hαJ
    · rw [map_latticeSection, hζ]

end Langlands.GroupScheme.CocharacterUniformizer
