import Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Rational.SplitComponentCocharacters
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.LinearAlgebra.RationalRealSpan

/-! # Actual split-component realizations of all central directions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

section SmoothConnected

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {a : A.toGrp ⟶ G}

/-- Integral centrality of root-annihilating cocharacters identifies the actual
real image of every split component with the full common root annihilator. -/
theorem IsSplitComponent.range_cocharacterMapReal_eq_relativeCentralDirections
    (hcentral : RootAnnihilatorCentralityStatement.{u})
    (ha : IsSplitComponent a) (hT : IsSplitTorus T.toGrp)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = a) :
    (cocharacterMapReal f).range = relativeCentralDirections i := by
  let := (hT.finite_relativeRoots i).fintype
  have hc : IsCentral (CommGroupScheme.groupHom f ≫ i) := by
    rw [hf]
    exact ha.1.2
  apply le_antisymm
  · apply (range_cocharacterMapReal_le_rootAnnihilator_iff f (relativeRoots i)).mpr
    intro μ α hα
    change gmEndEquiv k ((μ ≫ f) ≫ α) = 0
    rw [Category.assoc, root_restrict_eq_zero_of_isCentral i f ha.1.1.1 hc hα]
    simp
  · exact ha.rootAnnihilator_le_range_cocharacterMapReal f hf (relativeRoots i)
      (hcentral k G T hT i)

/-- The actual cocharacter map, as an equivalence onto all central directions.
The only structural input is the root-annihilator centrality criterion. -/
def IsSplitComponent.cocharacterEquivCentralDirections
    (hcentral : RootAnnihilatorCentralityStatement.{u})
    (ha : IsSplitComponent a) (hT : IsSplitTorus T.toGrp)
    (f : A ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
    (hf : CommGroupScheme.groupHom f ≫ i = a) :
    V A ≃ₗ[ℝ] relativeCentralDirections i :=
  (LinearEquiv.ofInjective (cocharacterMapReal f) (cocharacterMapReal_injective f)).trans
    (LinearEquiv.ofEq _ _
      (ha.range_cocharacterMapReal_eq_relativeCentralDirections hcentral hT f hf))

@[simp] theorem IsSplitComponent.cocharacterEquivCentralDirections_coe
    (hcentral : RootAnnihilatorCentralityStatement.{u})
    (ha : IsSplitComponent a) (hT : IsSplitTorus T.toGrp)
    (f : A ⟶ T) [Mono (CommGroupScheme.groupHom f).hom.hom.left]
    (hf : CommGroupScheme.groupHom f ≫ i = a) (v : V A) :
    (ha.cocharacterEquivCentralDirections hcentral hT f hf v : V T) =
      cocharacterMapReal f v := rfl

/-- Both exact restriction kernels follow from the actual image equality:
perfect real duality first, then faithful rational-to-real descent. -/
theorem IsSplitComponent.restriction_kernels_eq_relativeRootSpans
    (hcentral : RootAnnihilatorCentralityStatement.{u})
    (ha : IsSplitComponent a) (hT : IsSplitTorus T.toGrp)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ i = a) :
    (rationalCharacterRestrictRat (CommGroupScheme.groupHom f)).ker =
        relativeRootSpan i ∧
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker =
        relativeRootSpanReal i := by
  have hreal := ker_restrictReal_eq_relativeRootSpanReal_of_range
    ha.1.1.1 hT i f
    (ha.range_cocharacterMapReal_eq_relativeCentralDirections hcentral hT f hf)
  refine ⟨?_, hreal⟩
  exact ker_baseChange_rat_eq_ratSpan_of_real
    (characterRestrict (CommGroupScheme.groupHom f)).toIntLinearMap (relativeRoots i) hreal

end SmoothConnected

/-- The full split-central-direction target follows from the geometric
centrality criterion and integral character restriction, with no realization,
rank or complement premise. -/
theorem relativeSplitCentralDirections_of_centrality_characterRestriction
    (hcentral : RootAnnihilatorCentralityStatement.{u})
    (hrestriction : CharacterRestrictionStatement.{u}) :
    RelativeSplitCentralDirectionsStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  let := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus T.toGrp := hi.1.1
  let := hT.finite_realCocharacterSpace
  let := hT.finite_realCharacterSpace
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k G hG).1
  obtain ⟨f, hf, hfc, hfinj⟩ := ha.exists_commFactor_of_isMaximalSplitTorus hi
  have himage := ha.range_cocharacterMapReal_eq_relativeCentralDirections hcentral hT f hf
  have hc : IsCentral (CommGroupScheme.groupHom f ≫ i) := by
    rw [hf]
    exact ha.1.2
  have hrank : Module.finrank ℝ (relativeCentralDirections i) = rationalCharacterRank G := by
    calc
      Module.finrank ℝ (relativeCentralDirections i) =
          Module.finrank ℝ (V A) := by
        rw [← himage]
        exact LinearMap.finrank_range_of_inj hfinj
      _ = splitTorusRank A := ha.1.1.1.finrank_realCocharacterSpace
      _ = rationalCharacterRank G :=
        (rationalCharacterRank_eq_splitTorusRank_of_characterRestriction
          hrestriction hG ha).symm
  refine ⟨inferInstance, inferInstance, hT.finrank_realCocharacterSpace,
    hT.finrank_realCharacterSpace, hrank, ?_, ?_⟩
  · intro w v hv
    rw [← himage] at hv
    exact relativeWeylRealAction_eq_self_of_mem_central_range i f hc w hv
  · intro A' a' ha'
    obtain ⟨f', hf', hfc', hfinj'⟩ := ha'.exists_commFactor_of_isMaximalSplitTorus hi
    obtain ⟨hrat, hreal⟩ :=
      ha'.restriction_kernels_eq_relativeRootSpans hcentral hT f' hf'
    exact ⟨f', hf', hfc', hfinj',
      ha'.range_cocharacterMapReal_eq_relativeCentralDirections hcentral hT f' hf',
      hrat, hreal⟩

end Langlands.GroupScheme
