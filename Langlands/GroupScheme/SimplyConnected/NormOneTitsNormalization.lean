import Langlands.GroupScheme.SimplyConnected.NormOneInnerStar
import Langlands.GroupScheme.Reductive.InnerTitsRootVanishing

/-! # First fundamental Tits classes of actual norm-one groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits

open Langlands.CentralSimple Langlands.Brauer MatrixRepresentation SplitRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : GaloisPinningData k K G) (A : CSA.{u, u} k) (model : G ≅ normOne k A)
    (chart : K ⊗[k] A ≃ₐ[K] Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) K)
    (hm : 2 ≤ reducedDegree k A)

/-- In the numbering induced by the actual chart, the first and last
fundamental weights have Brauer classes `[A]` and `-[A]`. -/
def NormOneTitsNormalizationStatement : Prop :=
  let p := d.toSplitPinning
  let hG := IsSimplyConnected.of_iso model (normOne_isSimplyConnected k A)
  let hinner := normOneInnerStar d A model chart
  let w := Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base
    (d.corootSpan_eq_top_of_simplyConnected hG)
  ∃ number : p.base.support ≃ Fin (reducedDegree k A - 1),
    let first := number.symm ⟨0, by omega⟩
    let last := number.symm ⟨reducedDegree k A - 2, by omega⟩
    (∀ a b : p.base.support, p.rootDatum.pairing a b =
      CartanMatrix.A (reducedDegree k A - 1) (number a) (number b)) ∧
    p.IsHighestWeight (representationOn A chart model) (w first) ∧
    d.innerTitsObstruction hG hinner (w first) = classOf A ∧
    d.innerTitsObstruction hG hinner (w last) = -classOf A

/-- The actual column algebra computes the first class. The endpoint sum is an
actual root, so root vanishing computes the opposite sign at the last vertex. -/
theorem normOneTitsNormalization : NormOneTitsNormalizationStatement d A model chart hm := by
  let p := d.toSplitPinning
  let b := algebraBaseMap k K
  let E := (GroupScheme.baseChange b).mapIso model ≪≫ Splitting.splittingIso k A chart
  let hG := IsSimplyConnected.of_iso model (normOne_isSimplyConnected k A)
  let hinner := normOneInnerStar d A model chart
  let hspan := d.corootSpan_eq_top_of_simplyConnected hG
  let w := Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := inferInstanceAs
    (IsAffineHom (Limits.pullback.snd G.X.hom b))
  obtain ⟨number, hcartan, hweight, hroot⟩ := p.numberedWeightsOfSpecialLinearIso hm E hspan
  let first := number.symm ⟨0, by omega⟩
  let last := number.symm ⟨reducedDegree k A - 2, by omega⟩
  have hw : p.IsHighestWeight (representationOn A chart model) (w first) := by
    simpa only [w, first, E, representationOn, representation, Iso.trans_hom,
      Functor.mapIso_hom, restrict_comp] using hweight
  have hfirst : d.innerTitsObstruction hG hinner (w first) = classOf A :=
    column_titsObstruction A chart d hG (d.fixedWeightOfInner hG hinner (w first)) model hw
  refine ⟨number, hcartan, hw, hfirst, ?_⟩
  change d.innerTitsObstruction hG hinner (w last) = -classOf A
  obtain ⟨r, hr⟩ := hroot
  have hs : d.innerTitsObstruction hG hinner (w first + w last) = 0 :=
    hr.symm ▸ d.innerTitsObstruction_root hG hinner r
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm, ← hfirst, ← map_add]
  exact hs

/-- The canonical matrix chart over the separable closure gives the full absolute normalization. -/
theorem normOneAbsoluteTitsNormalization
    (p : GaloisPinningData k (SeparableClosure k) G) (B : CSA.{u, u} k)
    (e : G ≅ normOne k B) (hB : 2 ≤ reducedDegree k B) :
    NormOneTitsNormalizationStatement p B e (separableClosureChart k B) hB :=
  normOneTitsNormalization p B e (separableClosureChart k B) hB

end Langlands.GroupScheme.CentralSimpleUnits
