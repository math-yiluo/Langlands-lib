import Langlands.GroupScheme.Reductive.AlmostAllPlacesQuasiSplitStatement
import Langlands.GroupScheme.RelativeLevi.HenselianQuasiSplitStatement
import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.IntegralModel.ArithmeticReductiveSpreading
import Langlands.GroupScheme.Reductive.GenericSpreadingProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.Global.IntegralModelCompletions
import Langlands.Global.CompletionIntegersSmoothPointLifting
import Langlands.Global.CompletionResidueAdic

/-! # Quasi-splitness at almost all places from henselian quasi-splitness

The quasi-splitness clause of `AlmostAllPlacesQuasiSplitStatement` follows from
`HenselianFiniteResidueQuasiSplitStatement`: spread the group out to a reductive model over a
ring of `S`-integers, base change the model to the completed integers at a place outside `S`,
take a Borel subgroup there and restrict it to the generic fibre.
-/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global
open Langlands.GroupScheme.IntegralModel.ArithmeticSpreading
open scoped NumberField

namespace Langlands.GroupScheme

/-- Reduction of the quasi-splitness clause of `AlmostAllPlacesQuasiSplitStatement` to
`HenselianFiniteResidueQuasiSplitStatement`: if reductive group schemes over henselian local
rings with finite residue field are quasi-split, then every connected reductive group over a
number field `F` is quasi-split over `F_v` for all but finitely many finite places `v`. -/
def AlmostAllPlacesQuasiSplitClauseReductionStatement : Prop :=
  HenselianFiniteResidueQuasiSplitStatement.{u} →
    ∀ (F : Type u) [Field F] [NumberField F]
      (G : GroupScheme (Spec (CommRingCat.of F))),
      IsConnectedReductive G →
        ∀ᶠ v in Filter.cofinite (α := FinitePlace F),
          IsQuasiSplit
            ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap F (FiniteCompletion F v))))).obj G)

namespace AlmostAllPlacesQuasiSplitReduction

variable (F : Type u) [Field F] [NumberField F]

/-- The completed integer ring at a finite place is a henselian local ring. -/
theorem henselianLocalRing_adicCompletionIntegers (v : FinitePlace F) :
    HenselianLocalRing (v.adicCompletionIntegers F) :=
  adicCompletionIntegers_henselian (𝓞 F) F v

/-- Given henselian quasi-splitness, the base change of a connected reductive group to the
completion `F_v` is quasi-split at every finite place `v` outside the places of its
arithmetic reductive model `reductiveModelData`. -/
theorem eventually_isQuasiSplit (hH : HenselianFiniteResidueQuasiSplitStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    ∀ᶠ v in Filter.cofinite (α := FinitePlace F),
      IsQuasiSplit
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap F (FiniteCompletion F v))))).obj G) := by
  let D := reductiveModelData F genericReductivitySpreading G hG
  rw [Filter.eventually_cofinite]
  refine D.places.finite_toSet.subset ?_
  intro v hv
  by_contra hvS
  apply hv
  let w : {v : FinitePlace F // v ∉ D.places} := ⟨v, hvS⟩
  let N := IntegralModelCompletions.model F D.places w D.model
  let : HenselianLocalRing (v.adicCompletionIntegers F) :=
    henselianLocalRing_adicCompletionIntegers F v
  have hred : IsReductive N.group := D.reductive.baseChange _
  obtain ⟨-, B, i, hi⟩ := (hH (v.adicCompletionIntegers F) N.group hred).1
  have hgeo := hi.fieldPoint hred
    (Spec.algebraMap (v.adicCompletionIntegers F) (FiniteCompletion F v))
  have hq : IsQuasiSplit N.genericFibre :=
    ⟨hred.isConnectedReductive_algebraMap _, _, _, hgeo⟩
  exact hq.of_iso N.genericIso.symm

end AlmostAllPlacesQuasiSplitReduction

/-- The quasi-splitness clause of `AlmostAllPlacesQuasiSplitStatement` follows from
`HenselianFiniteResidueQuasiSplitStatement`. -/
theorem almostAllPlacesQuasiSplitClauseReduction :
    AlmostAllPlacesQuasiSplitClauseReductionStatement.{u} :=
  fun hH F _ _ G hG => AlmostAllPlacesQuasiSplitReduction.eventually_isQuasiSplit F hH G hG

end Langlands.GroupScheme
