import Langlands.Representation.CuspidalSupport.AdjacentDualTransport
import Langlands.Representation.Classification.IncreasingAdjacentQuotientUpperProductIrreducibility

/-! Products of the decreasing adjacent subrepresentation with either factor. -/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Either repeated factor preserves irreducibility of the actual proper
subrepresentation of the decreasing adjacent product. -/
def DecreasingAdjacentSubrepresentationRepeatedProducts : Prop :=
  letI := T.topology
  ∀ (d : ℕ) (hd : 0 < d)
    (B A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := d)),
    A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass →
    let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd A.obj B.obj)
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      let L := SmoothRep.subrepresentation P S
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks (d+d) d (by omega) hd)).obj
        (twoBlockFactors (by omega) hd L A.obj)).IsIrreducible ∧
      ((T.normalizedProductInductionFunctor
        (Shahidi.twoBlocks (d+d) d (by omega) hd)).obj
        (twoBlockFactors (by omega) hd L B.obj)).IsIrreducible

/-- Transfer the supplied-quotient upper-factor theorem through the actual
adjacent factor comparison, and then through actual smooth duality. -/
theorem decreasingAdjacentSubrepresentationRepeatedProducts :
    DecreasingAdjacentSubrepresentationRepeatedProducts.{uF,uV} F T := by
  let := T.topology
  let (r : ℕ) := T.generalLinearTopologicalGroup r
  intro d hd B A hAB P S hS₀ hS₁ L
  have hPred : ¬ P.IsIrreducible := by
    intro h
    rcases h.eq_bot_or_eq_top S with h | h
    · exact hS₀ h
    · exact hS₁ h
  have hstr := TwoSupercuspidalAdjacent.adjacentStructure F T hd
    (nonassociatedJacquetSubquotients F T (d+d))
    (associatedJacquetFiltration F T (d+d)) A B (Or.inr hAB)
  have hLi : L.IsIrreducible := ((hstr.1 hPred).2.2 S hS₀ hS₁).1
  have hLa : L.IsAdmissible := (cuspidalEmbedding F T (d+d) L hLi).1
  have hdd : 0 < d+d := by omega
  constructor
  · obtain ⟨U,hU₀,hU₁⟩ :=
      decreasingProper_exists_increasingProper.{uF,uV} F T hd B A hAB S hS₀ hS₁
    obtain ⟨e⟩ :=
      decreasingSubrepresentation_equiv_increasingQuotient.{uF,uV} F T hd B A hAB
        S U hS₀ hS₁ hU₀ hU₁
    let R := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd B.obj A.obj)
    let eL : L ≅ SmoothRep.quotient R U :=
      SmoothRep.mkIso (A := L) (B := SmoothRep.quotient R U) e
    have hQ := increasingAdjacentQuotientUpperProductIrreducibility.{uF,uV}
      F T d hd B A hAB U hU₀ hU₁
    have hM := JacquetLength.isIrreducible_of_equiv
      (SmoothRep.equivOfIso
        ((T.binaryNormalizedProductFunctor (d+d) d).mapIso
          (Iso.prod eL (Iso.refl A.obj))).symm) hQ
    rw [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks F T hdd hd] at hM
    exact hM
  · let DA := CuspidalProductContragredient.dualRep T A
    let DB := CuspidalProductContragredient.dualRep T B
    let R := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks d d hd hd)).obj
      (twoBlockFactors hd hd DA.obj DB.obj)
    have hRrel := dualRep_adjacent_reverse.{max uF uV,uF} F T B A hAB
    have hPa : P.IsAdmissible :=
      twoFactorProduct_admissible F T hd hd A.obj B.obj A.property.2.1 B.property.2.1
    let eP : P.contragredient ≅ R :=
      twoFactorProduct_contragredientIso.{uV,uF} F T hd hd A.obj B.obj A.property.2.1 B.property.2.1
    obtain ⟨U,hU₀,hU₁,⟨eQ⟩⟩ :=
      dualSubrepresentation_exists_quotient (compactOpen_cofinal F T (d+d))
        P R S hPa hPred hLi hLa eP
    have hQ := increasingAdjacentQuotientUpperProductIrreducibility.{uF,uV}
      F T d hd DA DB hRrel U hU₀ hU₁
    let eL : SmoothRep.quotient R U ≅ L.contragredient :=
      SmoothRep.mkIso (A := SmoothRep.quotient R U) (B := L.contragredient) eQ
    have hMd := JacquetLength.isIrreducible_of_equiv
      (SmoothRep.equivOfIso
        ((T.binaryNormalizedProductFunctor (d+d) d).mapIso
          (Iso.prod eL (Iso.refl DB.obj)))) hQ
    rw [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks F T hdd hd] at hMd
    let M := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks (d+d) d hdd hd)).obj
      (twoBlockFactors hdd hd L B.obj)
    have hMa : M.IsAdmissible :=
      twoFactorProduct_admissible F T hdd hd L B.obj hLa B.property.2.1
    let eM := twoFactorProduct_contragredientIso.{uV,uF} F T hdd hd L B.obj hLa B.property.2.1
    have hMdi : M.contragredient.IsIrreducible :=
      JacquetLength.isIrreducible_of_equiv (SmoothRep.equivOfIso eM.symm) hMd
    exact (SmoothRep.isIrreducible_contragredient_iff
      (compactOpen_cofinal F T ((d+d)+d)) M hMa).mp hMdi

end Langlands.CuspidalSupport
