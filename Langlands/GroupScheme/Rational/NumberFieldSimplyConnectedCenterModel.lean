import Langlands.GroupScheme.Rational.KleinFourCenterKernelModel
import Langlands.GroupScheme.Reductive.AbsoluteCartanClassificationProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.TypeACenterCharacters

/-! # Arithmetic models of the full centre of absolutely almost-simple groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace HasNumberFieldCentralKernelModel

variable {F : Type u} [Field F] {Y Z : GroupScheme (Spec (CommRingCat.of F))}

/-- The arithmetic kernel models are invariant under actual group isomorphism. -/
theorem of_iso (e : Y ≅ Z) (h : HasNumberFieldCentralKernelModel Z) :
    HasNumberFieldCentralKernelModel Y := by
  rcases h with ⟨n, hn, ⟨i⟩⟩ | ⟨I, _, n, hn, ⟨i⟩⟩ |
    ⟨B, _, _, _, _, n, hn, ⟨i⟩⟩ | ⟨B, _, _, _, _, n, hn, hB, ⟨i⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e ≪≫ i⟩⟩
  · exact Or.inr (Or.inl ⟨I, inferInstance, n, hn, ⟨e ≪≫ i⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
      n, hn, ⟨e ≪≫ i⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
      n, hn, hB, ⟨e ≪≫ i⟩⟩))

variable [NumberField F] {U : CommGroupScheme (Spec (CommRingCat.of F))}

local notation "Ω" => SeparableClosure F
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap F Ω)
local notation "X" => characterLattice (Functor.obj (BC) U)

private theorem of_character_card_one (hU : IsMultiplicativeType U.toGrp)
    (hcard : Nat.card X = 1) : HasNumberFieldCentralKernelModel U.toGrp := by
  let : Finite X := Nat.finite_of_card_ne_zero (hcard.trans_ne (by decide))
  let : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp (by rw [hcard])
  have hcyc : IsAddCyclic X := ⟨0, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  exact of_small_cyclic hU hcyc (by decide) (by decide) hcard

private theorem of_character_prime_card (hU : IsMultiplicativeType U.toGrp)
    {p : ℕ} (hp : p.Prime) (hp' : p ≤ 4) (hcard : Nat.card X = p) :
    HasNumberFieldCentralKernelModel U.toGrp := by
  let : Fact p.Prime := ⟨hp⟩
  have hcyc : IsAddCyclic X := isAddCyclic_of_prime_card hcard
  exact of_small_cyclic hU hcyc hp.pos hp' hcard

private theorem of_character_card_four (hU : IsMultiplicativeType U.toGrp)
    (hcard : Nat.card X = 4) : HasNumberFieldCentralKernelModel U.toGrp := by
  by_cases h : IsAddCyclic X
  · exact of_small_cyclic hU h (by decide) (by decide) hcard
  have he : Nat.card X = 2 ^ 2 := hcard.trans (by decide)
  exact of_kleinFour hU ⟨hcard, (not_isAddCyclic_iff_exponent_eq_prime (by decide) he).mp h⟩

end HasNumberFieldCentralKernelModel

namespace TitsIndexData

open Langlands.LinearAlgebra

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- Every full toral centre of an absolutely almost-simple simply connected
group over a number field has one of the arithmetic kernel models. -/
theorem toralCenter_hasNumberFieldCentralKernelModel
    (hsc : IsSimplyConnected G) (hsimple : IsAbsolutelyAlmostSimple G) :
    HasNumberFieldCentralKernelModel d.toralCenter.group.toGrp := by
  have ht := absolutelyAlmostSimpleCartanClassification F G d hsimple
  have hm := d.toralCenter_isMultiplicativeType
  rcases ht with ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ | ⟨n, hn, e, he⟩ |
    ⟨n, hn, e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact HasNumberFieldCentralKernelModel.of_cyclic_sign hm (Nat.succ_pos n)
      (d.centerCharacterEquivA hsc e he hn).symm.toAddEquiv
      (d.centerCharacter_action_sign_A hsc e he hn)
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.B n) he
    rw [cartan_B_det (by omega)] at hc
    exact HasNumberFieldCentralKernelModel.of_character_prime_card hm Nat.prime_two (by decide) hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.C n) he
    rw [cartan_C_det (by omega)] at hc
    exact HasNumberFieldCentralKernelModel.of_character_prime_card hm Nat.prime_two (by decide) hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.D n) he
    rw [cartan_D_det (by omega)] at hc
    exact HasNumberFieldCentralKernelModel.of_character_card_four hm hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.E 6) he
    rw [CartanMatrix.E₆_det] at hc
    exact HasNumberFieldCentralKernelModel.of_character_prime_card hm Nat.prime_three (by decide) hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.E 7) he
    rw [CartanMatrix.E₇_det] at hc
    exact HasNumberFieldCentralKernelModel.of_character_prime_card hm Nat.prime_two (by decide) hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e (CartanMatrix.E 8) he
    rw [CartanMatrix.E₈_det] at hc
    exact HasNumberFieldCentralKernelModel.of_character_card_one hm hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e CartanMatrix.F₄ he
    rw [CartanMatrix.F₄_det] at hc
    exact HasNumberFieldCentralKernelModel.of_character_card_one hm hc
  · have hc := d.natCard_centerCharacter_eq_cartanDet hsc e CartanMatrix.G₂ he
    rw [CartanMatrix.G₂_det] at hc
    exact HasNumberFieldCentralKernelModel.of_character_card_one hm hc

end TitsIndexData

/-- The actual full centre of any absolutely almost-simple simply connected group
over a number field is isomorphic to an arithmetic kernel model. -/
def NumberFieldSimplyConnectedFullCenterModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G Z : GroupScheme (Spec (CommRingCat.of F)))
    (i : Z ⟶ G), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      IsSchemeTheoreticCenter i → HasNumberFieldCentralKernelModel Z

theorem numberFieldSimplyConnectedFullCenterModel :
    NumberFieldSimplyConnectedFullCenterModelStatement.{u} := by
  intro F _ _ G Z i hsc hsimple hZ
  let hR := hsc.isSemisimple.isConnectedReductive
  let : IsAffineHom G.X.hom := hR.isAffineHom
  let : Smooth G.X.hom := hR.smooth
  obtain ⟨d⟩ := titsIndexExistence F G hsc.isSemisimple
  exact (d.toralCenter_hasNumberFieldCentralKernelModel hsc hsimple).of_iso (d.isoToralCenter hZ)

/-- The actual kernel of a simply connected cover of an absolutely almost-simple
adjoint number-field group has one of the arithmetic models. -/
theorem numberFieldAbsolutelyAlmostSimpleAdjointCenter :
    NumberFieldAbsolutelyAlmostSimpleAdjointCenterStatement.{u} := by
  intro F _ _ C H f hH hsimple hf
  exact numberFieldSimplyConnectedFullCenterModel F C (kernel f) (kernelι f)
    hf.isSimplyConnected
    (hf.isCentralIsogeny.isAbsolutelyAlmostSimple_source hf.isSimplyConnected.isSemisimple hsimple)
    (hf.isCentralIsogeny.isSchemeTheoreticCenter_kernelι_of_isAdjoint hH)

/-- The full published Hasse principle follows from the absolute simply
connected kernel and the quadratic isometry theorem. -/
theorem numberFieldHassePrinciple_of_absolute
    (hsc : NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u})
    (hq : NumberFieldQuadraticIsometryStatement.{u}) :
    NumberFieldHassePrincipleStatement.{u} :=
  numberFieldHassePrinciple_of_absolute_and_center hsc numberFieldAbsolutelyAlmostSimpleAdjointCenter hq

end Langlands.GroupScheme
