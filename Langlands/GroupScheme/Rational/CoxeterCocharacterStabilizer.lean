import Langlands.GroupScheme.Rational.CoxeterStandardCocharacter
import Langlands.GroupScheme.Rational.PositiveRootInduction

/-! # The actual Weyl stabilizer of a standard cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- The stabilizer of the pairing with an actual cocharacter under the
actual scheme relative-Weyl character action. -/
def cocharacterPairingWeylStabilizer (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (ζ : cocharacterLattice T) :
    Subgroup (relativeWeylGroup i) where
  carrier := {w | ∀ χ : characterLattice T,
    latticePairing T (schemeWeylCharacterAction i w χ) ζ = latticePairing T χ ζ}
  one_mem' := by simp
  mul_mem' := by
    intro v w hv hw χ
    rw [map_mul, LinearEquiv.mul_apply, hv, hw]
  inv_mem' := by
    intro w hw χ
    have h := hw (schemeWeylCharacterAction i w⁻¹ χ)
    simpa using h.symm

/-- A realized simple reflection negates its labelled actual simple root. -/
theorem IsRelativeWeylCoxeterRealization.simple_action_self
    (h : IsRelativeWeylCoxeterRealization i ν cs) (a : SimpleRoot i ν) :
    schemeWeylCharacterAction i (cs.simple a) a.1 = -a.1 := by
  obtain ⟨f, hf, ha⟩ := h.1 a
  rw [ha, hf, two_zsmul]
  abel

/-- Every element of a standard Coxeter subgroup preserves pairing with a
standard cocharacter for the corresponding face. -/
theorem IsRelativeWeylCoxeterRealization.standardSubgroup_le_pairingStabilizer
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    {I : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    standardSubgroup cs I ≤ cocharacterPairingWeylStabilizer i ζ := by
  intro w hw
  rw [h.2.2.2.2 I] at hw
  obtain ⟨n, hn, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hw
  intro χ
  apply latticePairing_weylAction_of_mem_dynamicCentralizer i n
  exact (mem_standardLevi i ν).mp hn ζ hζ

/-- The pairing stabilizer of a standard cocharacter is exactly its standard
Coxeter subgroup. A right descent forces its simple label into the face. -/
theorem IsRelativeWeylCoxeterRealization.pairingStabilizer_eq_standardSubgroup
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    {I : Finset (SimpleRoot i ν)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ) :
    cocharacterPairingWeylStabilizer i ζ = standardSubgroup cs I := by
  classical
  apply le_antisymm ?_ (h.standardSubgroup_le_pairingStabilizer hζ)
  intro w hw
  generalize hn : cs.length w = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw1 : w = 1
    · simp [hw1]
    obtain ⟨a, ha⟩ := cs.exists_rightDescent_of_ne_one hw1
    change cs.length (w * cs.simple a) < cs.length w at ha
    have hnot : schemeWeylCharacterAction i w a.1 ∉ positiveRelativeRoots i ν := by
      intro hpos
      have := (h.2.2.1 w a).mpr hpos
      omega
    have hroot := schemeWeylCharacterAction_mem_relativeRoots (i := i) w a.2.1.1
    have hnegroot : -(schemeWeylCharacterAction i w a.1) ∈ relativeRoots i := by
      have hsa := schemeWeylCharacterAction_mem_relativeRoots (i := i)
        (w * cs.simple a) a.2.1.1
      simpa only [map_mul, LinearEquiv.mul_apply, h.simple_action_self a,
        map_neg] using hsa
    have hneg : -(schemeWeylCharacterAction i w a.1) ∈ positiveRelativeRoots i ν := by
      refine ⟨hnegroot, ?_⟩
      have hne := hν _ hroot
      have hnpos : ¬0 < latticePairing T (schemeWeylCharacterAction i w a.1) ν :=
        fun hpos => hnot ⟨hroot, hpos⟩
      simp only [map_neg, LinearMap.neg_apply]
      omega
    have hnonneg := hζ.pairing_nonneg_of_positive i ν hneg
    have heq := hw a.1
    have haI : a ∈ I := by
      by_contra hnotI
      have hpos := hζ.2.2 a.1 a.2 (by
        rintro ⟨b, hb, he⟩
        have hab : b = a := Subtype.ext he
        exact hnotI (hab ▸ hb))
      simp only [map_neg, LinearMap.neg_apply] at hnonneg
      omega
    have hs := h.standardSubgroup_le_pairingStabilizer hζ
      (simple_mem_standardSubgroup cs haI)
    have hws : w * cs.simple a ∈ standardSubgroup cs I :=
      ih _ (by omega) ((cocharacterPairingWeylStabilizer i ζ).mul_mem hw hs) rfl
    have := (standardSubgroup cs I).mul_mem hws (simple_mem_standardSubgroup cs haI)
    simpa only [mul_assoc, cs.simple_mul_simple_self, mul_one] using this

end Langlands.GroupScheme
