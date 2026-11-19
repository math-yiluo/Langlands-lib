import Langlands.GroupScheme.Rational.BasedFundamentalWeightTransport
import Langlands.GroupScheme.Rational.HighestWeightIntertwiners
import Langlands.GroupScheme.Reductive.GaloisPinningIso
import Langlands.GroupScheme.Reductive.PinnedIsoAlignment
import Langlands.GroupScheme.Reductive.SpecialLinearHighestWeight
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan

/-! # Numbering the weights of an actual special-linear chart -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- A rational inner correction on the comparison group preserves the highest weight
of the pullback to the source with its original chosen torus. -/
theorem isHighestWeight_restrict_of_innerComp
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type} [Fintype I] [DecidableEq I]
    (E : G ≅ H) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    {ρ : MatrixRepresentation H I} {lam : characterLattice p.torus}
    (hρ : p.IsHighestWeight (ρ.restrict (E ≪≫ H.innerIso g).hom) lam) :
    p.IsHighestWeight (ρ.restrict E.hom) lam := by
  let C := ρ.rationalMatrix g
  have hC : Intertwines (ρ.restrict E.hom) (ρ.restrict (E ≪≫ H.innerIso g).hom)
      (C : Matrix I I k) := by
    intro S x
    rw [affineMatrix_restrict, affineMatrix_restrict]
    simp only [Iso.trans_hom, Grp.comp_hom_hom]
    rw [← Category.assoc, comp_innerIso_hom, map_mul, map_mul, map_inv,
      affineMatrix_constantPoint]
    let U := Matrix.GeneralLinearGroup.map (algebraMap k S) C
    change (U : Matrix I I S) * _ =
      ((U * ρ.affineMatrix S (x ≫ E.hom.hom.hom) * U⁻¹ : GL I S) : Matrix I I S) * U
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  have hb : Function.Bijective (C : Matrix I I k).mulVecLin :=
    (Matrix.GeneralLinearGroup.toLin C).toLinearEquiv.bijective
  obtain ⟨D, hD, hbD⟩ := hC.exists_inverse hb
  exact hρ.of_intertwines hD hbD

/-- The numbered type-A vertices and the two endpoint weights of the pulled-back
column chart on the supplied split pinning. -/
def NumberedWeightsOfSpecialLinearIsoStatement {m : ℕ} (hm : 2 ≤ m)
    (E : G ≅ SpecialLinear.groupScheme (Fin m) (CommRingCat.of k))
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) : Prop :=
  ∃ number : p.base.support ≃ Fin (m - 1),
    let w := Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan
    let first := number.symm ⟨0, by omega⟩
    let last := number.symm ⟨m - 2, by omega⟩
    (∀ a b : p.base.support, p.rootDatum.pairing a b =
      CartanMatrix.A (m - 1) (number a) (number b)) ∧
    p.IsHighestWeight
      (MatrixRepresentation.restrict (SpecialLinear.inclusion (Fin m) (CommRingCat.of k))
        E.hom) (w first) ∧
    ∃ r : p.rootIndex, w first + w last = p.rootDatum.root r

/-- An actual chart supplies the adjacent-root numbering on any split pinning
by rational inner alignment. The first weight is realized by the original column
chart and the sum of the endpoint weights is an actual root. -/
theorem numberedWeightsOfSpecialLinearIso {m : ℕ} (hm : 2 ≤ m)
    (E : G ≅ SpecialLinear.groupScheme (Fin m) (CommRingCat.of k))
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) :
    p.NumberedWeightsOfSpecialLinearIsoStatement hm E hspan := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hm
  have hsize : m = n + 1 + 1 := by omega
  clear hn
  subst m
  open SpecialLinear.FinSucc in
  obtain ⟨J, hJ, P, hP, hred, B, num, hspanQ, hnum, hcartan⟩ :=
    exists_coordinateRootDatum (n + 1) k
  let : Finite J := hJ
  let q := SpecialLinear.FinSucc.coordinatePinning P hP hred B
  obtain ⟨g, φ, e, ht, he, hb⟩ := p.exists_inner_comp_based q E
  let s := e.indexEquiv.subtypeEquiv hb
  let number : p.base.support ≃ Fin (n + 1) := s.trans num
  let a := number.symm 0
  let b := number.symm (Fin.last n)
  have ha : s a = num.symm 0 := s.apply_symm_apply (num.symm 0)
  have hb' : s b = num.symm (Fin.last n) := s.apply_symm_apply (num.symm (Fin.last n))
  have hwa (c : p.base.support) :
      e.weightEquiv (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan c) =
        Langlands.RootDatum.fundamentalWeightBasis P B hspanQ (s c) :=
    p.weightEquiv_fundamentalWeightBasis q e hb hspan hspanQ c
  refine ⟨number, ?_, ?_, ?_⟩
  · intro i j
    exact (e.toHom.pairing (i := (i : p.rootIndex)) (j := (j : p.rootIndex))).symm.trans
      (hcartan (s i) (s j))
  · change p.IsHighestWeight _ (Langlands.RootDatum.fundamentalWeightBasis _ _ hspan a)
    apply p.isHighestWeight_restrict_of_innerComp E g
    have he' (χ : characterLattice p.torus) : e.weightMap χ = characterLattice.congr φ χ :=
      he χ
    apply (isHighestWeight_restrict_iso_iff (E ≪≫ _) φ ht e he' hb _ _).mpr
    change q.IsHighestWeight _ (e.weightEquiv
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a))
    rw [hwa a, ha, SpecialLinear.FinSucc.first_fundamentalWeightBasis hP B num hnum hspanQ]
    exact SpecialLinear.FinSucc.inclusion_isHighestWeight P hP hred B num hnum
  · have hne : (0 : Fin (n + 1 + 1)) ≠ Fin.last (n + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    obtain ⟨j, hj⟩ := (SpecialLinear.FinSucc.mem_range_root_iff hP
      (SpecialLinear.FinSucc.rootChar (n + 1) k 0 (Fin.last (n + 1)))).mpr
        ⟨0, Fin.last (n + 1), hne, rfl⟩
    refine ⟨e.indexEquiv.symm j, ?_⟩
    apply e.weightEquiv.injective
    change e.weightEquiv (Langlands.RootDatum.fundamentalWeightBasis _ _ hspan a +
      Langlands.RootDatum.fundamentalWeightBasis _ _ hspan b) =
        e.weightMap (p.rootDatum.root (e.indexEquiv.symm j))
    rw [map_add, hwa a, hwa b, ha, hb',
      SpecialLinear.FinSucc.first_fundamentalWeightBasis hP B num hnum hspanQ,
      SpecialLinear.FinSucc.last_fundamentalWeightBasis hP B num hnum hspanQ,
      e.toHom.root_weightMap_apply p.rootDatum q.rootDatum, Equiv.apply_symm_apply]
    change _ = P.root j
    rw [hj,
      SpecialLinear.FinSucc.rootChar_eq_weightChar_sub, sub_eq_add_neg]

end Langlands.GroupScheme.SplitPinning
