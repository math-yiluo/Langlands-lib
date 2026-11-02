import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Reductive.GeneralLinearRoots

/-! # Proof of `GeneralLinearRootDatumStatement` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Reducedness -/

omit [Fintype n] in
/-- Two vectors `eₐ - e_b` and `e_c - e_d` with a nontrivial integer relation are equal or
opposite. -/
theorem rootCoord_eq_or_eq_neg {a b c d : n} (hab : a ≠ b) (hcd : c ≠ d) {s t : ℤ}
    (h : s • rootCoord (a, b) + t • rootCoord (c, d) = 0) (hst : ¬(s = 0 ∧ t = 0)) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have ha := congrFun h a
  have hb := congrFun h b
  have hc := congrFun h c
  have hd := congrFun h d
  simp only [rootCoord, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul,
    Pi.zero_apply] at ha hb hc hd
  by_cases hca : c = a <;> by_cases hcb : c = b <;> by_cases hda : d = a <;>
    by_cases hdb : d = b <;> simp_all

omit [Fintype n] in
theorem rootCoord_swap_eq_neg (a b : n) : rootCoord (b, a) = -rootCoord (a, b) := by
  simp [rootCoord]

variable (k : Type u) [Field k]

/-- The root datum of `GL_n` is reduced. -/
theorem rootDatum_isReduced : (rootDatum n k).IsReduced := by
  constructor
  intro p q h
  have h' : ¬LinearIndependent ℤ ![rootCoord p.1, rootCoord q.1] := by
    intro hli
    apply h
    have h2 := hli.map' (characterCoordEquiv n k).symm.toLinearMap
      (LinearEquiv.ker _)
    convert h2 using 1
    ext i
    fin_cases i <;> rfl
  rw [LinearIndependent.pair_iff] at h'
  push Not at h'
  obtain ⟨s, t, hst, hne⟩ := h'
  have hne' : ¬(s = 0 ∧ t = 0) := fun e => hne e.1 e.2
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨c, d⟩, hcd⟩ := q
  rcases rootCoord_eq_or_eq_neg hab hcd hst hne' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rfl
  · right
    apply (characterCoordEquiv n k).injective
    rw [map_neg, characterCoordEquiv_rootDatum_root, characterCoordEquiv_rootDatum_root]
    exact (rootCoord_swap_eq_neg _ _).symm.trans rfl |>.symm.trans (by
      rw [rootCoord_swap_eq_neg, neg_neg])

/-! ### Injectivity of the permutation action -/

theorem permutationAction_injective : Function.Injective (permutationAction n k) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  ext c
  have h := congrArg (fun e => characterCoordEquiv n k
    (e ((characterCoordEquiv n k).symm (Pi.single c 1))) (w c)) hw
  simp only [characterCoordEquiv_permutationAction, LinearEquiv.apply_symm_apply,
    Equiv.Perm.coe_inv, Equiv.symm_apply_apply, Pi.single_eq_same] at h
  change 1 = characterCoordEquiv n k ((characterCoordEquiv n k).symm (Pi.single c 1)) (w c) at h
  rw [LinearEquiv.apply_symm_apply] at h
  by_contra hne
  rw [Pi.single_eq_of_ne (show w c ≠ c from hne)] at h
  exact one_ne_zero h

/-! ### The root datum -/

theorem isRootDatumOf_rootDatum :
    IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) (rootDatum n k) := by
  refine ⟨rfl, ?_, fun α => ?_⟩
  · rw [roots_diagonalTorus]
    ext χ
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1.1, p.1.2, p.2, characterLatticeEquiv_rootDatum_root p⟩
    · rintro ⟨i, j, hij, hχ⟩
      refine ⟨⟨(i, j), hij⟩, ?_⟩
      apply (splitTorus.characterLatticeEquiv k (ULift.{u} n)).injective
      rw [characterLatticeEquiv_rootDatum_root, hχ]
  · exact ⟨permPoint _ (Equiv.swap α.1.1 α.1.2), torusPerm _ (Equiv.swap α.1.1 α.1.2),
      isNormalizingPoint_permPoint _ _,
      (characterAut_torusPerm k _).trans (rootDatum_reflection α).symm⟩

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme

/-- The root datum of `GL_n` over a field (Milne, Examples 17.88, 21.6 and 21.40). -/
theorem generalLinearRootDatum : GeneralLinearRootDatumStatement.{u} := by
  intro k _ n _ _
  exact ⟨GeneralLinear.isMaximalTorus_diagonalTorus k, GeneralLinear.roots_diagonalTorus,
    GeneralLinear.isRootDatumOf_rootDatum k, GeneralLinear.rootDatum_isReduced k,
    GeneralLinear.weylImage_diagonalTorus n k, GeneralLinear.permutationAction_injective k⟩

end Langlands.GroupScheme
