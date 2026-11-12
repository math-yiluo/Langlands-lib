import Langlands.GroupScheme.SymplecticMatrix.RootSystem
import Langlands.GroupScheme.Rational.RelativeRoots

/-! # The type `C` root data of the split symplectic group in coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

variable (l k) in
/-- The coordinate character `e_a : diag(t, t⁻¹) ↦ t_a`. -/
def coordChar (a : l) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv l k).symm (Pi.single a 1)

variable (l k) in
/-- The coordinate cocharacter `e_a^∨ : s ↦ diag(t, t⁻¹)` with `t_a = s` and `t_c = 1` for
`c ≠ a`. -/
def coordCochar (a : l) : cocharacterLattice 𝔻 :=
  (GeneralLinear.cocharacterCoordEquiv l k).symm (Pi.single a 1)

theorem characterCoordEquiv_coordChar (a : l) :
    GeneralLinear.characterCoordEquiv l k (coordChar l k a) = Pi.single a 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem cocharacterCoordEquiv_coordCochar (a : l) :
    GeneralLinear.cocharacterCoordEquiv l k (coordCochar l k a) = Pi.single a 1 :=
  LinearEquiv.apply_symm_apply _ _

/-- The coordinate characters and cocharacters are dual bases. -/
theorem latticePairing_coordChar_coordCochar (a c : l) :
    latticePairing 𝔻 (coordChar l k a) (coordCochar l k c) = if a = c then 1 else 0 := by
  rw [GeneralLinear.latticePairing_coord, characterCoordEquiv_coordChar,
    cocharacterCoordEquiv_coordCochar,
    Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul]) (by simp),
    Pi.single_eq_same, one_mul, Pi.single_apply]

/-- The long root `2e_a` is twice the coordinate character `e_a`. -/
theorem two_smul_coordChar (a : l) : 2 • coordChar l k a = longRoot l k a := by
  apply (GeneralLinear.characterCoordEquiv l k).injective
  rw [map_nsmul, characterCoordEquiv_coordChar, characterCoordEquiv_longRoot]
  funext c
  simp only [Pi.smul_apply, Pi.single_apply, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> omega

/-- The long roots `2e_a` are roots. -/
theorem two_smul_coordChar_mem_roots (a : l) :
    2 • coordChar l k a ∈ relativeRoots (diagonalTorus l (CommRingCat.of k)) := by
  rw [two_smul_coordChar]
  exact longRoot_mem_roots a

/-- For `a ≠ b`, the short roots `e_b - e_a` and `-e_a - e_b` are roots. -/
theorem short_mem_roots {a b : l} (hab : a ≠ b) :
    coordChar l k b - coordChar l k a ∈ relativeRoots (diagonalTorus l (CommRingCat.of k)) ∧
      -coordChar l k a - coordChar l k b ∈
        relativeRoots (diagonalTorus l (CommRingCat.of k)) := by
  have h1 : coordChar l k b - coordChar l k a = diffRoot l k b a := by
    apply (GeneralLinear.characterCoordEquiv l k).injective
    rw [map_sub, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar,
      characterCoordEquiv_diffRoot]
  have h2 : -coordChar l k a - coordChar l k b = -sumRoot l k a b := by
    rw [← neg_add']
    congr 1
    apply (GeneralLinear.characterCoordEquiv l k).injective
    rw [map_add, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar,
      characterCoordEquiv_sumRoot]
  rw [h1, h2]
  exact ⟨diffRoot_mem_roots (Ne.symm hab), neg_mem_roots (sumRoot_mem_roots hab)⟩

/-- **The roots of type `C`.** Every root is `±2e_a`, or `e_b - e_a`, `-e_a - e_b` or
`e_a + e_b` for some `a ≠ b`. -/
theorem roots_typeC :
    ∀ χ ∈ relativeRoots (diagonalTorus l (CommRingCat.of k)),
      (∃ a, χ = 2 • coordChar l k a ∨ χ = -(2 • coordChar l k a)) ∨
        ∃ a b, a ≠ b ∧ (χ = coordChar l k b - coordChar l k a ∨
          χ = -coordChar l k a - coordChar l k b ∨ χ = coordChar l k a + coordChar l k b) := by
  intro χ hχ
  obtain ⟨x, y, hne, hxy⟩ := (mem_roots_iff χ).mp hχ
  have key : ∀ ψ : characterLattice 𝔻,
      GeneralLinear.characterCoordEquiv l k ψ = weightCoord l x - weightCoord l y → χ = ψ :=
    fun ψ hψ => (GeneralLinear.characterCoordEquiv l k).injective (hxy.trans hψ.symm)
  rcases x with a | a <;> rcases y with b | b
  · have hab : a ≠ b := fun h => hne (congrArg Sum.inl h)
    refine Or.inr ⟨b, a, Ne.symm hab, Or.inl (key _ ?_)⟩
    rw [map_sub, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar, weightCoord_inl,
      weightCoord_inl]
  · by_cases hab : a = b
    · subst hab
      refine Or.inl ⟨a, Or.inl (key _ ?_)⟩
      rw [two_smul_coordChar, characterCoordEquiv_longRoot, weightCoord_inl_sub_inr]
    · refine Or.inr ⟨a, b, hab, Or.inr (Or.inr (key _ ?_))⟩
      rw [map_add, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar, weightCoord_inl,
        weightCoord_inr, Pi.single_neg, sub_neg_eq_add]
  · by_cases hab : a = b
    · subst hab
      refine Or.inl ⟨a, Or.inr (key _ ?_)⟩
      rw [map_neg, two_smul_coordChar, characterCoordEquiv_longRoot, ← neg_sub,
        weightCoord_inl_sub_inr]
    · refine Or.inr ⟨a, b, hab, Or.inr (Or.inl (key _ ?_))⟩
      rw [map_sub, map_neg, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar,
        weightCoord_inl, weightCoord_inr, Pi.single_neg]
  · have hab : a ≠ b := fun h => hne (congrArg Sum.inr h)
    refine Or.inr ⟨a, b, hab, Or.inl (key _ ?_)⟩
    rw [map_sub, characterCoordEquiv_coordChar, characterCoordEquiv_coordChar, weightCoord_inr,
      weightCoord_inr, Pi.single_neg, Pi.single_neg, sub_neg_eq_add, neg_add_eq_sub]

/-- **Long coroots.** In a root datum of the diagonal torus, the coroot of `2e_a` is `e_a^∨`. -/
theorem coroot_eq_coordCochar {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus l (CommRingCat.of k)) P) :
    ∀ r a, P.root r = 2 • coordChar l k a → P.coroot r = coordCochar l k a := by
  intro r a h
  rw [two_smul_coordChar] at h
  apply (GeneralLinear.cocharacterCoordEquiv l k).injective
  rw [cocharacterCoordEquiv_coroot_of_root_eq_longRoot hP h, cocharacterCoordEquiv_coordCochar]

end Langlands.GroupScheme.SymplecticMatrix
