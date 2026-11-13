import Langlands.GroupScheme.SymplecticMatrix.TypeC
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.LinearAlgebra.RootDatumCoweightFace
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # A simply connected split pinning of type `C_n` of the symplectic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsAddIndecomposable

namespace Langlands.GroupScheme.SymplecticMatrix

/-! ### Short coroots -/

section ShortCoroot

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]

local notation "𝕃" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- Pairing a coordinate vector with `e_p - e_q`. -/
theorem sum_mul_single_sub_single (f : l → ℤ) (p q : l) :
    ∑ c, f c * (Pi.single p 1 - Pi.single q 1 : l → ℤ) c = f p - f q := by
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single p (fun c _ hc => by rw [Pi.single_eq_of_ne hc, mul_zero]) (by simp),
    Finset.sum_eq_single q (fun c _ hc => by rw [Pi.single_eq_of_ne hc, mul_zero]) (by simp)]
  simp

/-- The coordinates of `2e_c - m (e_a - e_b)`. -/
theorem characterCoordEquiv_longRoot_sub_diffRoot (c a b : l) (m : ℤ) (d : l) :
    GeneralLinear.characterCoordEquiv l k (longRoot l k c - m • diffRoot l k a b) d =
      (if d = c then 2 else 0) - m * ((if d = a then 1 else 0) - (if d = b then 1 else 0)) := by
  rw [map_sub, map_zsmul, characterCoordEquiv_longRoot, characterCoordEquiv_diffRoot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

/-- **Short coroots.** In a root datum of the diagonal torus, the coroot of the short root
`e_a - e_b` is `e_a^∨ - e_b^∨`. -/
theorem cocharacterCoordEquiv_coroot_of_root_eq_diffRoot {J : Type u}
    {P : RootDatum J (characterLattice 𝕃) (cocharacterLattice 𝕃)}
    (hP : IsRootDatumOf (diagonalTorus l (CommRingCat.of k)) P) {j : J} {a b : l}
    (hab : a ≠ b) (hj : P.root j = diffRoot l k a b) :
    GeneralLinear.cocharacterCoordEquiv l k (P.coroot j) = Pi.single a 1 - Pi.single b 1 := by
  obtain ⟨ν, hν⟩ : ∃ ν, GeneralLinear.cocharacterCoordEquiv l k (P.coroot j) = ν := ⟨_, rfl⟩
  have hpair : ∀ j', P.pairing j' j = latticePairing 𝕃 (P.root j') (P.coroot j) := fun j' => by
    rw [← P.root_coroot_eq_pairing, hP.1]
  -- `⟨e_a - e_b, ν⟩ = 2`
  have h2 : ν a - ν b = 2 := by
    have h := hpair j
    rw [P.pairing_same, hj, GeneralLinear.latticePairing_coord, characterCoordEquiv_diffRoot,
      hν] at h
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at h
    rw [Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul])
        (by simp),
      Finset.sum_eq_single b (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul])
        (by simp)] at h
    simp only [Pi.single_eq_same, one_mul] at h
    omega
  -- the reflection of the long root `2e_c` in `e_a - e_b`
  have hmem : ∀ c : l, longRoot l k c - (2 * ν c) • diffRoot l k a b ∈
      roots (diagonalTorus l (CommRingCat.of k)) := by
    intro c
    obtain ⟨jc, hjc⟩ : longRoot l k c ∈ Set.range P.root := by
      rw [hP.2.1]
      exact longRoot_mem_roots c
    have hm : P.root (P.reflectionPerm j jc) ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
      rw [← hP.2.1]
      exact ⟨_, rfl⟩
    rw [P.root_reflectionPerm, P.reflection_apply_root, hjc, hj] at hm
    have hc := hpair jc
    rw [hjc, latticePairing_longRoot, hν] at hc
    rwa [hc] at hm
  have hcoord := fun c d => characterCoordEquiv_longRoot_sub_diffRoot (k := k) c a b (2 * ν c) d
  have hba : b ≠ a := Ne.symm hab
  -- `ν a ≤ 1`: coordinate `b` of the reflection of `2e_a`
  have ha1 : ν a ≤ 1 := by
    have h := (coord_mem_Icc_of_mem_roots (hmem a) b).2
    rw [hcoord, ite_eq_right hba, ite_eq_right hba, ite_eq_left rfl] at h
    omega
  -- `ν b ≥ -1`: coordinate `a` of the reflection of `2e_b`
  have hb1 : -1 ≤ ν b := by
    have h := (coord_mem_Icc_of_mem_roots (hmem b) a).2
    rw [hcoord, ite_eq_right hab, ite_eq_left rfl, ite_eq_right hab] at h
    omega
  rw [hν]
  funext d
  simp only [Pi.sub_apply, Pi.single_apply]
  by_cases hda : d = a
  · subst hda
    rw [ite_eq_left rfl, ite_eq_right hab]
    omega
  by_cases hdb : d = b
  · subst hdb
    rw [ite_eq_right hba, ite_eq_left rfl]
    omega
  rw [ite_eq_right hda, ite_eq_right hdb]
  -- the reflection of `2e_d` has coordinate `2` at `d`, so it is `2e_d`
  have hd2 : GeneralLinear.characterCoordEquiv l k
      (longRoot l k d - (2 * ν d) • diffRoot l k a b) d = 2 := by
    rw [hcoord, ite_eq_left rfl, ite_eq_right hda, ite_eq_right hdb]
    ring
  have h := congrFun (eq_single_two_of_mem_roots (hmem d) hd2) a
  rw [hcoord, ite_eq_right (Ne.symm hda), ite_eq_left rfl, ite_eq_right hab, Pi.single_eq_of_ne (Ne.symm hda)] at h
  omega

end ShortCoroot

namespace TypeCPinning

/-! ### Integer bookkeeping -/

variable {n : ℕ}

/-- The value `n - a` on `e_a` and `a - n` on `-e_a` of the regular cocharacter. -/
def wHeight : Fin n ⊕ Fin n → ℤ :=
  Sum.elim (fun a => (n : ℤ) - ((a : ℕ) : ℤ)) (fun a => ((a : ℕ) : ℤ) - n)

@[simp] theorem wHeight_inl (a : Fin n) : wHeight (Sum.inl a) = (n : ℤ) - ((a : ℕ) : ℤ) := rfl

@[simp] theorem wHeight_inr (a : Fin n) : wHeight (Sum.inr a) = ((a : ℕ) : ℤ) - n := rfl

theorem sum_weightCoord_mul (x : Fin n ⊕ Fin n) :
    ∑ c : Fin n, weightCoord (Fin n) x c * ((n : ℤ) - ((c : ℕ) : ℤ)) = wHeight x := by
  rcases x with a | a
  · rw [weightCoord_inl, Finset.sum_eq_single a
      (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul]) (by simp)]
    simp
  · rw [weightCoord_inr, Finset.sum_eq_single a
      (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_mul]) (by simp)]
    simp only [Pi.single_eq_same, wHeight_inr]
    ring

theorem wHeight_injective : Function.Injective (wHeight (n := n)) := by
  intro x y h
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [wHeight_inl, wHeight_inr] at h <;> have := a.isLt <;> have := b.isLt
  · exact congrArg _ (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg _ (Fin.ext (by omega))

/-- The second weight of the `i`-th simple root: `e_{i+1}` for `i + 1 < n`, else `-e_i`. -/
def simpleSnd (i : Fin n) : Fin n ⊕ Fin n :=
  if h : (i : ℕ) + 1 < n then Sum.inl ⟨i + 1, h⟩ else Sum.inr i

theorem inl_ne_simpleSnd (i : Fin n) : (Sum.inl i : Fin n ⊕ Fin n) ≠ simpleSnd i := by
  unfold simpleSnd
  split_ifs with h
  · intro h'
    have := congrArg Fin.val (Sum.inl_injective h')
    simp at this
  · exact Sum.inl_ne_inr

theorem wHeight_simple (i : Fin n) :
    wHeight (Sum.inl i) - wHeight (simpleSnd i) = if (i : ℕ) + 1 < n then 1 else 2 := by
  unfold simpleSnd
  have := i.isLt
  split_ifs with h <;> simp only [wHeight_inl, wHeight_inr] <;> omega

/-- The simple roots are pairwise distinct. -/
theorem simple_injective {i i' : Fin n}
    (h : weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i) =
      weightCoord (Fin n) (Sum.inl i') - weightCoord (Fin n) (simpleSnd i')) : i = i' := by
  by_contra hne
  have h1 := congrFun h i
  have h2 := congrFun h i'
  have hi := i.isLt
  have hi' := i'.isLt
  have hv : (i : ℕ) ≠ i' := fun h => hne (Fin.ext h)
  unfold simpleSnd at h1 h2
  split_ifs at h1 h2 <;>
    simp only [Pi.sub_apply, weightCoord_inl, weightCoord_inr, Pi.single_apply, Fin.ext_iff]
      at h1 h2 <;>
    split_ifs at h1 h2 <;> omega

/-- A weight difference of regular value `1` has nonpositive coordinate at the last index. -/
theorem coord_last_nonpos {x y : Fin n ⊕ Fin n} (h : wHeight x - wHeight y = 1) (i : Fin n)
    (hi : (i : ℕ) + 1 = n) :
    (weightCoord (Fin n) x - weightCoord (Fin n) y) i ≤ 0 := by
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [wHeight_inl, wHeight_inr, Pi.sub_apply, weightCoord_inl, weightCoord_inr,
      Pi.single_apply, Fin.ext_iff] at h ⊢ <;>
    have := a.isLt <;> have := b.isLt <;> split_ifs <;> omega

/-! ### Simple roots over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

variable (n k) in
/-- The regular cocharacter with coordinates `c ↦ n - c`. -/
def regularCochar : cocharacterLattice 𝔻 :=
  (GeneralLinear.cocharacterCoordEquiv (Fin n) k).symm (fun c => (n : ℤ) - ((c : ℕ) : ℤ))

theorem latticePairing_regularCochar {χ : characterLattice 𝔻} {x y : Fin n ⊕ Fin n}
    (h : GeneralLinear.characterCoordEquiv (Fin n) k χ =
      weightCoord (Fin n) x - weightCoord (Fin n) y) :
    latticePairing 𝔻 χ (regularCochar n k) = wHeight x - wHeight y := by
  rw [GeneralLinear.latticePairing_coord, regularCochar, LinearEquiv.apply_symm_apply, h]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sum_weightCoord_mul]

theorem exists_root_eq {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P) (j : J) :
    ∃ x y : Fin n ⊕ Fin n, x ≠ y ∧ GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
      weightCoord (Fin n) x - weightCoord (Fin n) y :=
  (mem_roots_iff _).mp (by rw [← hP.2.1]; exact ⟨j, rfl⟩)

theorem exists_root_of_ne {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P)
    {x y : Fin n ⊕ Fin n} (hxy : x ≠ y) :
    ∃ j : J, GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
      weightCoord (Fin n) x - weightCoord (Fin n) y := by
  have hmem : (GeneralLinear.characterCoordEquiv (Fin n) k).symm
      (weightCoord (Fin n) x - weightCoord (Fin n) y) ∈
        roots (diagonalTorus (Fin n) (CommRingCat.of k)) :=
    (mem_roots_iff _).mpr ⟨x, y, hxy, LinearEquiv.apply_symm_apply _ _⟩
  rw [← hP.2.1] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, by rw [hj, LinearEquiv.apply_symm_apply]⟩

theorem root'_regularCochar {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P)
    {j : J} {x y : Fin n ⊕ Fin n}
    (hj : GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
      weightCoord (Fin n) x - weightCoord (Fin n) y) :
    P.root' j (regularCochar n k) = wHeight x - wHeight y := by
  change P.toLinearMap (P.root j) (regularCochar n k) = _
  rw [hP.1, latticePairing_regularCochar hj]

theorem root'_regularCochar_ne_zero {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P) (j : J) :
    P.root' j (regularCochar n k) ≠ 0 := by
  obtain ⟨x, y, hxy, hj⟩ := exists_root_eq hP j
  rw [root'_regularCochar hP hj, sub_ne_zero]
  exact fun h => hxy (wHeight_injective h)

/-- **Simple roots.** For the regular cocharacter `c ↦ n - c`, the indecomposable positive
roots are `e_i - e_{i+1}` for `i + 1 < n` and `2e_{n-1}`. -/
theorem mem_baseOf_iff {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P) (j : J) :
    j ∈ baseOf P.root ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ) ↔
      ∃ i : Fin n, GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
        weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i) := by
  have hval : ∀ i : J, ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ) (P.root i) =
      P.root' i (regularCochar n k) := fun i => rfl
  change IsAddIndecomposable P.root _ j ↔ _
  constructor
  · rintro ⟨hpos, hind⟩
    obtain ⟨x, y, hxy, hj⟩ := exists_root_eq hP j
    have hpos' : 0 < P.root' j (regularCochar n k) := by
      simpa only [Set.mem_ofPred_eq, hval] using hpos
    rw [root'_regularCochar hP hj] at hpos'
    have hgap : ∀ z : Fin n ⊕ Fin n, wHeight y < wHeight z → wHeight z < wHeight x → False := by
      intro z hzy hxz
      have hxz' : x ≠ z := fun h => by rw [h] at hxz; exact lt_irrefl _ hxz
      have hzy' : z ≠ y := fun h => by rw [h] at hzy; exact lt_irrefl _ hzy
      obtain ⟨j1, hj1⟩ := exists_root_of_ne hP hxz'
      obtain ⟨j2, hj2⟩ := exists_root_of_ne hP hzy'
      have h1 : j1 ∈ {i | 0 < ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ)
          (P.root i)} := by
        simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hj1]
        linarith
      have h2 : j2 ∈ {i | 0 < ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ)
          (P.root i)} := by
        simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hj2]
        linarith
      have hsum : P.root j = P.root j1 + P.root j2 := by
        apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
        rw [map_add, hj, hj1, hj2]
        abel
      rcases hind j1 h1 j2 h2 hsum with h | h
      · exact P.ne_zero j1 h
      · exact P.ne_zero j2 h
    rcases x with a | a <;> rcases y with b | b <;>
      simp only [wHeight_inl, wHeight_inr] at hpos'
    · -- `e_a - e_b`
      have hb := b.isLt
      have hab : (b : ℕ) = a + 1 := by
        by_contra hne
        exact hgap (Sum.inl ⟨a + 1, by omega⟩) (by simp only [wHeight_inl]; push_cast; omega)
          (by simp only [wHeight_inl]; push_cast; omega)
      refine ⟨a, ?_⟩
      rw [hj]
      unfold simpleSnd
      rw [dite_eq_left (by omega)]
      congr 3
      exact Fin.ext hab
    · -- `e_a + e_b`
      have ha := a.isLt
      have hb := b.isLt
      have ha' : (a : ℕ) + 1 = n := by
        by_contra hne
        exact hgap (Sum.inl ⟨a + 1, by omega⟩) (by simp only [wHeight_inl, wHeight_inr]; omega)
          (by simp only [wHeight_inl]; push_cast; omega)
      have hb' : (b : ℕ) + 1 = n := by
        by_contra hne
        exact hgap (Sum.inr ⟨n - 1, by omega⟩)
          (by simp only [wHeight_inr]; push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; omega)
          (by simp only [wHeight_inl, wHeight_inr]; push_cast
              [Nat.cast_sub (show 1 ≤ n by omega)]; omega)
      refine ⟨a, ?_⟩
      rw [hj]
      unfold simpleSnd
      rw [dite_eq_right (by omega)]
      congr 3
      exact Fin.ext (by omega)
    · -- `-e_a - e_b` is negative
      have ha := a.isLt
      have hb := b.isLt
      omega
    · -- `e_b - e_a`
      have ha := a.isLt
      have hab : (a : ℕ) = b + 1 := by
        by_contra hne
        exact hgap (Sum.inr ⟨b + 1, by omega⟩) (by simp only [wHeight_inr]; push_cast; omega)
          (by simp only [wHeight_inr]; push_cast; omega)
      refine ⟨b, ?_⟩
      rw [hj]
      unfold simpleSnd
      rw [dite_eq_left (by omega)]
      funext c
      simp only [Pi.sub_apply, weightCoord_inl, weightCoord_inr, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  · rintro ⟨i, hj⟩
    have hv := wHeight_simple i
    have hpos : 0 < P.root' j (regularCochar n k) := by
      rw [root'_regularCochar hP hj, hv]
      split_ifs <;> norm_num
    refine ⟨by simpa only [Set.mem_ofPred_eq, hval] using hpos, ?_⟩
    intro j1 h1 j2 h2 hsum
    exfalso
    have h1' : 0 < P.root' j1 (regularCochar n k) := by
      simpa only [Set.mem_ofPred_eq, hval] using h1
    have h2' : 0 < P.root' j2 (regularCochar n k) := by
      simpa only [Set.mem_ofPred_eq, hval] using h2
    have hs : P.root' j (regularCochar n k) =
        P.root' j1 (regularCochar n k) + P.root' j2 (regularCochar n k) := by
      rw [← hval, ← hval, ← hval, hsum, map_add]
    obtain ⟨x1, y1, -, hj1⟩ := exists_root_eq hP j1
    obtain ⟨x2, y2, -, hj2⟩ := exists_root_eq hP j2
    rw [root'_regularCochar hP hj1] at h1' hs
    rw [root'_regularCochar hP hj2] at h2' hs
    rw [root'_regularCochar hP hj, hv] at hs
    by_cases hi : (i : ℕ) + 1 < n
    · rw [ite_eq_left hi] at hs
      omega
    · rw [ite_eq_right hi] at hs
      have hi' : (i : ℕ) + 1 = n := by have := i.isLt; omega
      have c1 := coord_last_nonpos (x := x1) (y := y1) (by omega) i hi'
      have c2 := coord_last_nonpos (x := x2) (y := y2) (by omega) i hi'
      have hc := congrFun (congrArg (GeneralLinear.characterCoordEquiv (Fin n) k) hsum) i
      rw [map_add, Pi.add_apply, hj, hj1, hj2] at hc
      have hci : (weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i)) i = 2 := by
        unfold simpleSnd
        rw [dite_eq_right hi]
        simp
      omega

/-- The pairing of two simple roots is the Cartan matrix of type `C_n`. -/
theorem pairing_simple {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P) {a b : J} {i i' : Fin n}
    (ha : GeneralLinear.characterCoordEquiv (Fin n) k (P.root a) =
      weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i))
    (hb : GeneralLinear.characterCoordEquiv (Fin n) k (P.root b) =
      weightCoord (Fin n) (Sum.inl i') - weightCoord (Fin n) (simpleSnd i')) :
    P.pairing a b = CartanMatrix.C n i i' := by
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h : (i' : ℕ) + 1 < n
  · have hb' : P.root b = diffRoot (Fin n) k i' ⟨i' + 1, h⟩ := by
      apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
      rw [hb, characterCoordEquiv_diffRoot, simpleSnd, dite_eq_left h, weightCoord_inl,
        weightCoord_inl]
    have hne : i' ≠ ⟨i' + 1, h⟩ := fun h' => by
      have := congrArg Fin.val h'
      simp at this
    rw [← P.root_coroot_eq_pairing, hP.1, GeneralLinear.latticePairing_coord,
      cocharacterCoordEquiv_coroot_of_root_eq_diffRoot hP hne hb', ha,
      sum_mul_single_sub_single]
    unfold simpleSnd
    split_ifs with hi2 <;>
      simp only [CartanMatrix.C, Matrix.of_apply, Pi.sub_apply, weightCoord_inl,
        weightCoord_inr, Pi.single_apply, Fin.ext_iff] <;>
      split_ifs <;> omega
  · have hb' : P.root b = longRoot (Fin n) k i' := by
      apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
      rw [hb, characterCoordEquiv_longRoot, simpleSnd, dite_eq_right h, weightCoord_inl_sub_inr]
    rw [pairing_eq_coord_of_root_eq_longRoot hP hb', ha]
    unfold simpleSnd
    split_ifs with hi2 <;>
      simp only [CartanMatrix.C, Matrix.of_apply, Pi.sub_apply, weightCoord_inl,
        weightCoord_inr, Pi.single_apply, Fin.ext_iff] <;>
      split_ifs <;> omega

/-! ### The pinning -/

variable (n k)

/-- **Coordinate root datum of `Sp_{2n}`.** The diagonal torus has a reduced root datum with
spanning coroots and a base numbered so that the simple pairings form the Cartan matrix
`C_n`. -/
theorem exists_coordinateRootDatum :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻))
      (_ : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P) (_ : P.IsReduced)
      (B : P.Base) (e : B.support ≃ Fin n),
      P.corootSpan ℤ = ⊤ ∧
        ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.C n (e a) (e b) := by
  classical
  obtain ⟨J, hJ, P, hP, hred⟩ := exists_rootDatum (Fin n) k
  have : Fintype J := Fintype.ofFinite J
  have : P.IsReduced := hred
  obtain ⟨B, hB⟩ := Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P
    (regularCochar n k) (root'_regularCochar_ne_zero hP)
  have hsimple : ∀ j : J, j ∈ B.support ↔ ∃ i : Fin n,
      GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
        weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i) :=
    fun j => by rw [← Finset.mem_coe, hB, mem_baseOf_iff hP]
  let g : B.support → Fin n := fun j => ((hsimple j).mp j.2).choose
  have hg : ∀ j : B.support, GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
      weightCoord (Fin n) (Sum.inl (g j)) - weightCoord (Fin n) (simpleSnd (g j)) :=
    fun j => ((hsimple j).mp j.2).choose_spec
  have hbij : Function.Bijective g := by
    refine ⟨fun a b hab => Subtype.ext (P.root.injective ?_), fun i => ?_⟩
    · apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
      rw [hg a, hg b, hab]
    · obtain ⟨j, hj⟩ := exists_root_of_ne hP (inl_ne_simpleSnd i)
      have hjB : j ∈ B.support := (hsimple j).mpr ⟨i, hj⟩
      exact ⟨⟨j, hjB⟩, simple_injective ((hg ⟨j, hjB⟩).symm.trans hj)⟩
  refine ⟨J, hJ, P, hP, hred, B, Equiv.ofBijective g hbij, corootSpan_eq_top hP, ?_⟩
  intro a b
  exact pairing_simple hP (hg a) (hg b)

/-- **The split pinning of `Sp_{2n}`.** Over a field, the diagonal torus of the split
symplectic group carries a split pinning whose coroots span the cocharacter lattice and whose
simple roots, numbered `e_i - e_{i+1}` (`i + 1 < n`) and `2e_{n-1}`, have Cartan matrix
`C_n`. -/
theorem exists_splitPinning :
    ∃ p : SplitPinning (groupScheme (Fin n) (CommRingCat.of k)),
      p.rootDatum.corootSpan ℤ = ⊤ ∧
        ∃ e : p.base.support ≃ Fin n,
          ∀ a b : p.base.support, p.rootDatum.pairing a b = CartanMatrix.C n (e a) (e b) := by
  classical
  obtain ⟨J, hJ, P, hP, hred, B, e, hspan, hcartan⟩ := exists_coordinateRootDatum n k
  have : Finite J := hJ
  have hG := isConnectedReductive (Fin n) k
  exact ⟨{ isConnectedReductive := hG
           torus := 𝔻
           inclusion := diagonalTorus (Fin n) (CommRingCat.of k)
           isSplitTorus := isSplitTorus_diagonalTorus (Fin n) k
           isMaximalTorus := isMaximalTorus_diagonalTorus (Fin n) k
           rootIndex := J
           rootDatum := P
           isRootDatum := hP
           isReduced := hred
           base := B
           pinning := RootPinning.ofSplitMaximalTorus hG (isSplitTorus_diagonalTorus (Fin n) k) _
             (isMaximalTorus_diagonalTorus (Fin n) k) P hP B },
    hspan, e, hcartan⟩

end Field

end TypeCPinning

end Langlands.GroupScheme.SymplecticMatrix
