import Langlands.GroupScheme.Reductive.SpecialLinearCoroots
import Langlands.GroupScheme.Reductive.SpecialLinearPinningStatement
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.LinearAlgebra.RootDatumCoweightFace

/-! # The split pinning of `SL_{n+1}` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsAddIndecomposable

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : ℕ}

/-! ### Integer coordinates -/

section Coords

variable (n) in
/-- The coordinates `x ↦ n - 2x` of a regular cocharacter. -/
def regularCoord (x : Fin (n + 1)) : ℤ :=
  n - 2 * (x : ℕ)

theorem sum_range_two_mul (m : ℕ) :
    ∑ i ∈ Finset.range m, 2 * (i : ℤ) = m * ((m : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_regularCoord : ∑ x, regularCoord n x = 0 := by
  simp only [regularCoord, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 * (i : ℤ)) (n + 1), sum_range_two_mul]
  push_cast
  ring

theorem regularCoord_sub (x y : Fin (n + 1)) :
    regularCoord n x - regularCoord n y = 2 * ((y : ℕ) - (x : ℕ) : ℤ) := by
  simp only [regularCoord]
  ring

/-- The simple coroot `u(b) - u(b + 1)` takes the value `A_n(a, b)` on `w(a) - w(a + 1)`. -/
theorem delta_sub_delta_eq_cartan (a b : Fin n) :
    delta b.castSucc b.succ a.castSucc - delta b.castSucc b.succ a.succ =
      CartanMatrix.A n a b := by
  simp only [delta, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> omega

theorem eq_of_cartan_eq_two {a b : Fin n} (h : CartanMatrix.A n a b = 2) : a = b := by
  simp only [CartanMatrix.A, Matrix.of_apply] at h
  split_ifs at h with h1 <;> first | exact h1 | omega

end Coords

/-! ### Simple roots over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

variable (n k) in
/-- The regular cocharacter with coordinates `x ↦ n - 2x`. -/
def regularCochar : cocharacterLattice 𝔻 :=
  cochar n k (regularCoord n)

theorem latticePairing_rootChar_regularCochar (x y : Fin (n + 1)) :
    latticePairing 𝔻 (rootChar n k x y) (regularCochar n k) = 2 * ((y : ℕ) - (x : ℕ) : ℤ) := by
  rw [regularCochar, latticePairing_rootChar_cochar x y sum_regularCoord, regularCoord_sub]

/-- The simple roots `w(a) - w(a + 1)` are pairwise distinct. -/
theorem rootChar_castSucc_succ_injective :
    Function.Injective fun a : Fin n => rootChar n k a.castSucc a.succ := by
  intro a b hab
  have h := congrArg (fun χ => latticePairing 𝔻 χ (corootChar n k b.castSucc b.succ)) hab
  simp only [latticePairing_rootChar_corootChar, delta_sub_delta_eq_cartan] at h
  rw [show CartanMatrix.A n b b = 2 by simp [CartanMatrix.A]] at h
  exact eq_of_cartan_eq_two h

theorem exists_root_eq {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) (j : J) :
    ∃ x y : Fin (n + 1), x ≠ y ∧ P.root j = rootChar n k x y :=
  (mem_range_root_iff hP (P.root j)).mp (Set.mem_range_self j)

theorem root'_regularCochar {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    {j : J} {x y : Fin (n + 1)} (hj : P.root j = rootChar n k x y) :
    P.root' j (regularCochar n k) = 2 * ((y : ℕ) - (x : ℕ) : ℤ) := by
  change P.toLinearMap (P.root j) (regularCochar n k) = _
  rw [hP.1, hj, latticePairing_rootChar_regularCochar]

theorem root'_regularCochar_ne_zero {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) (j : J) :
    P.root' j (regularCochar n k) ≠ 0 := by
  obtain ⟨x, y, hxy, hj⟩ := exists_root_eq hP j
  rw [root'_regularCochar hP hj]
  have : (x : ℕ) ≠ y := Fin.val_ne_of_ne hxy
  omega

/-- The pairing of two roots of a root datum of the diagonal torus. -/
theorem pairing_eq_delta {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P)
    {i j : J} {x y p q : Fin (n + 1)} (hi : P.root i = rootChar n k x y)
    (hj : P.root j = rootChar n k p q) :
    P.pairing i j = delta p q x - delta p q y := by
  rw [← P.root_coroot_eq_pairing, coroot_eq_corootChar hP hj, hP.1, hi,
    latticePairing_rootChar_corootChar]

/-- **Simple roots.** For the regular cocharacter `x ↦ n - 2x`, the indecomposable positive
roots are exactly the `w(a) - w(a + 1)`. -/
theorem mem_baseOf_iff {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) (j : J) :
    j ∈ baseOf P.root ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ) ↔
      ∃ a : Fin n, P.root j = rootChar n k a.castSucc a.succ := by
  have hval : ∀ i : J, ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ) (P.root i) =
      P.root' i (regularCochar n k) := fun i => rfl
  change IsAddIndecomposable P.root _ j ↔ _
  constructor
  · rintro ⟨hpos, hind⟩
    obtain ⟨x, y, hxy, hj⟩ := exists_root_eq hP j
    have hpos' : 0 < P.root' j (regularCochar n k) := by
      simpa only [Set.mem_ofPred_eq, hval] using hpos
    rw [root'_regularCochar hP hj] at hpos'
    have hy : (y : ℕ) = x + 1 := by
      by_contra hne
      have hz : (x : ℕ) + 1 < n + 1 := by omega
      set z : Fin (n + 1) := ⟨x + 1, hz⟩
      have hxz : x ≠ z := fun h => by
        have := congrArg Fin.val h
        simp [z] at this
      have hzy : z ≠ y := fun h => by
        have := congrArg Fin.val h
        simp only [z] at this
        omega
      obtain ⟨j1, hj1⟩ := (mem_range_root_iff hP _).mpr ⟨x, z, hxz, rfl⟩
      obtain ⟨j2, hj2⟩ := (mem_range_root_iff hP _).mpr ⟨z, y, hzy, rfl⟩
      have h1 : j1 ∈ {i | 0 < ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ) (P.root i)} := by
        simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hj1]
        simp only [z]
        omega
      have h2 : j2 ∈ {i | 0 < ((P.flip.toLinearMap (regularCochar n k)) : _ →+ ℤ) (P.root i)} := by
        simp only [Set.mem_ofPred_eq, hval, root'_regularCochar hP hj2]
        simp only [z]
        omega
      rcases hind j1 h1 j2 h2 (by rw [hj, hj1, hj2, rootChar_add_rootChar]) with h | h
      · exact P.ne_zero j1 h
      · exact P.ne_zero j2 h
    refine ⟨⟨x, by omega⟩, ?_⟩
    rw [hj]
    congr 1
    ext
    simp [hy]
  · rintro ⟨a, hj⟩
    have hpos : 0 < P.root' j (regularCochar n k) := by
      rw [root'_regularCochar hP hj]
      simp
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
    rw [root'_regularCochar hP hj] at hs
    simp only [Fin.val_castSucc, Fin.val_succ] at hs
    omega

/-! ### The pinning -/

variable (n k)

/-- **Coordinate root datum of `SL_{n+1}`.** The determinant-one diagonal torus has a
reduced root datum with spanning coroots and a base numbered by the adjacent coordinate roots.
Its simple-root pairings are the Cartan matrix `A_n`. -/
theorem exists_coordinateRootDatum :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻))
      (_ : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P) (_ : P.IsReduced)
      (B : P.Base) (e : B.support ≃ Fin n),
      P.corootSpan ℤ = ⊤ ∧
        (∀ a : B.support, P.root a.val = rootChar n k (e a).castSucc (e a).succ) ∧
          ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.A n (e a) (e b) := by
  classical
  have hG := isConnectedReductive k (Fin (n + 1)) 0
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k (groupScheme (Fin (n + 1))
    (CommRingCat.of k)) hG 𝔻 (isSplitTorus_diagonalTorus n k)
    (diagonalTorus n (CommRingCat.of k)) (isMaximalTorus_diagonalTorus n k)
  have : Fintype J := Fintype.ofFinite J
  have : P.IsReduced := hred
  obtain ⟨B, hB⟩ := Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P (regularCochar n k)
    (root'_regularCochar_ne_zero hP)
  have hsimple : ∀ j : J, j ∈ B.support ↔ ∃ a : Fin n, P.root j = rootChar n k a.castSucc a.succ :=
    fun j => by rw [← Finset.mem_coe, hB, mem_baseOf_iff hP]
  let g : B.support → Fin n := fun j => ((hsimple j).mp j.2).choose
  have hg : ∀ j : B.support, P.root j = rootChar n k (g j).castSucc (g j).succ :=
    fun j => ((hsimple j).mp j.2).choose_spec
  have hbij : Function.Bijective g := by
    refine ⟨fun i j hij => Subtype.ext (P.root.injective ?_), fun a => ?_⟩
    · rw [hg i, hg j, hij]
    · obtain ⟨j, hj⟩ := (mem_range_root_iff hP _).mpr
        ⟨a.castSucc, a.succ, (show a.castSucc < a.succ from Fin.castSucc_lt_succ).ne, rfl⟩
      have hjB : j ∈ B.support := (hsimple j).mpr ⟨a, hj⟩
      refine ⟨⟨j, hjB⟩, rootChar_castSucc_succ_injective (k := k) ?_⟩
      exact (hg ⟨j, hjB⟩).symm.trans hj
  refine ⟨J, hJ, P, hP, hred, B, Equiv.ofBijective g hbij,
    corootSpan_eq_top hP, hg, ?_⟩
  intro a b
  change P.pairing a b = CartanMatrix.A n (g a) (g b)
  rw [pairing_eq_delta hP (hg a) (hg b), delta_sub_delta_eq_cartan]

/-- **The split pinning of `SL_{n+1}`.** Over a field, the diagonal torus of `SL_{n+1}` carries
a split pinning whose coroots span the cocharacter lattice and whose simple roots, numbered
`w(a) - w(a + 1)` for `a : Fin n`, have Cartan matrix `A_n`. -/
theorem exists_splitPinning :
    ∃ p : SplitPinning (groupScheme (Fin (n + 1)) (CommRingCat.of k)),
      p.rootDatum.corootSpan ℤ = ⊤ ∧
        ∃ e : p.base.support ≃ Fin n,
          ∀ a b : p.base.support, p.rootDatum.pairing a b = CartanMatrix.A n (e a) (e b) := by
  classical
  obtain ⟨J, hJ, P, hP, hred, B, e, hspan, _, hcartan⟩ := exists_coordinateRootDatum n k
  have : Finite J := hJ
  have hG := isConnectedReductive k (Fin (n + 1)) 0
  exact ⟨{ isConnectedReductive := hG
           torus := 𝔻
           inclusion := diagonalTorus n (CommRingCat.of k)
           isSplitTorus := isSplitTorus_diagonalTorus n k
           isMaximalTorus := isMaximalTorus_diagonalTorus n k
           rootIndex := J
           rootDatum := P
           isRootDatum := hP
           isReduced := hred
           base := B
           pinning := RootPinning.ofSplitMaximalTorus hG (isSplitTorus_diagonalTorus n k) _
             (isMaximalTorus_diagonalTorus n k) P hP B },
    hspan, e, hcartan⟩

end Field

end Langlands.GroupScheme.SpecialLinear.FinSucc

namespace Langlands.GroupScheme

/-- **Split pinning of `SL_{n+1}`.** `SL_{n+1}` over a field has a split pinning with coroots
spanning the cocharacter lattice and Cartan matrix `A_n`. -/
theorem specialLinearSimplyConnectedPinning : SpecialLinearSimplyConnectedPinningStatement.{u} := by
  intro k _ n
  exact SpecialLinear.FinSucc.exists_splitPinning n k

end Langlands.GroupScheme
