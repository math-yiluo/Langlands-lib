import Langlands.GroupScheme.SpecialLinearTorus
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion

/-! # The split special linear group over a field is simply connected -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

/-! ### A coordinate computation -/

/-- If `ν c + ∑ ν = 2` and `ν d = ν c - 1` for every `d ≠ c`, then `ν = e_c`. -/
theorem eq_single_of_pairing {I : Type*} [Fintype I] [DecidableEq I] (ν : I → ℤ) (c : I)
    (hself : ν c + ∑ d, ν d = 2) (hd : ∀ d, d ≠ c → ν d = ν c - 1) : ν = Pi.single c 1 := by
  have hS : ∑ d, ν d = ∑ d, ((ν c - 1) + (Pi.single c 1 : I → ℤ) d) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hdc : d = c
    · subst hdc
      rw [Pi.single_eq_same]
      ring
    · rw [hd d hdc, Pi.single_eq_of_ne hdc, add_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_pi_single', Finset.mem_univ, ite_true] at hS
  have h : ((Fintype.card I : ℤ) + 1) * (ν c - 1) = 0 := by
    linear_combination hself - hS
  have hc : ν c = 1 := by
    rcases mul_eq_zero.mp h with h | h
    · omega
    · omega
  funext d
  by_cases hdc : d = c
  · subst hdc
    rw [Pi.single_eq_same, hc]
  · rw [Pi.single_eq_of_ne hdc, hd d hdc, hc, sub_self]

variable {n : Type} [Fintype n] [DecidableEq n]

section Pairings

variable {p : n}

/-- Pairing the weight coordinates of `x ≠ p` with `ν` picks out `ν_x`. -/
theorem sum_weightCoord_val_mul (c : OffPivot p) (ν : OffPivot p → ℤ) :
    ∑ d, weightCoord p c.1 d * ν d = ν c := by
  rw [weightCoord_val]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- Pairing the weight coordinates of the pivot with `ν` gives `-∑ ν`. -/
theorem sum_weightCoord_pivot_mul (ν : OffPivot p → ℤ) :
    ∑ d, weightCoord p p d * ν d = -∑ d, ν d := by
  rw [weightCoord_pivot]
  simp only [neg_one_mul, Finset.sum_neg_distrib]

end Pairings

/-! ### The zero weight space and maximality -/

section Field

variable {p : n} {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (OffPivot p))

/-- The zero weight space consists of the Lie algebra elements with diagonal matrix. -/
theorem mem_weightSpace_zero_iff
    (X : Additive (lieKernel (groupScheme n (CommRingCat.of k)) k)) :
    X ∈ weightSpace (diagonalTorus p (CommRingCat.of k)) 0 ↔
      ∀ x y : n, x ≠ y → lieMatrix X x y = 0 := by
  rw [mem_weightSpace_diagonalTorus_iff_support, map_zero]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  have hw : (0 : OffPivot p → ℤ) = weightCoord p x - weightCoord p y ↔ x = y := by
    rw [eq_comm, sub_eq_zero]
    exact (weightCoord_injective p).eq_iff
  rw [hw]
  exact not_imp_comm

variable (p k) in
/-- The diagonal entries away from the pivot of an element of the zero weight space. -/
def zeroWeightCoord :
    weightSpace (diagonalTorus p (CommRingCat.of k)) 0 →ₗ[k] (OffPivot p → k) where
  toFun X c := lieMatrix (X : Additive (lieKernel (groupScheme n (CommRingCat.of k)) k)) c.1 c.1
  map_add' X Y := by
    funext c
    simp only [Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' a X := by
    funext c
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      RingHom.id_apply]

theorem zeroWeightCoord_apply (X : weightSpace (diagonalTorus p (CommRingCat.of k)) 0)
    (c : OffPivot p) :
    zeroWeightCoord p k X c =
      lieMatrix (X : Additive (lieKernel (groupScheme n (CommRingCat.of k)) k)) c.1 c.1 :=
  rfl

/-- The pivot diagonal entry of a trace-zero matrix is minus the sum of the other diagonal
entries. -/
theorem apply_pivot_eq_neg_sum {A : Type*} [CommRing A] {Y : Matrix n n A}
    (hY : Matrix.trace Y = 0) : Y p p = -∑ c : OffPivot p, Y c.1 c.1 := by
  rw [Matrix.trace, Fintype.sum_eq_add_sum_subtype_ne _ p] at hY
  simp only [Matrix.diag_apply] at hY
  linear_combination hY

/-- An element of the zero weight space is determined by its diagonal entries away from the
pivot. -/
theorem lieMatrix_eq_zero_of_zeroWeightCoord
    (X : weightSpace (diagonalTorus p (CommRingCat.of k)) 0) (hX : zeroWeightCoord p k X = 0) :
    lieMatrix (X : Additive (lieKernel (groupScheme n (CommRingCat.of k)) k)) = 0 := by
  obtain ⟨Xv, hXv⟩ := X
  have hd : ∀ x y : n, x ≠ y → lieMatrix Xv x y = 0 := (mem_weightSpace_zero_iff Xv).mp hXv
  have h0 : ∀ c : OffPivot p, lieMatrix Xv c.1 c.1 = 0 := fun c => by
    have h := congrFun hX c
    rw [zeroWeightCoord_apply, Pi.zero_apply] at h
    exact h
  change lieMatrix Xv = 0
  ext x y
  rw [Matrix.zero_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = p
    · subst hx
      rw [apply_pivot_eq_neg_sum (trace_lieMatrix Xv), Finset.sum_eq_zero fun c _ => h0 c,
        neg_zero]
    · exact h0 ⟨x, hx⟩
  · exact hd x y hxy

variable (p) in
/-- The diagonal with prescribed entries `d` away from the pivot and `-∑ d` at the pivot. -/
def offPivotDiag {A : Type*} [CommRing A] (d : OffPivot p → A) : n → A :=
  fun x => if h : x = p then -∑ c, d c else d ⟨x, h⟩

theorem offPivotDiag_val {A : Type*} [CommRing A] (d : OffPivot p → A) (c : OffPivot p) :
    offPivotDiag p d c.1 = d c := by
  simp [offPivotDiag, c.2]

theorem trace_diagonal_offPivotDiag {A : Type*} [CommRing A] (d : OffPivot p → A) :
    Matrix.trace (Matrix.diagonal (offPivotDiag p d)) = 0 := by
  rw [Matrix.trace_diagonal, Fintype.sum_eq_add_sum_subtype_ne _ p]
  have h1 : offPivotDiag p d p = -∑ c, d c := by simp [offPivotDiag]
  rw [h1, Finset.sum_congr rfl fun c _ => offPivotDiag_val d c, neg_add_cancel]

theorem zeroWeightCoord_bijective : Function.Bijective (zeroWeightCoord p k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [lieMatrix_eq_zero_of_zeroWeightCoord X hX, Submodule.coe_zero, map_zero]
  · intro d
    obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _
      (trace_diagonal_offPivotDiag d)
    have hmem : X ∈ weightSpace (diagonalTorus p (CommRingCat.of k)) 0 := by
      rw [mem_weightSpace_zero_iff, hX]
      intro x y hxy
      exact Matrix.diagonal_apply_ne _ hxy
    refine ⟨⟨X, hmem⟩, ?_⟩
    funext c
    rw [zeroWeightCoord_apply]
    change lieMatrix X c.1 c.1 = d c
    rw [hX, Matrix.diagonal_apply_eq, offPivotDiag_val]

/-- The zero weight space of the diagonal torus has dimension `|n| - 1`. -/
theorem finrank_weightSpace_zero :
    Module.finrank k (weightSpace (diagonalTorus p (CommRingCat.of k)) 0) =
      Fintype.card (OffPivot p) := by
  rw [(LinearEquiv.ofBijective (zeroWeightCoord p k) zeroWeightCoord_bijective).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

variable (p k) in
/-- **Maximality.** The diagonal torus of `SL_n` over a field is a maximal torus. -/
theorem isMaximalTorus_diagonalTorus :
    IsMaximalTorus (diagonalTorus p (CommRingCat.of k)) := by
  have : Nonempty n := ⟨p⟩
  have : IsAffineHom (𝔻).toGrp.X.hom := isAffineHom_splitTorus _ _
  refine isMaximalTorus_of_finrank_zeroWeight _ (isSplitTorus_diagonalTorus n p k)
    (isClosedSubgroup_diagonalTorus n p k) ?_
  rw [finrank_weightSpace_zero]
  have h := splitTorus.finrank_lieKernel (ULift.{u} (OffPivot p)) k
  rw [Nat.card_ulift, Nat.card_eq_fintype_card] at h
  exact h.symm

/-! ### Roots -/

/-- Every root of the diagonal torus is a weight difference `w(x) - w(y)`. -/
theorem exists_coord_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus p (CommRingCat.of k))) :
    ∃ x y : n, GeneralLinear.characterCoordEquiv (OffPivot p) k χ =
      weightCoord p x - weightCoord p y := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
  obtain ⟨x, y, hxy⟩ : ∃ x y, lieMatrix X x y ≠ 0 := by
    by_contra h
    apply hX0
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [map_zero]
    refine Matrix.ext fun x y => ?_
    rw [Matrix.zero_apply]
    by_contra hne
    exact h ⟨x, y, hne⟩
  exact ⟨x, y, (mem_weightSpace_diagonalTorus_iff_support X χ).mp hX x y hxy⟩

/-- Every coordinate of a root lies between `-2` and `2`. -/
theorem coord_mem_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus p (CommRingCat.of k))) (c : OffPivot p) :
    -2 ≤ GeneralLinear.characterCoordEquiv (OffPivot p) k χ c ∧
      GeneralLinear.characterCoordEquiv (OffPivot p) k χ c ≤ 2 := by
  obtain ⟨x, y, hxy⟩ := exists_coord_of_mem_roots hχ
  rw [hxy, Pi.sub_apply]
  have hx := weightCoord_apply_mem p x c
  have hy := weightCoord_apply_mem p y c
  omega

variable (p k) in
/-- The character `w(x) - w(y)` of the diagonal torus. -/
def rootChar (x y : n) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv (OffPivot p) k).symm (weightCoord p x - weightCoord p y)

theorem characterCoordEquiv_rootChar (x y : n) :
    GeneralLinear.characterCoordEquiv (OffPivot p) k (rootChar p k x y) =
      weightCoord p x - weightCoord p y :=
  LinearEquiv.apply_symm_apply _ _

/-- For `x ≠ y` the character `w(x) - w(y)` is a root, with root vector the matrix unit at
`(x, y)`. -/
theorem rootChar_mem_roots {x y : n} (hxy : x ≠ y) :
    rootChar p k x y ∈ roots (diagonalTorus p (CommRingCat.of k)) := by
  refine ⟨fun h0 => ?_, ?_⟩
  · have h1 := characterCoordEquiv_rootChar (p := p) (k := k) x y
    rw [h0, map_zero, eq_comm, sub_eq_zero] at h1
    exact hxy (weightCoord_injective p h1)
  · obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _
      (Matrix.trace_single_eq_of_ne x y (1 : k) hxy)
    rw [Submodule.ne_bot_iff]
    refine ⟨X, ?_, fun h0 => ?_⟩
    · rw [mem_weightSpace_diagonalTorus_iff_support, hX, characterCoordEquiv_rootChar]
      intro x' y' hx'y'
      obtain ⟨rfl, rfl⟩ : x' = x ∧ y' = y := by
        by_contra h
        exact hx'y' (Matrix.single_apply_of_ne _ _ _ _ _ fun e => h ⟨e.1.symm, e.2.symm⟩)
      rfl
    · have h1 := congrArg (fun Y => lieMatrix Y x y) h0
      simp only [hX, map_zero, Matrix.single_apply_same, Matrix.zero_apply] at h1
      exact one_ne_zero h1

/-! ### Coroots -/

/-- The pairing of `w(x) - w(y)` with a cocharacter, in coordinates. -/
theorem latticePairing_rootChar (x y : n) (ν : cocharacterLattice 𝔻) :
    latticePairing 𝔻 (rootChar p k x y) ν =
      ∑ d, weightCoord p x d * GeneralLinear.cocharacterCoordEquiv (OffPivot p) k ν d -
        ∑ d, weightCoord p y d * GeneralLinear.cocharacterCoordEquiv (OffPivot p) k ν d := by
  rw [GeneralLinear.latticePairing_coord, characterCoordEquiv_rootChar, ← Finset.sum_sub_distrib]
  simp only [Pi.sub_apply, sub_mul]

/-- Reflecting the root `w(x) - w(y)` along a root `w(x₀) - w(y₀)` of a root datum gives a root,
so its coordinates stay between `-2` and `2`. -/
theorem reflection_coord_mem {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus p (CommRingCat.of k)) P) {j : J} {x₀ y₀ x y : n}
    (hj : P.root j = rootChar p k x₀ y₀) (hxy : x ≠ y) (c : OffPivot p) :
    -2 ≤ (weightCoord p x - weightCoord p y) c -
        latticePairing 𝔻 (rootChar p k x y) (P.coroot j) *
          (weightCoord p x₀ - weightCoord p y₀) c ∧
      (weightCoord p x - weightCoord p y) c -
          latticePairing 𝔻 (rootChar p k x y) (P.coroot j) *
            (weightCoord p x₀ - weightCoord p y₀) c ≤ 2 := by
  obtain ⟨j', hj'⟩ : rootChar p k x y ∈ Set.range P.root := by
    rw [hP.2.1]
    exact rootChar_mem_roots hxy
  have hmem : P.root (P.reflectionPerm j j') ∈ roots (diagonalTorus p (CommRingCat.of k)) := by
    rw [← hP.2.1]
    exact ⟨_, rfl⟩
  have hpair : P.pairing j' j = latticePairing 𝔻 (P.root j') (P.coroot j) := by
    rw [← P.root_coroot_eq_pairing, hP.1]
  rw [P.root_reflectionPerm, P.reflection_apply_root, hj, hj'] at hmem
  rw [hj'] at hpair
  have h := coord_mem_of_mem_roots hmem c
  rw [map_sub, map_zsmul, characterCoordEquiv_rootChar, characterCoordEquiv_rootChar, hpair,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h

/-- **Coroots.** In a root datum of the diagonal torus, the coroot of the root
`w(c) - w(p) = e_c + ∑_d e_d` is the cocharacter `e_c^∨`. -/
theorem cocharacterCoordEquiv_coroot_of_root_eq_rootChar {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus p (CommRingCat.of k)) P) {j : J} {c : OffPivot p}
    (hj : P.root j = rootChar p k c.1 p) :
    GeneralLinear.cocharacterCoordEquiv (OffPivot p) k (P.coroot j) = Pi.single c 1 := by
  apply eq_single_of_pairing
  · have h : P.pairing j j = latticePairing 𝔻 (P.root j) (P.coroot j) := by
      rw [← P.root_coroot_eq_pairing, hP.1]
    rw [P.pairing_same, hj, latticePairing_rootChar, sum_weightCoord_val_mul,
      sum_weightCoord_pivot_mul] at h
    linarith
  · intro d hdc
    have hne1 : d.1 ≠ c.1 := fun h => hdc (Subtype.ext h)
    have h1 := reflection_coord_mem hP hj hne1 c
    have h2 := reflection_coord_mem hP hj d.2 c
    have hself : P.pairing j j = latticePairing 𝔻 (P.root j) (P.coroot j) := by
      rw [← P.root_coroot_eq_pairing, hP.1]
    rw [P.pairing_same, hj, latticePairing_rootChar, sum_weightCoord_val_mul,
      sum_weightCoord_pivot_mul] at hself
    rw [latticePairing_rootChar, sum_weightCoord_val_mul, sum_weightCoord_val_mul] at h1
    rw [latticePairing_rootChar, sum_weightCoord_val_mul, sum_weightCoord_pivot_mul] at h2
    simp only [Pi.sub_apply, weightCoord_val, weightCoord_pivot, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hdc)] at h1 h2
    omega

/-- **Coroot span.** The coroots of a root datum of the diagonal torus span the cocharacter
lattice: they contain the basis `e_c^∨`. -/
theorem corootSpan_eq_top {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus p (CommRingCat.of k)) P) :
    P.corootSpan ℤ = ⊤ := by
  rw [eq_top_iff,
    ← ((Pi.basisFun ℤ (OffPivot p)).map
      (GeneralLinear.cocharacterCoordEquiv (OffPivot p) k).symm).span_eq,
    Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨j, hj⟩ : rootChar p k c.1 p ∈ Set.range P.root := by
    rw [hP.2.1]
    exact rootChar_mem_roots c.2
  rw [Module.Basis.map_apply, Pi.basisFun_apply,
    ← cocharacterCoordEquiv_coroot_of_root_eq_rootChar hP hj, LinearEquiv.symm_apply_apply]
  exact Submodule.subset_span ⟨j, rfl⟩

/-! ### Simple connectedness -/

variable (p k)

/-- The diagonal torus of `SL_n` over a field has a reduced root datum. -/
theorem exists_rootDatum :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)),
      IsRootDatumOf (diagonalTorus p (CommRingCat.of k)) P ∧ P.IsReduced :=
  rootDatumExistence k (groupScheme n (CommRingCat.of k)) (isConnectedReductive k n p) 𝔻
    (isSplitTorus_diagonalTorus n p k) (diagonalTorus p (CommRingCat.of k))
    (isMaximalTorus_diagonalTorus p k)

include p in
/-- The split special linear group over a field is simply connected (stated with an explicit
pivot index `p`). -/
theorem isSimplyConnected_of_pivot : IsSimplyConnected (groupScheme n (CommRingCat.of k)) := by
  obtain ⟨J, _, P, hP, -⟩ := exists_rootDatum p k
  have hss : IsSemisimple (groupScheme n (CommRingCat.of k)) := by
    refine ((splitSemisimpleRootDatum k _ (isConnectedReductive k n p) 𝔻
      (isSplitTorus_diagonalTorus n p k) _ (isMaximalTorus_diagonalTorus p k) J P hP).2).mpr ?_
    rw [corootSpan_eq_top hP]
    infer_instance
  exact splitCorootSpanSimplyConnected k _ hss 𝔻 (isSplitTorus_diagonalTorus n p k)
    _ (isMaximalTorus_diagonalTorus p k) J P hP (corootSpan_eq_top hP)

end Field

end Langlands.GroupScheme.SpecialLinear

namespace Langlands.GroupScheme.SpecialLinear

/-- **Simple connectedness of `SL_n`.** For a nonempty finite index type `n`, the special linear
group `SL_n` over a field is simply connected. -/
theorem isSimplyConnected (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (k : Type u)
    [Field k] : IsSimplyConnected (groupScheme n (CommRingCat.of k)) :=
  isSimplyConnected_of_pivot (Classical.arbitrary n) k

end Langlands.GroupScheme.SpecialLinear
