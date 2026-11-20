import Langlands.GroupScheme.Trigonalizable.Flag
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Trigonalizable groups embed in the upper triangular group (Milne 16.2, (a) ⇒ (c))

Choose a closed embedding `ρ : G → GL_N` and a maximal flag of `kᴺ` stabilized by `ρ`, which
exists because `G` is trigonalizable. A basis adapted to the flag gives an invertible matrix `P`.
After conjugating by `P⁻¹`, the representation is upper triangular on every scheme test, because
each term of the flag is stable. Hence it factors through a closed immersion into the upper
triangular group `T_N`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open MatrixRepresentation

namespace Trigonalizable

section LinearAlgebra

variable {K : Type*} [Field K] {N : ℕ}

/-- A nonzero coefficient vector has a last nonzero coordinate, which lies at or after any
given nonzero coordinate. -/
theorem exists_last_ne_zero {c : Fin N → K} {i : Fin N} (hi : c i ≠ 0) :
    ∃ m, i ≤ m ∧ c m ≠ 0 ∧ ∀ l, m < l → c l = 0 := by
  classical
  let s := Finset.univ.filter fun l => c l ≠ 0
  have hs : i ∈ s := by simp [s, hi]
  refine ⟨s.max' ⟨i, hs⟩, s.le_max' i hs, ?_, fun l hl => ?_⟩
  · simpa [s] using s.max'_mem ⟨i, hs⟩
  · by_contra hl'
    have hls : l ∈ s := by simp [s, hl']
    exact absurd (s.le_max' l hls) (not_le.mpr hl)

/-- For vectors adapted to a flag (the `j`-th lies in the `(j+1)`-st term but not in the `j`-th),
a combination whose last nonzero coefficient is at `m` does not lie in the `m`-th term. -/
theorem sum_smul_notMem_of_adapted {W : Fin (N + 1) → Submodule K (Fin N → K)}
    (hW : Monotone W) {p : Fin N → Fin N → K} (hp : ∀ j, p j ∈ W j.succ)
    (hp' : ∀ j, p j ∉ W j.castSucc) (c : Fin N → K) (m : Fin N) (hm : c m ≠ 0)
    (hmax : ∀ l, m < l → c l = 0) :
    ∑ l, c l • p l ∉ W m.castSucc := by
  intro hsum
  apply hp' m
  have hrest : ∑ l ∈ Finset.univ.erase m, c l • p l ∈ W m.castSucc := by
    refine Submodule.sum_mem _ fun l hl => ?_
    rcases lt_trichotomy l m with hlm | hlm | hlm
    · exact Submodule.smul_mem _ _ (hW (Fin.succ_le_castSucc_iff.mpr hlm) (hp l))
    · exact absurd hlm (Finset.ne_of_mem_erase hl)
    · rw [hmax l hlm, zero_smul]
      exact Submodule.zero_mem _
  have hm' : c m • p m ∈ W m.castSucc := by
    have h := Submodule.sub_mem _ hsum hrest
    rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ m), add_sub_cancel_right] at h
  exact (Submodule.smul_mem_iff _ hm).mp hm'

/-- A maximal flag of `Kᴺ` has an adapted basis: an invertible matrix whose `j`-th column lies
in the `(j+1)`-st term of the flag and whose inverse sends that term into the span of the first
`j+1` coordinate vectors. -/
theorem exists_adapted_matrix {W : Fin (N + 1) → Submodule K (Fin N → K)} (hW : Monotone W)
    (hrank : ∀ i, Module.finrank K (W i) = i.val) :
    ∃ P : GL (Fin N) K, (∀ j, (fun r => (P : Matrix (Fin N) (Fin N) K) r j) ∈ W j.succ) ∧
      ∀ j, ∀ w ∈ W j.succ, ∀ i, j < i →
        (((P⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w) i = 0 := by
  have hlt (j : Fin N) : W j.castSucc < W j.succ := by
    refine lt_of_le_of_ne (hW (Fin.castSucc_le_succ j)) fun h => ?_
    have h' := congrArg (fun U : Submodule K (Fin N → K) => Module.finrank K U) h
    simp only [hrank, Fin.val_castSucc, Fin.val_succ] at h'
    omega
  choose p hp hp' using fun j => SetLike.exists_of_lt (hlt j)
  let A : Matrix (Fin N) (Fin N) K := Matrix.of fun r l => p l r
  have hA (c : Fin N → K) : A *ᵥ c = ∑ l, c l • p l := by
    funext r
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : Function.Injective A.mulVec := by
    intro c c' hcc
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hi' : (c - c') i ≠ 0 := sub_ne_zero.mpr hi
    obtain ⟨m, -, hm, hmax⟩ := exists_last_ne_zero hi'
    apply sum_smul_notMem_of_adapted hW hp hp' (c - c') m hm hmax
    rw [← hA, Matrix.mulVec_sub, hcc, sub_self]
    exact Submodule.zero_mem _
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hunit.unit, fun j => ?_, fun j w hw i hji => ?_⟩
  · rw [IsUnit.unit_spec]
    exact hp j
  · by_contra hne
    obtain ⟨m, him, hm, hmax⟩ := exists_last_ne_zero hne
    apply sum_smul_notMem_of_adapted hW hp hp' _ m hm hmax
    rw [← hA]
    have hAinv : A *ᵥ (((hunit.unit⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec]
      nth_rewrite 1 [← IsUnit.unit_spec hunit]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hAinv]
    exact hW (Fin.succ_le_castSucc_iff.mpr (lt_of_lt_of_le hji him)) hw

end LinearAlgebra

variable {k : Type u} [Field k]

/-- Conjugating by the inverse of a matrix adapted to a stable flag makes a representation upper
triangular on every scheme test. -/
theorem conjugate_pointMatrix_eq_zero_of_adapted
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {N : ℕ}
    (ρ : MatrixRepresentation G (Fin N)) {W : Fin (N + 1) → Submodule k (Fin N → k)}
    (hst : ∀ i, ρ.IsStableSubspace (W i)) (P : GL (Fin N) k)
    (hcol : ∀ j, (fun r => (P : Matrix (Fin N) (Fin N) k) r j) ∈ W j.succ)
    (htri : ∀ j, ∀ w ∈ W j.succ, ∀ i, j < i →
      (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ w) i = 0)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) (i j : Fin N) (hji : j < i) :
    ((ρ.conjugate (basePoint (R := CommRingCat.of k) P⁻¹)).pointMatrix T x :
      Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) i j = 0 := by
  let φ : Matrix Unit (Fin N) k := fun _ l => ((P⁻¹ : GL (Fin N) k) : Matrix _ _ k) i l
  have hφ : ∀ w ∈ W j.succ, φ *ᵥ w = 0 := by
    intro w hw
    funext u
    exact htri j w hw i hji
  have h := congrFun ((hst j.succ).mulVec_pointMatrix_eq_zero φ hφ (hcol j) T x) ()
  rw [conjugate_pointMatrix, pointsEquiv_constantPoint_basePoint, map_inv, inv_inv,
    Units.val_mul, Units.val_mul]
  rw [Matrix.mulVec_mulVec] at h
  exact h

/-- A closed linear embedding which is upper triangular at the universal point factors as a
closed immersion into the upper triangular group `T_N`. -/
theorem exists_closed_blockParabolic_factor
    {H : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
    (ρ : MatrixRepresentation H (Fin N)) (hρ : IsClosedSubgroup ρ)
    (h : ∀ i j : Fin N, j < i →
      (ρ.pointMatrix H.X (𝟙 H.X) : Matrix (Fin N) (Fin N) Γ(H.X.left, ⊤)) i j = 0) :
    ∃ j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ)),
      IsClosedSubgroup j := by
  let e : Fin N → ℤ := fun i => -(i.val : ℤ)
  have hu : ρ.hom.hom ∈
      (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e).carrier H.X := by
    refine (GeneralLinear.mem_blockParabolic _).2 fun i j hij => ?_
    have hji : j < i := by
      change j.val < i.val
      simp only [e] at hij
      omega
    simpa only [pointMatrix_apply, Category.id_comp] using h i j hji
  have hmono : Mono ρ.hom.hom := by
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    exact Over.mono_of_mono_left _
  have hiρ : (SubgroupFunctor.range ρ).IsRepresentedBy ρ := ⟨hmono, rfl⟩
  have hi := GeneralLinear.isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k) e
  have hle : ∀ T, (SubgroupFunctor.range ρ).carrier T ≤
      (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e).carrier T := by
    rintro T _ ⟨x, rfl⟩
    exact (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e).comp_mem x hu
  let f := SubgroupFunctor.IsRepresentedBy.lift hiρ hi
    (fun T => Subgroup.inclusion (hle T)) (fun _ _ => rfl)
  have hf : f ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e = ρ :=
    SubgroupFunctor.IsRepresentedBy.lift_comp_eq hiρ hi _ (fun _ _ => rfl)
      (fun _ _ => rfl)
  refine ⟨f, ?_⟩
  have : IsClosedImmersion
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockParabolicHom (Fin N) (CommRingCat.of k) e
  have hcomp : f.hom.hom.left ≫
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left =
      ρ.hom.hom.left := congrArg (fun a => a.hom.hom.left) hf
  have : IsClosedImmersion (f.hom.hom.left ≫
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left) := by
    rw [hcomp]
    exact hρ
  exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left
    (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e).hom.hom.left

/-- Milne 16.2, (a) ⇒ (c): a trigonalizable affine algebraic group admits a closed embedding into
the upper triangular group `T_N` for some `N`. -/
theorem exists_closed_triangular_of_isTrigonalizable
    {G : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G.X.hom] (hG : IsTrigonalizable G) :
    ∃ (N : ℕ) (j : G ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ))),
      IsClosedSubgroup j := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨W, hmono, hrank, hst⟩ :=
    exists_stableFlag_of_card_eq hG N (Fin N) ρ (Fintype.card_fin N)
  obtain ⟨P, hcol, htri⟩ := exists_adapted_matrix hmono hrank
  let g := basePoint (R := CommRingCat.of k) P⁻¹
  have hρg : IsClosedSubgroup (ρ.conjugate g) := by
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    have : IsIso
        ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g).hom.hom.hom))
    change IsClosedImmersion (ρ.hom.hom.left ≫ _)
    infer_instance
  obtain ⟨j, hj⟩ := exists_closed_blockParabolic_factor (ρ.conjugate g) hρg
    fun i j hji => conjugate_pointMatrix_eq_zero_of_adapted ρ hst P hcol htri _ _ i j hji
  exact ⟨N, j, hj⟩

end Trigonalizable

end Langlands.GroupScheme
