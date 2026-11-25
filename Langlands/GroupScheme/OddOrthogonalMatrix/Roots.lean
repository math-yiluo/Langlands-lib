import Langlands.GroupScheme.OddOrthogonalMatrix.Torus
import Langlands.GroupScheme.OrthogonalMatrix.Roots

/-! # Maximality and roots of the actual odd diagonal torus -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] {K : Type u} [Field K]

omit [Fintype l] in
theorem signedWeight_ne_zero (a : l ⊕ l) : SymplecticMatrix.weightCoord l a ≠ 0 := by
  intro h
  rcases a with a | a <;> have he := congrFun h a <;>
    simp [SymplecticMatrix.weightCoord] at he

omit [Fintype l] in
theorem weightCoord_injective : Function.Injective (weightCoord l) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · exact False.elim (signedWeight_ne_zero y h.symm)
  · exact False.elim (signedWeight_ne_zero x h)
  · exact congrArg Sum.inr (SymplecticMatrix.weightCoord_injective h)

/-- The even linear condition embeds into the odd norm-one linear equations. -/
theorem evenEmbed_mem_lieMatrices (A : Matrix (l ⊕ l) (l ⊕ l) K)
    (hA : OrthogonalMatrix.IsAlt (A * OrthogonalMatrix.formMatrix l K +
      OrthogonalMatrix.formMatrix l K * A.transpose)) : evenEmbed A ∈ lieMatrices := by
  have hd : lieDefect (evenEmbed A) = Matrix.fromBlocks (0 : Matrix Unit Unit K) 0 0
      (A * OrthogonalMatrix.formMatrix l K + OrthogonalMatrix.formMatrix l K * A.transpose) := by
    simp [lieDefect, evenEmbed, formMatrix, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_transpose, Matrix.fromBlocks_add]
  have hQ : OrthogonalMatrix.IsAlt (lieDefect (evenEmbed A)) := by
    obtain ⟨U, hU⟩ := hA
    refine ⟨Matrix.fromBlocks (0 : Matrix Unit Unit K) 0 0 U, ?_⟩
    rw [hd, hU]
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j <;> simp
  refine (mem_lieMatrices_iff _).2 ⟨hQ, ?_⟩
  have ht := trace_evenPart_eq_zero hQ
  change A.trace = 0 at ht
  simpa [evenEmbed, Matrix.trace, Fintype.sum_sum_type] using ht

/-- Each short coefficient is present in every characteristic, even when
its axis-row coefficient `-2` vanishes. -/
theorem shortVector_mem_lieMatrices (a : l ⊕ l) : (shortVector a : Matrix _ _ K) ∈ lieMatrices := by
  apply (one_add_epsilonMatrix_equations_iff _).1
  have hs := shortMatrix_epsilon K a 1
  rw [one_smul] at hs
  rw [← hs]
  exact ⟨isAlt_shortMatrix_defect a (TrivSqZeroExt.inr (1 : K)),
    det_shortMatrix a (TrivSqZeroExt.inr (1 : K))⟩

variable (K)

/-- The actual Lie vector with prescribed admissible matrix. -/
def matrixLieVector (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    Additive (lieKernel (groupScheme l K) K) := (lieMatrixEquiv K).symm ⟨Y, hY⟩

@[simp] theorem lieMatrix_matrixLieVector (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    lieMatrix K (matrixLieVector K Y hY) = Y :=
  congrArg Subtype.val ((lieMatrixEquiv K).apply_symm_apply ⟨Y, hY⟩)

/-- The actual differential always satisfies the linearized norm-one equations. -/
theorem lieMatrix_mem (X : Additive (lieKernel (groupScheme l K) K)) :
    lieMatrix K X ∈ lieMatrices := by
  rw [lieMatrix_eq_tangentCoefficient]
  exact tangentCoefficient_mem K _

/-- The paired hyperbolic entries of an actual odd Lie matrix sum to zero. -/
theorem lieMatrix_swap_add (X : Additive (lieKernel (groupScheme l K) K)) (x y : l ⊕ l) :
    lieMatrix K X (Sum.inr x) (Sum.inr y.swap) +
      lieMatrix K X (Sum.inr y) (Sum.inr x.swap) = 0 :=
  ((OrthogonalMatrix.isAlt_lie_iff_swap _).mp
    (isAlt_evenPart_lieDefect ((mem_lieMatrices_iff _).mp (lieMatrix_mem K X)).1)).1 x y

/-- The forbidden double short-root entry of an actual odd Lie matrix vanishes. -/
theorem lieMatrix_swap_self (X : Additive (lieKernel (groupScheme l K) K)) (x : l ⊕ l) :
    lieMatrix K X (Sum.inr x) (Sum.inr x.swap) = 0 :=
  ((OrthogonalMatrix.isAlt_lie_iff_swap _).mp
    (isAlt_evenPart_lieDefect ((mem_lieMatrices_iff _).mp (lieMatrix_mem K X)).1)).2 x

variable {K}

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)

/-- The zero weight space consists exactly of diagonal admissible matrices. -/
theorem mem_weightSpace_zero_iff (X : Additive (lieKernel (groupScheme l K) K)) :
    X ∈ weightSpace (diagonalTorus l K) 0 ↔
      ∀ x y : Index l, x ≠ y → lieMatrix K X x y = 0 := by
  rw [mem_weightSpace_diagonalTorus_iff_support, LinearEquiv.map_zero]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  have hw : (0 : l → ℤ) = weightCoord l x - weightCoord l y ↔ x = y := by
    rw [eq_comm, sub_eq_zero]
    exact weightCoord_injective.eq_iff
  rw [hw]
  exact not_imp_comm

variable (l K) in
/-- Independent diagonal hyperbolic coordinates of the zero weight space. -/
def zeroWeightCoord : weightSpace (diagonalTorus l K) 0 →ₗ[K] (l → K) where
  toFun X a := lieMatrix K X.val (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl a))
  map_add' X Y := by
    funext a
    simp only [Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext a
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply]

/-- The zero weight coordinates are injective. -/
theorem zeroWeightCoord_injective : Function.Injective (zeroWeightCoord l K) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  apply Subtype.ext
  apply lieMatrix_injective K
  rw [Submodule.coe_zero, map_zero]
  have hd := (mem_weightSpace_zero_iff X.val).mp X.property
  have h0 (a : l) : lieMatrix K X.val (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl a)) = 0 :=
    congrFun hX a
  have ha := axis_diagonal_eq_zero (lieMatrix_mem K X.val)
  apply Matrix.ext
  intro x y
  rw [Matrix.zero_apply]
  by_cases hxy : x = y
  · subst y
    rcases x with x | x
    · cases x; exact ha
    · rcases x with a | a
      · exact h0 a
      · have he := lieMatrix_swap_add K X.val (Sum.inr a) (Sum.inl a)
        simpa [h0] using he
  · exact hd x y hxy

/-- Every diagonal hyperbolic coordinate family is realized in the zero weight space. -/
theorem zeroWeightCoord_surjective : Function.Surjective (zeroWeightCoord l K) := by
  intro d
  let Y := evenEmbed (Matrix.diagonal (Sum.elim d (fun a => -d a)))
  have hY : Y ∈ lieMatrices := evenEmbed_mem_lieMatrices _ (OrthogonalMatrix.isAlt_diagonal_lie d)
  let X := matrixLieVector K Y hY
  have hX : lieMatrix K X = Y := lieMatrix_matrixLieVector K _ _
  have hw : X ∈ weightSpace (diagonalTorus l K) 0 := by
    rw [mem_weightSpace_zero_iff, hX]
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y <;>
      simp_all [Y, evenEmbed]
  refine ⟨⟨X, hw⟩, ?_⟩
  funext a
  change lieMatrix K X (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl a)) = d a
  rw [hX]
  simp [Y, evenEmbed]

/-- The zero weight dimension of the odd diagonal torus is its rank. -/
theorem finrank_weightSpace_zero :
    Module.finrank K (weightSpace (diagonalTorus l K) 0) = Fintype.card l := by
  rw [(LinearEquiv.ofBijective (zeroWeightCoord l K)
    ⟨zeroWeightCoord_injective, zeroWeightCoord_surjective⟩).finrank_eq,
      Module.finrank_fintype_fun_eq_card]

variable (l K)

/-- The diagonal torus factored through the actual identity component. -/
def identityTorus : (𝔗).toGrp ⟶ identityComponent (groupScheme l K) :=
  IdentityComponent.torusHom (diagonalTorus l K) (isSplitSubtorus_diagonalTorus l K).1

@[reassoc (attr := simp)] theorem identityTorus_comp :
    identityTorus l K ≫ identityComponentι (groupScheme l K) = diagonalTorus l K :=
  IdentityComponent.torusHom_comp _ _

theorem isClosedSubgroup_identityTorus : IsClosedSubgroup (identityTorus l K) :=
  IdentityComponent.isClosedSubgroup_torusHom _ _ (isSplitSubtorus_diagonalTorus l K).2

/-- The actual odd diagonal torus is maximal in the identity component. -/
theorem isMaximalTorus_identityTorus : IsMaximalTorus (identityTorus l K) := by
  have : IsAffineHom (𝔗).toGrp.X.hom := isAffineHom_splitTorus _ _
  refine isMaximalTorus_of_finrank_zeroWeight _ (isSplitSubtorus_diagonalTorus l K).1
    (isClosedSubgroup_identityTorus l K) ?_
  rw [identityTorus, IdentityComponent.finrank_weightSpace, finrank_weightSpace_zero]
  have h := splitTorus.finrank_lieKernel (ULift.{u} l) K
  rw [Nat.card_ulift, Nat.card_eq_fintype_card] at h
  exact h.symm

theorem roots_identityTorus : roots (identityTorus l K) = roots (diagonalTorus l K) :=
  IdentityComponent.roots_torusHom _ _

variable {l K}

/-- The actual nonzero adjoint weights of the odd diagonal torus are exactly
`±e_a` and `±e_a±e_b` for distinct hyperbolic indices. -/
theorem mem_roots_iff (χ : characterLattice 𝔗) :
    χ ∈ roots (diagonalTorus l K) ↔
      (∃ a : l ⊕ l, GeneralLinear.characterCoordEquiv l K χ = SymplecticMatrix.weightCoord l a) ∨
      ∃ a b : l ⊕ l, OrthogonalMatrix.index a ≠ OrthogonalMatrix.index b ∧
        GeneralLinear.characterCoordEquiv l K χ =
          SymplecticMatrix.weightCoord l a - SymplecticMatrix.weightCoord l b := by
  constructor
  · intro hχ
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
    obtain ⟨x, y, hxy⟩ : ∃ x y, lieMatrix K X x y ≠ 0 := by
      by_contra h
      apply hX0
      apply lieMatrix_injective K
      rw [map_zero]
      refine Matrix.ext fun x y => ?_
      rw [Matrix.zero_apply]
      by_contra hne
      exact h ⟨x, y, hne⟩
    have hc := (mem_weightSpace_diagonalTorus_iff_support X χ).mp hX x y hxy
    rcases x with x | a <;> rcases y with y | b
    · cases x; cases y
      exact False.elim (hxy (axis_diagonal_eq_zero (lieMatrix_mem K X)))
    · cases x
      refine Or.inl ⟨b.swap, ?_⟩
      simpa only [weightCoord_axis, weightCoord_signed, zero_sub,
        OrthogonalMatrix.weightCoord_swap] using hc
    · cases y
      refine Or.inl ⟨a, ?_⟩
      simpa only [weightCoord_axis, weightCoord_signed, sub_zero] using hc
    · refine Or.inr ⟨a, b, fun hidx => ?_, hc⟩
      rcases OrthogonalMatrix.eq_or_eq_swap_of_index_eq hidx with rfl | rfl
      · apply hχ.1
        apply (GeneralLinear.characterCoordEquiv l K).injective
        rw [hc, sub_self, LinearEquiv.map_zero]
      · apply hxy
        simpa using lieMatrix_swap_self K X b.swap
  · rintro (⟨a, hc⟩ | ⟨a, b, hidx, hc⟩)
    · let Y : Matrix (Index l) (Index l) K := shortVector a.swap
      have hY : Y ∈ lieMatrices := shortVector_mem_lieMatrices _
      let X := matrixLieVector K Y hY
      have hX : lieMatrix K X = shortVector a.swap := lieMatrix_matrixLieVector K _ _
      refine ⟨fun h0 => ?_, ?_⟩
      · rw [h0, LinearEquiv.map_zero] at hc
        exact signedWeight_ne_zero a hc.symm
      · rw [Submodule.ne_bot_iff]
        refine ⟨X, ?_, fun h0 => ?_⟩
        · rw [mem_weightSpace_diagonalTorus_iff_support, hX, hc]
          intro z w hzw
          simp only [shortVector, Sum.swap_swap, Matrix.add_apply, Matrix.single_apply] at hzw
          by_cases h1 : Sum.inl () = z ∧ Sum.inr a.swap = w
          · rw [← h1.1, ← h1.2, weightCoord_axis, weightCoord_signed, zero_sub,
              OrthogonalMatrix.weightCoord_swap, neg_neg]
          · by_cases h2 : Sum.inr a = z ∧ Sum.inl () = w
            · rw [← h2.1, ← h2.2, weightCoord_signed, weightCoord_axis, sub_zero]
            · rw [ite_eq_right h1, ite_eq_right h2, add_zero] at hzw
              exact absurd rfl hzw
        · have he := congrArg (fun Z => lieMatrix K Z (Sum.inr a) (Sum.inl ())) h0
          simp [hX, shortVector] at he
    · have hab : a ≠ b := fun h => hidx (congrArg OrthogonalMatrix.index h)
      have hab' : ¬(b.swap = a ∧ a.swap = b) := fun h => hidx (by rw [← h.1, OrthogonalMatrix.index_swap])
      let Y : Matrix (Index l) (Index l) K :=
        evenEmbed (Matrix.single a b 1 - Matrix.single b.swap a.swap 1)
      have hY : Y ∈ lieMatrices := evenEmbed_mem_lieMatrices _ (OrthogonalMatrix.isAlt_rootVector_lie a b)
      let X := matrixLieVector K Y hY
      have hX : lieMatrix K X = Y := lieMatrix_matrixLieVector K _ _
      refine ⟨fun h0 => ?_, ?_⟩
      · rw [h0, LinearEquiv.map_zero, eq_comm, sub_eq_zero] at hc
        exact hab (SymplecticMatrix.weightCoord_injective hc)
      · rw [Submodule.ne_bot_iff]
        refine ⟨X, ?_, fun h0 => ?_⟩
        · rw [mem_weightSpace_diagonalTorus_iff_support, hX, hc]
          intro z w hzw
          rcases z with z | z <;> rcases w with w | w
          · exact False.elim (hzw rfl)
          · exact False.elim (hzw rfl)
          · exact False.elim (hzw rfl)
          · change ((Matrix.single a b (1 : K) - Matrix.single b.swap a.swap 1) :
              Matrix (l ⊕ l) (l ⊕ l) K) z w ≠ 0 at hzw
            simp only [Matrix.sub_apply, Matrix.single_apply] at hzw
            change _ = SymplecticMatrix.weightCoord l z - SymplecticMatrix.weightCoord l w
            by_cases h1 : a = z ∧ b = w
            · rw [← h1.1, ← h1.2]
            · by_cases h2 : b.swap = z ∧ a.swap = w
              · rw [← h2.1, ← h2.2, OrthogonalMatrix.weightCoord_swap, OrthogonalMatrix.weightCoord_swap]
                abel
              · rw [ite_eq_right h1, ite_eq_right h2, sub_zero] at hzw
                exact absurd rfl hzw
        · have he := congrArg (fun Z => lieMatrix K Z (Sum.inr a) (Sum.inr b)) h0
          simp only [hX, Y, evenEmbed, Matrix.fromBlocks_apply₂₂, map_zero, Matrix.zero_apply,
            Matrix.sub_apply, Matrix.single_apply_same, Matrix.single_apply, ite_eq_right hab', sub_zero] at he
          exact one_ne_zero he

end Langlands.GroupScheme.OddOrthogonalMatrix
