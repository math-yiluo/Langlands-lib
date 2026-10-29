import Langlands.Representation.Parabolic.FlattenedJacquetComparisonStatement
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation

/-! Representative-preserving comparison of the actual composed and flattened
upper radicals and their normalized Jacquet quotients. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric
open GeneralLinear.BlockShape

universe uK

variable (K : Type uK) [CommRing K] {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)

private theorem composed_le_flattened :
    composedUnipotent K B S ≤ (B.flatten S).unipotentSubgroup K := by
  intro g hg
  obtain ⟨hB, hI⟩ := (mem_leviPreimage_iff K B _ g).mp hg
  have hinner := (mem_refinedUnipotent K B S _).mp hI
  have hBzero := (B.mem_parabolic_iff K g).mp hB
  have hzero : ∀ (i i' : Fin B.length) (j : Fin (S i).length)
      (j' : Fin (S i').length) (a : Fin ((S i).size j))
      (b : Fin ((S i').size j')),
      i' < i ∨ (i' = i ∧ j'.val < j.val) →
        g (B.index i ((S i).index j a)) (B.index i' ((S i').index j' b)) = 0 := by
    intro i i' j j' a b hij
    rcases hij with hii' | ⟨hii', hjj'⟩
    · exact hBzero i i' _ _ hii'
    · subst i'
      have hi := ((S i).mem_unipotentSubgroup_iff K _).mp (hinner i)
      have hz := ((S i).mem_parabolic_iff K _).mp hi.1 j j' a b hjj'
      simpa only [leviProjection_apply] using hz
  apply ((B.flatten S).mem_unipotentSubgroup_iff K g).mpr
  constructor
  · rw [(B.flatten S).mem_parabolic_iff]
    intro k k' a b hkk'
    rw [B.flatten_index S k a, B.flatten_index S k' b]
    apply hzero
    apply (B.flattenBlockEquiv_lt_iff S _ _).mp
    simpa only [Equiv.apply_symm_apply] using hkk'
  · intro k a b
    rw [B.flatten_index S k a, B.flatten_index S k b]
    have hi := ((S ((B.flattenBlockEquiv S).symm k).1).mem_unipotentSubgroup_iff
      K _).mp (hinner ((B.flattenBlockEquiv S).symm k).1)
    exact hi.2 ((B.flattenBlockEquiv S).symm k).2 a b

/-- The actual composed upper radical equals the standard flattened radical. -/
theorem flattenedUnipotentComparison :
    FlattenedUnipotentComparisonStatement.{uK} := by
  intro K _ n B S
  exact le_antisymm (composed_le_flattened K B S)
    (B.flatten_unipotentSubgroup_le S K)

end Langlands.Parabolic

namespace Langlands.Parabolic.FlattenedComparison

open GeneralLinear Geometric

universe uF uV

private def quotientCongr {R G V : Type*} [CommRing R] [Group G]
    [AddCommGroup V] [Module R V] (ρ : Representation R G V)
    {N M : Subgroup G} (h : N = M) :
    Jacquet.Coinvariants ρ N ≃ₗ[R] Jacquet.Coinvariants ρ M := by
  cases h
  exact LinearEquiv.refl R _

private theorem quotientCongr_mk {R G V : Type*} [CommRing R] [Group G]
    [AddCommGroup V] [Module R V] (ρ : Representation R G V)
    {N M : Subgroup G} (h : N = M) (v : V) :
    quotientCongr ρ h (Jacquet.mk ρ N v) = Jacquet.mk ρ M v := by
  cases h
  rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem half_flattened :
    (T.composedLeviHalfModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom =
        T.leviHalfModulus (B.flatten S) := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
    ((T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) = _
  rw [T.composedLeviModulus_flattened B S]
  rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)

private def quotientEquiv :
    ComposedJacquetModule B S ρ ≃ₗ[ℂ] (B.flatten S).JacquetModule ρ :=
  (quotientCongr ρ (flattenedUnipotentComparison F.Carrier n B S)).trans
    ((B.flatten S).jacquetModuleEquiv ρ).symm

private theorem quotientEquiv_mk (v : V) :
    quotientEquiv B S ρ (composedJacquetMk B S ρ v) =
      (B.flatten S).jacquetMk ρ v := by
  change ((B.flatten S).jacquetModuleEquiv ρ).symm
    (quotientCongr ρ (flattenedUnipotentComparison F.Carrier n B S)
      (Jacquet.mk ρ (composedUnipotent F.Carrier B S) v)) = _
  rw [quotientCongr_mk, ← (B.flatten S).jacquetModuleEquiv_mk ρ v,
    LinearEquiv.symm_apply_apply]

private def normalizedEquiv :
    Representation.Equiv
      ((T.normalizedComposedJacquet B S ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (T.normalizedJacquet (B.flatten S) ρ) :=
  Representation.Equiv.mk (quotientEquiv B S ρ) (by
    intro m
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (composedUnipotent F.Carrier B S) x
    change quotientEquiv B S ρ
      (T.normalizedComposedJacquet B S ρ (flattenedLeviEquiv F.Carrier B S m)
        (composedJacquetMk B S ρ v)) =
      T.normalizedJacquet (B.flatten S) ρ m
        (quotientEquiv B S ρ (composedJacquetMk B S ρ v))
    rw [T.normalizedComposedJacquet_mk, map_smul,
      quotientEquiv_mk, quotientEquiv_mk,
      T.normalizedJacquet_mk_eq_inv_halfModulus, Units.smul_def,
      flattenedLeviEquiv_embedding]
    have hhalf := DFunLike.congr_fun (half_flattened T B S) m
    change T.composedLeviHalfModulus B S (flattenedLeviEquiv F.Carrier B S m) =
      T.leviHalfModulus (B.flatten S) m at hhalf
    change (((T.composedLeviHalfModulus B S
      (flattenedLeviEquiv F.Carrier B S m))⁻¹ : ℂˣ) : ℂ) •
        (B.flatten S).jacquetMk ρ
          (ρ ((B.flatten S).leviEmbedding F.Carrier m) v) = _
    rw [hhalf])

private theorem normalizedComparison :
    ∃ φ : Representation.Equiv
      ((T.normalizedComposedJacquet B S ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (T.normalizedJacquet (B.flatten S) ρ),
      ∀ v : V, φ (composedJacquetMk B S ρ v) = (B.flatten S).jacquetMk ρ v :=
  ⟨normalizedEquiv T B S ρ, quotientEquiv_mk B S ρ⟩

end Langlands.Parabolic.FlattenedComparison

namespace Langlands.Parabolic

universe uK uF uV

/-- Equality of the actual upper radicals and normalized quotient representations. -/
theorem flattenedJacquetComparison :
    FlattenedJacquetComparisonStatement.{uK,uF,uV} := by
  refine ⟨flattenedUnipotentComparison, ?_⟩
  intro p _ F T n B S V _ _ ρ
  exact FlattenedComparison.normalizedComparison T B S ρ

end Langlands.Parabolic
