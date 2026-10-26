import Langlands.Representation.Parabolic.FlattenedOppositeUnipotentComparisonProof
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation

/-! Representative-preserving normalized comparison of the actual composed
and flattened opposite Jacquet quotients. -/

noncomputable section

namespace Langlands.Parabolic.FlattenedOppositeComparison

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

private theorem half_of_full
    (hδ : (T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom = T.leviModulus (B.flatten S)) :
    (T.composedLeviHalfModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom =
        T.leviHalfModulus (B.flatten S) := by
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
    ((T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) = _
  rw [hδ]
  rfl

variable (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))

private theorem standard_mk (m : (B.flatten S).Levi F.Carrier) (v : A) :
    (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) A).ρ m
      (Jacquet.mk A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier) v) =
      (T.leviHalfModulus (B.flatten S) m : ℂ) •
        Jacquet.mk A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier)
          (A.ρ ((B.flatten S).leviEmbedding F.Carrier m) v) := by
  change (Jacquet.inverseHalfCharacter
      ((T.leviModulus (B.flatten S)).comp
        ((B.flatten S).leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
      ((B.flatten S).leviEquiv F.Carrier m) : ℂ) •
      Jacquet.mk A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier)
        (A.ρ ((B.flatten S).leviEmbedding F.Carrier m) v) = _
  congr 1
  simp [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, PadicField.TopologicalData.leviHalfModulus]

private def quotientEquiv :
    ComposedOppositeJacquetModule B S A.ρ ≃ₗ[ℂ]
      Jacquet.Coinvariants A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier) :=
  quotientCongr A.ρ (flattenedOppositeUnipotentComparison F.Carrier n B S)

private theorem quotientEquiv_mk (v : A) :
    quotientEquiv B S A (composedOppositeJacquetMk B S A.ρ v) =
      Jacquet.mk A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier) v :=
  quotientCongr_mk A.ρ (flattenedOppositeUnipotentComparison F.Carrier n B S) v

private def normalizedEquivOfModulus
    (hδ : (T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom = T.leviModulus (B.flatten S)) :
    Representation.Equiv
      ((T.normalizedComposedOppositeJacquet B S A.ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) A).ρ :=
  Representation.Equiv.mk (quotientEquiv B S A) (by
    intro m
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := composedOppositeJacquetMk_surjective B S A.ρ x
    change quotientEquiv B S A
      (T.normalizedComposedOppositeJacquet B S A.ρ
        (flattenedLeviEquiv F.Carrier B S m) (composedOppositeJacquetMk B S A.ρ v)) =
      (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) A).ρ m
        (quotientEquiv B S A (composedOppositeJacquetMk B S A.ρ v))
    rw [T.normalizedComposedOppositeJacquet_mk, map_smul,
      quotientEquiv_mk, quotientEquiv_mk, standard_mk,
      flattenedLeviEquiv_embedding]
    have hhalf := DFunLike.congr_fun (half_of_full T B S hδ) m
    change T.composedLeviHalfModulus B S (flattenedLeviEquiv F.Carrier B S m) =
      T.leviHalfModulus (B.flatten S) m at hhalf
    rw [hhalf])

private theorem normalizedComparisonOfModulus
    (hδ : (T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom = T.leviModulus (B.flatten S)) :
    ∃ φ : Representation.Equiv
      ((T.normalizedComposedOppositeJacquet B S A.ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) A).ρ,
      ∀ v : A,
        φ (composedOppositeJacquetMk B S A.ρ v) =
          Jacquet.mk A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier) v :=
  ⟨normalizedEquivOfModulus T B S A hδ, quotientEquiv_mk B S A⟩

end Langlands.Parabolic.FlattenedOppositeComparison

namespace Langlands.Parabolic

universe uK uF uV

/-- Equality of the actual opposite radicals and their normalized quotients. -/
theorem flattenedOppositeJacquetComparison :
    FlattenedOppositeJacquetComparisonStatement.{uK,uF,uV} := by
  refine ⟨flattenedOppositeUnipotentComparison, ?_⟩
  intro p _ F T n B S A
  exact FlattenedOppositeComparison.normalizedComparisonOfModulus T B S A
    (T.composedLeviModulus_flattened B S)

end Langlands.Parabolic
