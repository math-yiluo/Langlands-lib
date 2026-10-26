import Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation

/-!
# Equivariant surjectivity of the flattened normalized Jacquet quotient

Canonical positive halves of the published full modulus comparison identify
the two normalized actions on quotient representatives.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric
open scoped NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

theorem flattenedLeviHalfModulus
    (m : (B.flatten S).Levi F.Carrier) :
    T.leviHalfModulus (B.flatten S) m =
      T.leviHalfModulus B (flattenedLeviEquiv F.Carrier B S m).val *
        T.refinedLeviHalfModulus B S (flattenedLeviEquiv F.Carrier B S m) := by
  have hfull : T.composedLeviModulus B S (flattenedLeviEquiv F.Carrier B S m) =
      T.leviModulus (B.flatten S) m :=
    DFunLike.congr_fun (T.composedLeviModulus_flattened B S) m
  have hhalf : T.leviHalfModulus (B.flatten S) m =
      T.composedLeviHalfModulus B S (flattenedLeviEquiv F.Carrier B S m) := by
    change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        ((Units.map NNReal.sqrtHom.toMonoidHom) (T.leviModulus (B.flatten S) m)) =
      (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        ((Units.map NNReal.sqrtHom.toMonoidHom)
          (T.composedLeviModulus B S (flattenedLeviEquiv F.Carrier B S m)))
    rw [hfull]
  rw [hhalf, T.composedLeviHalfModulus_eq]
  rfl

theorem flattenedLeviInverseHalfModulus
    (m : (B.flatten S).Levi F.Carrier) :
    (T.leviHalfModulus (B.flatten S) m)⁻¹ =
      (T.leviHalfModulus B (flattenedLeviEquiv F.Carrier B S m).val)⁻¹ *
        T.refinedLeviInverseHalfModulus B S (flattenedLeviEquiv F.Carrier B S m) := by
  rw [T.flattenedLeviHalfModulus B S]
  exact _root_.mul_inv _ _

end Langlands.PadicField.TopologicalData

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)

@[simp]
theorem flattenJacquetMap_mk (v : V) :
    CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
        ((B.flatten S).jacquetMk ρ v) =
      refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v) := rfl

theorem normalizedIteratedJacquet_mk
    (m : refinedLevi F.Carrier B S) (v : V) :
    T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ) m
        (refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v)) =
      ((T.refinedLeviInverseHalfModulus B S m : ℂ) *
        ((T.leviHalfModulus B m.val)⁻¹ : ℂˣ)) •
        refinedJacquetMk B S (T.normalizedJacquet B ρ)
          (B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m.val) v)) := by
  rw [T.normalizedRefinedJacquet_mk, T.normalizedJacquet_mk_eq_inv_halfModulus,
    Units.smul_def, map_smul, smul_smul]

theorem flattenJacquetMap_action_mk
    (m : (B.flatten S).Levi F.Carrier) (v : V) :
    CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
        (T.normalizedJacquet (B.flatten S) ρ m ((B.flatten S).jacquetMk ρ v)) =
      ((T.leviHalfModulus (B.flatten S) m)⁻¹ : ℂˣ) •
        refinedJacquetMk B S (T.normalizedJacquet B ρ)
          (B.jacquetMk ρ (ρ ((B.flatten S).leviEmbedding F.Carrier m) v)) := by
  rw [T.normalizedJacquet_mk_eq_inv_halfModulus, Units.smul_def, map_smul,
    flattenJacquetMap_mk, Units.smul_def]

theorem flattenJacquetMap_equivariant_mk
    (m : (B.flatten S).Levi F.Carrier) (v : V) :
    CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
        (T.normalizedJacquet (B.flatten S) ρ m ((B.flatten S).jacquetMk ρ v)) =
      T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)
        (flattenedLeviEquiv F.Carrier B S m)
        (CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
          ((B.flatten S).jacquetMk ρ v)) := by
  rw [flattenJacquetMap_action_mk T B S ρ m v]
  conv_rhs =>
    rw [flattenJacquetMap_mk T B S ρ v,
      normalizedIteratedJacquet_mk T B S ρ (flattenedLeviEquiv F.Carrier B S m) v]
  simp only [Units.smul_def]
  apply congrArg₂
    (fun (a : ℂ) (z : RefinedJacquetModule B S (T.normalizedJacquet B ρ)) => a • z)
  · exact (congrArg (fun z : ℂˣ => (z : ℂ))
      (T.flattenedLeviInverseHalfModulus B S m)).trans (mul_comm _ _)
  · exact congrArg
      (fun g : GeneralLinear n F.Carrier =>
        refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ (ρ g v)))
      (flattenedLeviEquiv_embedding F.Carrier B S m).symm

theorem flattenJacquetMap_equivariant
    (m : (B.flatten S).Levi F.Carrier) (x : (B.flatten S).JacquetModule ρ) :
    CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
        (T.normalizedJacquet (B.flatten S) ρ m x) =
      T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)
        (flattenedLeviEquiv F.Carrier B S m)
        (CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ x) := by
  obtain ⟨v, rfl⟩ := (B.flatten S).jacquetMk_surjective ρ x
  exact flattenJacquetMap_equivariant_mk T B S ρ m v

def flattenedJacquetQuotientMap :
    (T.normalizedJacquet (B.flatten S) ρ).IntertwiningMap
      ((T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom) where
  toLinearMap := CuspidalSupport.MinimalJacquet.flattenJacquetMap T B S ρ
  isIntertwining' m := LinearMap.ext fun x =>
    flattenJacquetMap_equivariant T B S ρ m x

/-- The prescribed flattened quotient map is a surjective intertwiner for the
standard flattened and transported iterated normalized Jacquet actions. -/
theorem flattenedJacquetQuotient :
    FlattenedJacquetQuotientStatement.{uF,uV} := by
  intro p _ F T n B S V _ _ ρ
  refine ⟨flattenedJacquetQuotientMap T B S ρ, rfl, ?_⟩
  exact CuspidalSupport.MinimalJacquet.flattenJacquetMap_surjective T B S ρ

end Langlands.Parabolic
