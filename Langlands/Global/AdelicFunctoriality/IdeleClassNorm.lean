import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.NormAssemblyProof

/-! # The continuous norm on actual idele classes -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField
open scoped NumberField

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The constructed adelic norm agrees with the field norm on diagonal adeles. -/
@[simp] theorem adeleNorm_principal (x : L) :
    adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x) :=
  normAssembly.1 completedTensorComparison K L x

/-- On principal ideles, the norm is induced by the genuine field-unit norm. -/
@[simp] theorem ideleNorm_principal (x : Lˣ) :
    ideleNorm (K := K) (IdeleGroup.unitEmbedding (𝓞 L) L x) =
      IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K) x) :=
  ideleNorm_principal_of_principal_formula adeleNorm_principal x

/-- The norm of a principal idele is principal. -/
theorem ideleNorm_principal_le :
    IdeleGroup.principalSubgroup (𝓞 L) L ≤
      (IdeleGroup.principalSubgroup (𝓞 K) K).comap
        (ideleNorm (K := K) (L := L)).toMonoidHom :=
  ideleNorm_principal_le_of_principal_formula adeleNorm_principal

/-- The norm on actual idele classes, with their quotient topologies. -/
def ideleClassNorm : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K :=
  ideleClassNormOfPrincipalFormula adeleNorm_principal

/-- The quotient norm sends the class of an idele to the class of its norm. -/
@[simp] theorem ideleClassNorm_mk (a : IdeleGroup (𝓞 L) L) :
    ideleClassNorm (K := K) (QuotientGroup.mk a) =
      QuotientGroup.mk (ideleNorm (K := K) a) := rfl

theorem continuous_ideleClassNorm :
    Continuous (ideleClassNorm (K := K) (L := L)) :=
  (ideleClassNorm (K := K) (L := L)).continuous

/-- The norm of the class of a principal idele is the identity class. -/
@[simp] theorem ideleClassNorm_principal (x : Lˣ) :
    ideleClassNorm (K := K)
      (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 L) L x)) = 1 := by
  rw [ideleClassNorm_mk, ideleNorm_principal]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (Algebra.norm K) x, rfl⟩

/-- The representative formula uniquely determines this continuous homomorphism. -/
theorem ideleClassNorm_unique
    (f : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K)
    (hf : ∀ a : IdeleGroup (𝓞 L) L,
      f (QuotientGroup.mk a) = QuotientGroup.mk (ideleNorm (K := K) a)) :
    f = ideleClassNorm :=
  ideleClassNormOfPrincipalFormula_unique adeleNorm_principal f hf

end Langlands.Global.AdelicFunctoriality
