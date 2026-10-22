import Langlands.Global.AdelicFunctoriality.NormReduction

/-! # Quotient descent conditional on the exact principal-norm formula

The raw norm is the constructed product of actual local determinant norms.
The arithmetic principal formula remains an explicit hypothesis here.
-/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain
open scoped NumberField

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The principal-adele formula lifts to the actual unit embeddings. -/
theorem ideleNorm_principal_of_principal_formula
    (h : ∀ x : L,
      adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
        algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x))
    (x : Lˣ) :
    ideleNorm (K := K) (IdeleGroup.unitEmbedding (𝓞 L) L x) =
      IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K) x) := by
  apply Units.ext
  exact h x.val

/-- The arithmetic principal formula makes the raw norm preserve principal ideles. -/
theorem ideleNorm_principal_le_of_principal_formula
    (h : ∀ x : L,
      adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
        algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x)) :
    IdeleGroup.principalSubgroup (𝓞 L) L ≤
      (IdeleGroup.principalSubgroup (𝓞 K) K).comap
        (ideleNorm (K := K) (L := L)).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Units.map (Algebra.norm K) x,
    (ideleNorm_principal_of_principal_formula h x).symm⟩

/-- Descent of the constructed raw norm, given its exact arithmetic principal formula. -/
def ideleClassNormOfPrincipalFormula
    (h : ∀ x : L,
      adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
        algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x)) :
    IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K where
  __ := QuotientGroup.map _ _ (ideleNorm (K := K) (L := L)).toMonoidHom
    (ideleNorm_principal_le_of_principal_formula h)
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp (ideleNorm (K := K) (L := L)).continuous

@[simp] theorem ideleClassNormOfPrincipalFormula_mk
    (h : ∀ x : L,
      adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
        algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x))
    (a : IdeleGroup (𝓞 L) L) :
    ideleClassNormOfPrincipalFormula h (QuotientGroup.mk a) =
      QuotientGroup.mk (ideleNorm (K := K) a) := rfl

/-- The representative formula uniquely determines the continuous quotient norm. -/
theorem ideleClassNormOfPrincipalFormula_unique
    (h : ∀ x : L,
      adeleNorm (K := K) (algebraMap L (AdeleRing (𝓞 L) L) x) =
        algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x))
    (f : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K)
    (hf : ∀ a : IdeleGroup (𝓞 L) L,
      f (QuotientGroup.mk a) = QuotientGroup.mk (ideleNorm (K := K) a)) :
    f = ideleClassNormOfPrincipalFormula h := by
  ext a
  exact QuotientGroup.induction_on a hf

/-- Combining determinant compatibility with descent; finite tensor bijectivity
is still an explicit unproved arithmetic premise. -/
def ideleClassNormOfFiniteTensorComparison
    (h : ∀ p : HeightOneSpectrum (𝓞 K),
      Function.Bijective (finiteTensorMap (L := L) p)) :
    IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K :=
  ideleClassNormOfPrincipalFormula
    (adeleNorm_principal_of_finiteTensorMap_bijective h)

@[simp] theorem ideleClassNormOfFiniteTensorComparison_mk
    (h : ∀ p : HeightOneSpectrum (𝓞 K),
      Function.Bijective (finiteTensorMap (L := L) p))
    (a : IdeleGroup (𝓞 L) L) :
    ideleClassNormOfFiniteTensorComparison h (QuotientGroup.mk a) =
      QuotientGroup.mk (ideleNorm (K := K) a) := rfl

end Langlands.Global.AdelicFunctoriality
