import Langlands.Global.Arithmetic.ClassFieldStatement
import Langlands.Global.AdelicFunctoriality.Norm

/-!
# Norm-image comparison for finite abelian global reciprocity

The norm is the actual product of local determinant norms, followed by
the base idele-class quotient. No norm on the extension's idele-class
quotient, or theorem asserting its existence, is supplied as input.
-/

noncomputable section

universe u v

namespace Langlands.Global

/-- The kernel of normalized finite abelian reciprocity is the image
of the actual idele norm in the base idele-class group. -/
def ArtinNormKernelStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    ∀ ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
      Function.Surjective ρ →
      HasArithmeticArtinNormalization ρ.toMonoidHom →
      ρ.toMonoidHom.ker =
        ((ideleClassMap K).comp
          (AdelicFunctoriality.ideleNorm (K := K) (L := L))).toMonoidHom.range

/-- At every finite or infinite place, the inverse image of the global
norm subgroup is exactly the corresponding actual local norm subgroup. -/
def LocalGlobalNormImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    (∀ (p : FinitePlace K) (q : FinitePlace L) [q.asIdeal.LiesOver p.asIdeal],
      (((ideleClassMap K).comp
        (AdelicFunctoriality.ideleNorm (K := K) (L := L))).toMonoidHom.range).comap
          (finiteClassInclusion K p).toMonoidHom =
        (AdelicFunctoriality.FiniteExtension.localUnitNorm p q).toMonoidHom.range) ∧
    (∀ (p : InfinitePlace K) (q : InfinitePlace L) [q.LiesOver p],
      (((ideleClassMap K).comp
        (AdelicFunctoriality.ideleNorm (K := K) (L := L))).toMonoidHom.range).comap
          (infiniteClassInclusion K p).toMonoidHom =
        (AdelicFunctoriality.InfiniteExtension.localUnitNorm p q).toMonoidHom.range)

/-- The image of the actual idele norm has index equal to the degree
for a finite abelian extension of number fields. -/
def AbelianIdeleNormIndexStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    (((ideleClassMap K).comp
      (AdelicFunctoriality.ideleNorm (K := K) (L := L))).toMonoidHom.range).index =
        Module.finrank K L

/-- A Hecke character kills the actual idele norms exactly when it
factors uniquely through normalized finite abelian reciprocity. -/
def HeckeNormFactorizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    ∀ (ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L)) (χ : HeckeCharacter K),
      Function.Surjective ρ →
      HasArithmeticArtinNormalization ρ.toMonoidHom →
      ((∀ a : Ideles L,
          χ (ideleClassMap K (AdelicFunctoriality.ideleNorm (K := K) a)) = 1) ↔
        ∃! θ : (L ≃ₐ[K] L) →ₜ* ℂˣ, ∀ x : IdeleClasses K, θ (ρ x) = χ x)

/-- The concrete global and local norm-image, norm-index and
character-factorization forms of finite abelian global reciprocity. -/
def ArtinNormComparisonStatement : Prop :=
  ArtinNormKernelStatement.{u,v} ∧
  LocalGlobalNormImageStatement.{u,v} ∧
  AbelianIdeleNormIndexStatement.{u,v} ∧
  HeckeNormFactorizationStatement.{u,v}

end Langlands.Global
