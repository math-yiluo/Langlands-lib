import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeClosedQuotient
import Langlands.GroupScheme.Torus.MultiplicativeTypeKernelFactorizationStatement
import Langlands.GroupScheme.FppfKernelFactorization

/-! # Canonical factorization once the actual kernel has multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- Quotient existence and fpqc descent give the full canonical factorization
as soon as the actual kernel is known to be of multiplicative type. -/
theorem exists_factorization_of_multiplicativeType_kernel
    {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G)
    (hH : IsMultiplicativeType H) (hK : IsMultiplicativeType (kernel f))
    (hG : IsSeparated G.X.hom) :
    ∃ (Q : GroupScheme S) (q : H ⟶ Q) (v : Q ⟶ G),
      IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q ∧
      IsAffineHom q.hom.hom.left ∧ Mono v.hom.hom ∧ q ≫ v = f := by
  have : IsSeparated G.X.hom := hG
  obtain ⟨Q, q, hQ, hq, hqa⟩ :=
    exists_quotient_of_multiplicativeType hH hK (kernelι f)
      (inferInstance : IsClosedImmersion (kernelι f).hom.hom.left)
  have : IsAffineHom q.hom.hom.left := hqa
  obtain ⟨v, hv, hfac⟩ := FppfKernelFactorization.exists_mono_factor f q hq
  exact ⟨Q, q, v, hQ, hq, hqa, hv, hfac⟩

/-- The actual canonical factorization chosen from the multiplicative-type kernel. -/
def factorizationOfMultiplicativeTypeKernel
    {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G)
    (hH : IsMultiplicativeType H) (hK : IsMultiplicativeType (kernel f))
    (hG : IsSeparated G.X.hom) :
    Σ (Q : GroupScheme S), Σ (q : H ⟶ Q), {v : Q ⟶ G //
      IsMultiplicativeType Q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q ∧
      IsAffineHom q.hom.hom.left ∧ Mono v.hom.hom ∧ q ≫ v = f} := by
  let h := exists_factorization_of_multiplicativeType_kernel f hH hK hG
  let Q := Classical.choose h
  let hQ := Classical.choose_spec h
  let q := Classical.choose hQ
  let hq := Classical.choose_spec hQ
  exact ⟨Q, q, Classical.choose hq, Classical.choose_spec hq⟩

/-- The published exact target reduces to its kernel-multiplicative-type clause.
The kernel criterion remains an explicit premise of this reduction. -/
theorem multiplicativeTypeKernelFactorization_of_kernelCriterion
    (hK : ∀ (S : Scheme.{u}) (H G : GroupScheme S) (f : H ⟶ G),
      IsMultiplicativeType H → IsSeparated G.X.hom →
      (IsLocallyNoetherian S ∨
        (LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧
          QuasiSeparated G.X.hom)) →
      IsMultiplicativeType (kernel f)) :
    MultiplicativeTypeKernelFactorizationStatement.{u} := by
  intro S H G f hH hG hfin
  have hk := hK S H G f hH hG hfin
  exact ⟨hk, exists_factorization_of_multiplicativeType_kernel f hH hk hG⟩

end Langlands.GroupScheme
