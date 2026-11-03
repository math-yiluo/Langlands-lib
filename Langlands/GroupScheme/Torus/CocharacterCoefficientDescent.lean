import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-! # Descent of group-algebra elements along field extensions

An element of a group algebra `L[Λ]` comes from `F[Λ]` as soon as all of its coefficients lie in
`F`. Two criteria for this are recorded: invariance under the Galois group of a finite Galois
extension, and equality of the two images in `(L ⊗[F] L)[Λ]`.
-/

open scoped TensorProduct

namespace Langlands.GroupScheme.CocharacterDescent

variable {Λ : Type*} [AddMonoid Λ]

/-- An element of `L[Λ]` all of whose coefficients lie in the image of `F` comes from `F[Λ]`. -/
theorem exists_mapAlgHom_ofId_eq {F L : Type*} [CommSemiring F] [Semiring L] [Algebra F L]
    (x : AddMonoidAlgebra L Λ) (hx : ∀ γ, x.coeff γ ∈ Set.range (algebraMap F L)) :
    ∃ y : AddMonoidAlgebra F Λ, AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId F L) y = x := by
  have hmem : x ∈ Set.range (AddMonoidAlgebra.map (M := Λ) (algebraMap F L).toAddMonoidHom) := by
    rw [AddMonoidAlgebra.range_map]
    exact hx
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  rw [← hy]
  ext γ
  simp

/-- **Galois descent of coefficients.** For a finite Galois extension `N / k`, an element of
`N[Λ]` fixed coefficientwise by every `k`-automorphism of `N` comes from `k[Λ]`. -/
theorem exists_mapAlgHom_ofId_eq_of_isGalois {k N : Type*} [Field k] [Field N] [Algebra k N]
    [FiniteDimensional k N] [IsGalois k N] (x : AddMonoidAlgebra N Λ)
    (hx : ∀ σ : N ≃ₐ[k] N, AddMonoidAlgebra.mapAlgHom Λ (σ : N →ₐ[k] N) x = x) :
    ∃ y : AddMonoidAlgebra k Λ, AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId k N) y = x := by
  refine exists_mapAlgHom_ofId_eq x fun γ => (IsGalois.mem_range_algebraMap_iff_fixed _).mpr ?_
  intro σ
  have h := congrArg (fun z : AddMonoidAlgebra N Λ => z.coeff γ) (hx σ)
  simpa using h

/-- An element `ℓ` of a nonzero algebra `L` over a field `F` with `ℓ ⊗ 1 = 1 ⊗ ℓ` in `L ⊗[F] L`
lies in the image of `F`. -/
theorem mem_range_algebraMap_of_tmul_one_eq_one_tmul {F L : Type*} [Field F] [CommRing L]
    [Nontrivial L] [Algebra F L] {ℓ : L} (h : ℓ ⊗ₜ[F] (1 : L) = 1 ⊗ₜ ℓ) :
    ℓ ∈ Set.range (algebraMap F L) := by
  have hex : Algebra.IsEffective F L := Algebra.IsEffective.of_faithfullyFlat F L
  obtain ⟨r, hr⟩ := (hex ℓ).mp (by simp [h])
  exact ⟨r, hr⟩

/-- **Equalizer descent of coefficients.** Over a field `F`, an element of `L[Λ]` with equal images
under the two coefficient maps `L → L ⊗[F] L` comes from `F[Λ]`. -/
theorem exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight {F L : Type*} [Field F]
    [CommRing L] [Nontrivial L] [Algebra F L] (x : AddMonoidAlgebra L Λ)
    (hx : AddMonoidAlgebra.mapAlgHom Λ (Algebra.TensorProduct.includeLeft : L →ₐ[F] L ⊗[F] L) x =
      AddMonoidAlgebra.mapAlgHom Λ (Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L) x) :
    ∃ y : AddMonoidAlgebra F Λ, AddMonoidAlgebra.mapAlgHom Λ (Algebra.ofId F L) y = x := by
  refine exists_mapAlgHom_ofId_eq x fun γ => mem_range_algebraMap_of_tmul_one_eq_one_tmul ?_
  have h := congrArg (fun z : AddMonoidAlgebra (L ⊗[F] L) Λ => z.coeff γ) hx
  simpa using h

end Langlands.GroupScheme.CocharacterDescent
