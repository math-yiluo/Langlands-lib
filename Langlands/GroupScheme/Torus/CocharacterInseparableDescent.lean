import Langlands.GroupScheme.Torus.CocharacterDatum
import Langlands.GroupScheme.Torus.CocharacterCoefficientDescent
import Langlands.GroupScheme.Torus.FrobeniusTensorPower

/-! # Purely inseparable descent of cocharacter data

Let `L / F` be an extension of fields over `k` in which every `p ^ e`-th power of `L` lies in `F`,
where `p` is the exponential characteristic of `k`. Suppose that the points of `Z` are unchanged
after taking `p ^ e`-th powers by every algebra map that agrees with the identity after taking
`p ^ e`-th powers. Then a cocharacter datum over `L[Λ]` comes from one over `F[Λ]` of the same
weight: the quotient of its two images in `(L ⊗[F] L)[Λ]` is multiplicative and killed by `p ^ e`,
hence trivial, so its coordinates descend to `F[Λ]`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

/-- **Purely inseparable descent of cocharacter data.** Let `p` be the exponential characteristic
of `k` and suppose that for every `k`-algebra `A` and every `k`-algebra map `g : A → A` with
`a ^ p ^ e = g a ^ p ^ e` for all `a`, the points of `Z` satisfy `x ^ p ^ e = (g_* x) ^ p ^ e`.
If every `p ^ e`-th power of `L` lies in `F`, then a cocharacter datum for `χ` of weight `m` over
`L[Λ]` gives one of the same weight over `F[Λ]`. -/
theorem IsDatum.exists_of_pow_mem_range {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffine Z.toGrp.X.left]
    {Λ : Type u} [AddCommGroup Λ] [IsAddTorsionFree Λ] (p e : ℕ) [ExpChar k p]
    (hF : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : A →ₐ[k] A),
      (∀ a : A, a ^ p ^ e = g a ^ p ^ e) →
        ∀ x : Lie.AffinePoints Z.toGrp A, x ^ p ^ e = Lie.affineMap Z.toGrp g x ^ p ^ e)
    {F L : Type u} [Field F] [Field L] [Algebra k F] [Algebra k L] [Algebra F L]
    [IsScalarTower k F L] (hL : ∀ ℓ : L, ℓ ^ p ^ e ∈ (algebraMap F L).range)
    {χ : characterLattice Z} {m : Λ} {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)}
    (hx : IsDatum χ m x) :
    ∃ x' : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ), IsDatum χ m x' := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  -- The two inclusions `L → L ⊗[F] L` and the fold map `a ⊗ b ↦ 1 ⊗ a b`, over `k`.
  let i₁ : L →ₐ[k] L ⊗[F] L :=
    (Algebra.TensorProduct.includeLeft : L →ₐ[F] L ⊗[F] L).restrictScalars k
  let i₂ : L →ₐ[k] L ⊗[F] L :=
    (Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).restrictScalars k
  let φ : L ⊗[F] L →ₐ[k] L ⊗[F] L :=
    ((Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).comp
      (Algebra.TensorProduct.lmul' F)).restrictScalars k
  have hφ₁ : φ.comp i₁ = i₂ := by
    ext ℓ
    simp [φ, i₁, i₂]
  have hφ₂ : φ.comp i₂ = i₂ := by
    ext ℓ
    simp [φ, i₂]
  let g : AddMonoidAlgebra (L ⊗[F] L) Λ →ₐ[k] AddMonoidAlgebra (L ⊗[F] L) Λ :=
    AddMonoidAlgebra.mapAlgHom Λ φ
  have hg : ∀ a, a ^ p ^ e = g a ^ p ^ e := fun a =>
    CocharacterDescent.pow_eq_pow_mapAlgHom_includeRight_lmul' p e
      (fun ℓ => by obtain ⟨c, hc⟩ := hL ℓ; exact ⟨c, hc⟩) a
  have hgcomp : ∀ (f : L →ₐ[k] L ⊗[F] L) (y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)),
      Lie.affineMap Z.toGrp g (coeffMap f y) = coeffMap (φ.comp f) y := by
    intro f y
    have h : g.comp (AddMonoidAlgebra.mapAlgHom Λ f) = AddMonoidAlgebra.mapAlgHom Λ (φ.comp f) := by
      apply AlgHom.ext
      intro a
      ext γ
      simp [g]
    rw [coeffMap, coeffMap, ← Lie.affineMap_comp, h]
  -- The quotient of the two images of `x` in `(L ⊗[F] L)[Λ]`.
  let v := coeffMap i₁ x * (coeffMap i₂ x)⁻¹
  have hgv : Lie.affineMap Z.toGrp g v = 1 := by
    rw [map_mul, map_inv, hgcomp, hgcomp, hφ₁, hφ₂, mul_inv_cancel]
  have hvq : v ^ p ^ e = 1 := by
    rw [hF _ g hg v, hgv, one_pow]
  have hvmult : IsMult v := (hx.mult.coeff_map i₁).mul (hx.mult.coeff_map i₂).inv
  have hq : p ^ e ≠ 0 := pow_ne_zero e (expChar_ne_zero k p)
  have hv : v = 1 := by
    apply expMap_nsmul_injective (Z := Z) (S := L ⊗[F] L) (Λ := Λ) hq
    rw [hvmult.expMap_nsmul, hvq, map_one]
  have hx₁₂ : coeffMap i₁ x = coeffMap i₂ x := mul_inv_eq_one.mp hv
  -- Descend the coordinates of `x` to `F[Λ]`.
  let f : F →ₐ[k] L := IsScalarTower.toAlgHom k F L
  have hf : Function.Injective f := (algebraMap F L).injective
  have hfΛ : Function.Injective (AddMonoidAlgebra.mapAlgHom Λ f) := mapAlgHom_injective f hf
  obtain ⟨x', hx'⟩ := exists_affineMap_eq (AddMonoidAlgebra.mapAlgHom Λ f) hfΛ x (by
    intro c
    have hc := congrArg (fun ψ => ψ.hom c) (congrArg coord hx₁₂)
    simp only [coord_affineMap] at hc
    obtain ⟨y, hy⟩ :=
      CocharacterDescent.exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight
        (F := F) (L := L) (Λ := Λ) ((coord x).hom c) (by
          ext γ
          have hcγ := congrArg (fun z : AddMonoidAlgebra (L ⊗[F] L) Λ => z.coeff γ) hc
          simpa [i₁, i₂] using hcγ)
    refine ⟨y, ?_⟩
    rw [← hy]
    ext γ
    simp [f])
  rw [← hx'] at hx
  exact ⟨x', IsDatum.of_coeff_map f hf hx⟩

end Langlands.GroupScheme.CocharacterDatum
