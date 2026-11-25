/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Products

/-!
# Functors on the derived category not preserving countable coproducts

Let `A` be an abelian category with K-injective resolutions, countable coproducts and exact
countable products, and let `F` be an object of `A`. The complexes `Kₙ = F[0]⟦n⟧` for `n : ℕ`
are concentrated in pairwise distinct degrees, so their coproduct is also their product as
cochain complexes, and hence both their coproduct and their product in `D(A)`
(`DerivedCategory.isColimitCofanMkQObj`, `DerivedCategory.isLimitFanMkQObj`).

Let `R : D(A) ⥤ D` be a functor preserving countable products, and `X` an object of `D` which is
compact in the following weak sense: for a countable coproduct `c` in `D` and morphisms
`π n : c.pt ⟶ Y n` with `c.inj m ≫ π n = 0` for `m ≠ n`, every `φ : X ⟶ c.pt` satisfies
`φ ≫ π n = 0` for all but finitely many `n`. If `X ⟶ R(F[0]⟦n⟧)` is nonzero for infinitely
many `n`, then `R` does not preserve countable coproducts: otherwise `R(⊕ Kₙ)` would be both the
coproduct and the product of the `R(Kₙ)`, and a morphism `X ⟶ ∏ R(Kₙ)` with infinitely many
nonzero components would contradict the compactness of `X`
(`DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero`).

## Main statements

- `DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero`.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Abelian.HasKInjectiveResolutions A] [HasColimitsOfShape (Discrete ℕ) A]
  [HasLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) A]
  {D : Type*} [Category* D] [HasZeroMorphisms D]

/-- Let `R : D(A) ⥤ D` preserve countable products, where countable products in `A` are exact,
and let `X` be an object of `D` such that for every countable coproduct `c` in `D` and morphisms
`π n : c.pt ⟶ Y n` with `c.inj m ≫ π n = 0` for `m ≠ n`, every `φ : X ⟶ c.pt` satisfies
`φ ≫ π n = 0` for almost all `n`. If there are nonzero morphisms `X ⟶ R(F[0]⟦n⟧)` for all
`n ≥ 1`, then `R` does not preserve countable coproducts. -/
theorem not_preservesColimitsOfShape_of_forall_hom_ne_zero (R : DerivedCategory A ⥤ D)
    [R.PreservesZeroMorphisms] [PreservesLimitsOfShape (Discrete ℕ) R] (X : D)
    (hX : ∀ {Y : ℕ → D} {c : Cofan Y} (_ : IsColimit c) (π : ∀ n, c.pt ⟶ Y n)
      (_ : ∀ m n, m ≠ n → c.inj m ≫ π n = 0) (φ : X ⟶ c.pt), ∃ S : Finset ℕ, ∀ n ∉ S,
        φ ≫ π n = 0)
    (F : A) (hF : ∀ n : ℕ, ∃ φ : X ⟶ R.obj (((singleFunctor A 0).obj F)⟦((n + 1 : ℕ) : ℤ)⟧),
      φ ≠ 0) :
    ¬ PreservesColimitsOfShape (Discrete ℕ) R := by
  intro _
  let K (n : ℕ) := ((CochainComplex.singleFunctor A 0).obj F)⟦(n : ℤ)⟧
  have hs := coproductIsCoproduct K
  let p := Cofan.IsColimit.proj hs
  have hl := isLimitFanMkObjOfIsLimit R _ _
    (isLimitFanMkQObj (CochainComplex.isLimitFanMkProjSingleFunctorObjShift F hs))
  have hc := isColimitCofanMkObjOfIsColimit R _ _ (isColimitCofanMkQObj hs)
  let e (n : ℕ) : Q.obj (K n) ≅ ((singleFunctor A 0).obj F)⟦(n : ℤ)⟧ :=
    (Q.commShiftIso (n : ℤ)).app _ ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso ((singleFunctorIsoCompQ A 0).app F).symm
  choose φ hφ using hF
  let f : ∀ n, X ⟶ R.obj (Q.obj (K n))
    | 0 => 0
    | m + 1 => φ m ≫ R.map (e (m + 1)).inv
  obtain ⟨S, hS⟩ := hX hc (fun n ↦ R.map (Q.map (p n))) (fun m n h ↦ by
    simpa [← Functor.map_comp] using
      congr(R.map (Q.map $(Cofan.IsColimit.inj_proj_of_ne hs h)))) (Fan.IsLimit.lift hl f)
  have hN : S.sup id + 1 ∉ S := fun h ↦ Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)
  have h : f _ = 0 := (Fan.IsLimit.fac hl f _).symm.trans (hS _ hN)
  exact hφ _ (by simpa [f] using h =≫ R.map (e _).hom)

end DerivedCategory
