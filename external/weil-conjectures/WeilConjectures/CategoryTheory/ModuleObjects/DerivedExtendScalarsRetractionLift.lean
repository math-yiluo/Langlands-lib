/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransitionComplex
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangulated
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.RetractionLift

/-!
# Lifting compatible retractions from the reductions modulo `mⁿ⁺¹`

Let `R` be a commutative algebra object of a closed symmetric monoidal Grothendieck abelian
category `C`, `m` an integer and `φₙ : R ⟶ Sₙ` morphisms of commutative algebra objects such that
`0 ⟶ R --mⁿ⁺¹--> R --φₙ--> Sₙ ⟶ 0` is short exact, with transitions `ψₙ : Sₙ₊₁ ⟶ Sₙ`,
`φₙ₊₁ ≫ ψₙ = φₙ` (the case of interest is `R = 𝒪_E`, `m = ℓ`, `Sₙ = 𝒪_E/ℓⁿ⁺¹`). Let
`i : A ⟶ B` be a morphism of `D(Mod_R(C))` whose source `A` is complete with respect to `m`
(every morphism to `A` from an object on which `m` acts invertibly vanishes; for instance a
derived complete `𝒪_E`-complex).

* `Mod.isSplitMono_of_isCenterComplete_of_retractions`: if the reductions `Sₙ ⊗ᴸ_R i` admit
  morphisms `sₙ : Sₙ ⊗ᴸ_R B ⟶ Sₙ ⊗ᴸ_R A` which are compatible with reduction (the reduction
  `Sₙ ⊗ᴸ_{Sₙ₊₁} sₙ₊₁` of `sₙ₊₁` is `sₙ`, `Mod.derivedExtendScalarsReduction`) and `s₀` is a
  retraction of `S₀ ⊗ᴸ_R i`, then `i` is a split monomorphism.
* `Mod.isSplitMono_of_isCenterComplete_of_unique_retractions`: the compatibility holds as soon as
  each `Sₙ ⊗ᴸ_R i` has a unique retraction with some property `Pₙ` which is preserved by reduction
  (for torsion nearby cycles, the retraction which is invariant under the Galois action).

## Proof

Write `ηₙ : K ⟶ Sₙ ⊗ᴸ_R K` for the units, `tₙ` for the transitions
(`Mod.derivedReductionTransition`) and `δₙ : Sₙ ⊗ᴸ_R K ⟶ K⟦1⟧` for the connecting morphisms of the
natural reduction triangles `K --mⁿ⁺¹--> K --ηₙ--> Sₙ ⊗ᴸ_R K --δₙ--> K⟦1⟧`
(`Mod.derivedExtendScalarsTriangleδ`), so that `tₙ ≫ δₙ = δₙ₊₁ ≫ m`. The maps
`ρₙ = ηₙ(B) ≫ sₙ : B ⟶ Sₙ ⊗ᴸ_R A` are compatible with the transitions, so by
`CategoryTheory.Pretriangulated.exists_comp_eq_of_tower` there is `r : B ⟶ A` with
`r ≫ η₀ = ρ₀` (the Milnor sequence for `A = R lim (Sₙ ⊗ᴸ_R A)`: only the surjectivity onto
`lim Hom(B, Sₙ ⊗ᴸ_R A)` is used, no `lim¹` term needs to vanish). The endomorphism `e = i ≫ r`
satisfies `e ≫ η₀ = η₀`, so `S₀ ⊗ᴸ_R e = 𝟙` and `e` is invertible by derived Nakayama
(`Mod.isIso_of_comp_unit_eq`), and `r ≫ e⁻¹` is a retraction of `i`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C] {R : C} [MonObj R] [IsCommMonObj R]

section Nakayama

variable {S : C} [MonObj S] [IsCommMonObj S] {φ : R ⟶ S} [IsMonHom φ] (k : ℤ)
  (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)

/-- An endomorphism `e` of `K` with `e ≫ η_K = η_K` for the unit `η_K : K ⟶ S ⊗ᴸ_R K` reduces to
the identity: `S ⊗ᴸ_R e = 𝟙`. -/
lemma leftDerivedFunctor_map_eq_id_of_comp_unit_eq {K : DerivedCategory (Mod C R)} (e : K ⟶ K)
    (he : e ≫ (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K =
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K) :
    (extendScalars φ).leftDerivedFunctor.map e = 𝟙 _ := by
  apply ((derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact ((derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality e).symm.trans he

include hφ in
/-- **Derived Nakayama for endomorphisms reducing to the identity**: if
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact and `K` is complete with respect to `k`, an
endomorphism `e` of `K` with `e ≫ η_K = η_K` is an isomorphism. Its cone `X` is complete and
`S ⊗ᴸ_R X = 0` since `S ⊗ᴸ_R e = 𝟙`, so `k` acts invertibly on `X` by the reduction triangle,
whence `X = 0`. -/
theorem isIso_of_comp_unit_eq {K : DerivedCategory (Mod C R)}
    (hK : IsCenterComplete (k • (1 : CatCenter (DerivedCategory (Mod C R)))) K) (e : K ⟶ K)
    (he : e ≫ (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K =
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K) : IsIso e := by
  obtain ⟨X, g, δ, hT⟩ := distinguished_cocone_triangle e
  have hL := (extendScalars φ).leftDerivedFunctor.map_distinguished _ hT
  have hLX : IsZero ((extendScalars φ).leftDerivedFunctor.obj X) := by
    refine (Triangle.isZero₃_iff_isIso₁ _ hL).2 ?_
    change IsIso ((extendScalars φ).leftDerivedFunctor.map e)
    rw [leftDerivedFunctor_map_eq_id_of_comp_unit_eq e he]
    infer_instance
  have hk : IsIso (k • 𝟙 X) := (Triangle.isZero₃_iff_isIso₁ _
    (derivedExtendScalarsTriangle_distinguished k w hφ X)).1
    ((comap φ).mapDerivedCategory.map_isZero hLX)
  have hX : IsCenterComplete (k • (1 : CatCenter (DerivedCategory (Mod C R)))) X :=
    IsCenterComplete.ext₂ _ (rot_of_distTriang _ hT) hK
      (hK.shift (CatCenter.zsmul_one_app_shift k) 1)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ((IsZero.iff_id_eq_zero X).2 (hX ?_ (𝟙 X)))
  rw [CatCenter.zsmul_one_app]
  exact hk

end Nakayama

variable {S : ℕ → C} [∀ n, MonObj (S n)] [∀ n, IsCommMonObj (S n)] {φ : ∀ n, R ⟶ S n}
  [∀ n, IsMonHom (φ n)] {ψ : ∀ n, S (n + 1) ⟶ S n} [∀ n, IsMonHom (ψ n)]
  (hψ : ∀ n, φ (n + 1) ≫ ψ n = φ n) (m : ℤ) (w : ∀ n, ((m ^ (n + 1)) • 𝟙 R) ≫ φ n = 0)
  (hS : ∀ n, (ShortComplex.mk _ _ (w n)).ShortExact)
  [HasCountableProducts (DerivedCategory (Mod C R))]

include hS in
/-- **Lifting compatible retractions from the reductions modulo `mⁿ⁺¹`.** Let `i : A ⟶ B` with
`A` complete with respect to `m`, and let `sₙ : Sₙ ⊗ᴸ_R B ⟶ Sₙ ⊗ᴸ_R A` be compatible with
reduction, with `s₀` a retraction of `S₀ ⊗ᴸ_R i`. Then `i` is a split monomorphism. -/
theorem isSplitMono_of_isCenterComplete_of_retractions {A B : DerivedCategory (Mod C R)}
    (i : A ⟶ B) (hA : IsCenterComplete (m • (1 : CatCenter (DerivedCategory (Mod C R)))) A)
    (s : ∀ n, (extendScalars (φ n)).leftDerivedFunctor.obj B ⟶
      (extendScalars (φ n)).leftDerivedFunctor.obj A)
    (hs : (extendScalars (φ 0)).leftDerivedFunctor.map i ≫ s 0 = 𝟙 _)
    (hcompat : ∀ n, derivedExtendScalarsReduction (φ (n + 1)) (ψ n) (φ n) (hψ n) (s (n + 1)) =
      s n) :
    IsSplitMono i := by
  refine isSplitMono_of_tower (CatCenter.zsmul_one_app_shift m) hA
    ((derivedExtendMapDerivedCategoryAdjunction (φ 0)).unit.app A)
    (fun n ↦ (derivedReductionTransition (φ (n + 1)) (ψ n) (φ n) (hψ n)).app A)
    (fun n ↦ (derivedExtendScalarsTriangleδ (m ^ (n + 1)) (w n) (hS n)).app A) (fun n ↦ ?_)
    ((m ^ (0 + 1)) • 𝟙 A) (derivedExtendScalarsTriangle_distinguished _ (w 0) (hS 0) A) i
    (fun n ↦ (derivedExtendMapDerivedCategoryAdjunction (φ n)).unit.app B ≫
      (comap (φ n)).mapDerivedCategory.map (s n)) (fun n ↦ ?_) ?_ (fun e he ↦ ?_)
  · rw [CatCenter.zsmul_one_app]
    refine derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ (ψ n) (hψ n)
      (m ^ (n + 1 + 1)) (m ^ (n + 1)) m (pow_succ' m (n + 1)) (w (n + 1)) (hS (n + 1)) (w n)
      (hS n) A |>.trans ?_
    rw [Functor.map_zsmul, CategoryTheory.Functor.map_id]
  · rw [Category.assoc, map_comp_derivedReductionTransition_app, hcompat,
      unit_app_comp_derivedReductionTransition_app_assoc]
  · have := (derivedExtendMapDerivedCategoryAdjunction (φ 0)).unit.naturality_assoc i
      ((comap (φ 0)).mapDerivedCategory.map (s 0))
    dsimp only [Functor.id_map, Functor.comp_map] at this
    rw [this, ← Functor.map_comp, hs, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  · exact isIso_of_comp_unit_eq _ (w 0) (hS 0) (by rwa [zero_add, pow_one]) e he

include hS in
/-- **Lifting unique retractions from the reductions modulo `mⁿ⁺¹`.** Let `i : A ⟶ B` with `A`
complete with respect to `m`. Suppose that each reduction `Sₙ ⊗ᴸ_R i` has a retraction with a
property `Pₙ` (for instance, invariance under a group action), that such a retraction is unique,
and that the reduction of a retraction with property `Pₙ₊₁` has property `Pₙ`. Then `i` is a split
monomorphism: the retractions with property `Pₙ` are compatible with reduction. -/
theorem isSplitMono_of_isCenterComplete_of_unique_retractions {A B : DerivedCategory (Mod C R)}
    (i : A ⟶ B) (hA : IsCenterComplete (m • (1 : CatCenter (DerivedCategory (Mod C R)))) A)
    (P : ∀ n, ((extendScalars (φ n)).leftDerivedFunctor.obj B ⟶
      (extendScalars (φ n)).leftDerivedFunctor.obj A) → Prop)
    (hex : ∀ n, ∃ s, P n s ∧ (extendScalars (φ n)).leftDerivedFunctor.map i ≫ s = 𝟙 _)
    (huniq : ∀ n s s', P n s → P n s' → (extendScalars (φ n)).leftDerivedFunctor.map i ≫ s = 𝟙 _ →
      (extendScalars (φ n)).leftDerivedFunctor.map i ≫ s' = 𝟙 _ → s = s')
    (hred : ∀ n s, P (n + 1) s → (extendScalars (φ (n + 1))).leftDerivedFunctor.map i ≫ s = 𝟙 _ →
      P n (derivedExtendScalarsReduction (φ (n + 1)) (ψ n) (φ n) (hψ n) s)) :
    IsSplitMono i := by
  choose s hP hs using hex
  refine isSplitMono_of_isCenterComplete_of_retractions hψ m w hS i hA s (hs 0) fun n ↦ ?_
  refine huniq n _ _ (hred n _ (hP (n + 1)) (hs (n + 1))) (hP n) ?_ (hs n)
  rw [← derivedExtendScalarsReduction_map (φ (n + 1)) (ψ n) (φ n) (hψ n),
    ← derivedExtendScalarsReduction_comp, hs (n + 1), ← CategoryTheory.Functor.map_id,
    derivedExtendScalarsReduction_map, CategoryTheory.Functor.map_id]

end CategoryTheory.Mod
