/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-!

# Locally free module objects on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`.

`ProEtale.IsLocallyFree R M`: there is a pro-étale cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}`
is free of finite rank over `R|_{Uᵢ}`. For `R = E_X` with `E` a field these are the lisse
`E`-sheaves of Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 6.8.6.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace CategoryTheory.Mod

/-- A free module object of finite rank is finitely presented: `R^n` is the cokernel of the zero
morphism `R^0 ⟶ R^n`. -/
lemma IsFree.isFinitelyPresented {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]
    {M : Mod C R} (hM : IsFree R M) : IsFinitelyPresented R M :=
  let ⟨n, ⟨e⟩⟩ := hM
  ⟨n, 0, 0, ⟨e ≪≫ (cokernelZeroIsoTarget (X := finiteFree R 0)).symm⟩⟩

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *locally free* (of finite rank) if there is a
pro-étale cover `{Uᵢ ⟶ X}` such that each `M|_{Uᵢ}` is isomorphic to `(R|_{Uᵢ})^{nᵢ}`. -/
def IsLocallyFree (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFree ((ProEtale.upperStar A (𝒰.f i)).obj R)
      (((ProEtale.upperStar A (𝒰.f i)).mapMod R).obj M)

variable {R} in
/-- Local freeness is invariant under isomorphism of module objects. -/
lemma IsLocallyFree.of_iso {M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R} (e : M ≅ N)
    (hM : IsLocallyFree R M) : IsLocallyFree R N :=
  let ⟨𝒰, h𝒰⟩ := hM
  ⟨𝒰, fun i ↦
    let ⟨n, ⟨e'⟩⟩ := h𝒰 i
    ⟨n, ⟨((ProEtale.upperStar A (𝒰.f i)).mapMod R).mapIso e.symm ≪≫ e'⟩⟩⟩

variable {R} in
/-- A locally free module object is locally finitely presented, a free module object of finite
rank `R^n` being the cokernel of `0 : R^0 ⟶ R^n`. -/
lemma IsLocallyFree.isLocallyFinitelyPresented {M : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (hM : IsLocallyFree R M) : IsLocallyFinitelyPresented R M :=
  let ⟨𝒰, h𝒰⟩ := hM
  ⟨𝒰, fun i ↦ (h𝒰 i).isFinitelyPresented⟩

end AlgebraicGeometry.ProEtale
