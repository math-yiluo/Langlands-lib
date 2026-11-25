/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DistTriang
public import WeilConjectures.ConstructibleSheaf.LisseTrivialization
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Biproducts
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.Etale.ZModCoefficients

/-!
# From `ℤ/ℓ` coefficients to finite modules killed by `ℓ`

Let `j : V ⟶ W` and `ι : D ⟶ W` be morphisms of schemes and `ℓ` a prime. If the cohomology
sheaves of `ι^* Rj_* ℤ/ℓ` (with coefficients `ℤ/ℓ`) are finite locally constant, then so are
those of `ι^* Rj_* N_V` for every finite module `N` killed by `ℓ` over a finite ring `Λ`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients).

Indeed, the underlying abelian sheaf of `ℋⁿ(ι^* Rj_* N_V)` is computed from the underlying
abelian group of `N`, which is a finite direct sum of copies of `ℤ/ℓ`; so it is a finite direct
sum of copies of the underlying abelian sheaf of `ℋⁿ(ι^* Rj_* ℤ/ℓ)`. Finite local constancy of
a sheaf of modules over a finite ring only depends on its underlying sheaf of sets
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_forget`).

## Main statements

- `AddCommGrpCat.exists_iso_biproduct_of_nsmul_eq_zero`: a finite abelian group killed by a
  prime `ℓ` is a finite direct sum of copies of `ℤ/ℓ`.
- `AlgebraicGeometry.Etale.upperStarHomologyDirectImageConstant`: the additive functor
  `A ↦ ι^* ℋⁿ(Rj_* A_V)` on abelian groups, and
  `AlgebraicGeometry.Etale.nonempty_forget₂_homology_iso_upperStarHomologyDirectImageConstant`:
  it computes the underlying abelian sheaf of `ℋⁿ(Lι^* Rj_* M_V)` for every module `M`.
- `AlgebraicGeometry.Scheme.HasFiniteLocallyConstantHomology.constantSheaf_of_constantZModModule`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- A finite abelian group killed by a prime `ℓ` is isomorphic to a finite direct sum of copies
of `ℤ/ℓ`, being a finite-dimensional vector space over `ZMod ℓ`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem AddCommGrpCat.exists_iso_biproduct_of_nsmul_eq_zero {M : Type (u + 1)} [AddCommGroup M]
    [Finite M] {ℓ : ℕ} [Fact ℓ.Prime] (hM : ∀ m : M, ℓ • m = 0) :
    ∃ r : ℕ, Nonempty (AddCommGrpCat.of M ≅
      ⨁ fun _ : Fin r ↦ AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) := by
  have : Module (ZMod ℓ) M := AddCommGroup.zmodModule hM
  have : Module.Finite (ZMod ℓ) M := Module.Finite.of_finite
  exact ⟨_, ⟨((Module.finBasis (ZMod ℓ) M).equivFun.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ ↦ AddEquiv.ulift.symm)).toAddCommGrpIso ≪≫
      (AddCommGrpCat.biproductIsoPi _).symm⟩⟩

namespace AlgebraicGeometry.Etale

variable {W V D : Scheme.{u}} (j : V ⟶ W) (ι : D ⟶ W)

/-- The functor `A ↦ ι^* ℋⁿ(Rj_* A_V[0])` from abelian groups to abelian étale sheaves on `D`,
where `A_V` is the constant sheaf on `V` (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`). It is additive, all its constituents being
so. -/
noncomputable def upperStarHomologyDirectImageConstant (n : ℤ) :
    AddCommGrpCat.{u + 1} ⥤ Sheaf D.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ R((j)_*[AddCommGrpCat.{u + 1}]) ⋙
      DerivedCategory.homologyFunctor _ n ⋙ (ι)^*[AddCommGrpCat.{u + 1}]

/-- The functor `A ↦ ι^* ℋⁿ(Rj_* A_V[0])` is additive
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
instance additive_upperStarHomologyDirectImageConstant (n : ℤ) :
    (upperStarHomologyDirectImageConstant j ι n).Additive := by
  dsimp [upperStarHomologyDirectImageConstant]
  infer_instance

/-- For a module `M` over a commutative ring `Λ`, the underlying abelian sheaf of
`ℋⁿ(Lι^* Rj_* M_V[0])` is `ι^* ℋⁿ(Rj_* A_V[0])` for the underlying abelian group `A` of `M`:
the derived pullback commutes with cohomology sheaves, and forgetting the module structure
commutes with pullbacks, higher direct images and constant sheaves
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem nonempty_forget₂_homology_iso_upperStarHomologyDirectImageConstant (n : ℤ)
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) :
    Nonempty ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.homologyFunctor _ n).obj
        ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
          ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))))) ≅
      (upperStarHomologyDirectImageConstant j ι n).obj
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) := by
  obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso Λ j n
    ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  exact ⟨(sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      ((leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} Λ) ι n).app _).symm ≪≫
    (asIso (upperStarForget₂Comparison Λ ι _)).symm ≪≫
    (ι)^*[AddCommGrpCat.{u + 1}].mapIso
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
        ((DerivedCategory.homologyFunctor _ n).mapIso
          ((((j)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))).symm)) ≪≫
        e ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso
          (((j)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusCompatibility.app _) ≪≫
        (DerivedCategory.singleFunctor _ 0 ⋙ R((j)_*[AddCommGrpCat.{u + 1}]) ⋙
          DerivedCategory.homologyFunctor _ n).mapIso
            ((constantSheafSheafComposeForget₂Iso Λ).app M))⟩

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.Etale

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients: if
`ι^* Rj_* ℤ/ℓ` has finite locally constant cohomology sheaves, then so has `ι^* Rj_* N_V` for
every finite module `N` killed by `ℓ` over a finite ring `Λ`.

The underlying abelian group of `N` is a direct sum of `r` copies of `ℤ/ℓ`, so the underlying
abelian sheaf of `ℋⁿ(ι^* Rj_* N_V)` is a direct sum of `r` copies of that of
`ℋⁿ(ι^* Rj_* ℤ/ℓ)`; this identifies the underlying sheaves of sets, and finite local constancy
of a sheaf of modules over a finite ring is detected on its underlying sheaf of sets. -/
theorem HasFiniteLocallyConstantHomology.constantSheaf_of_constantZModModule
    {W V D : Scheme.{u}} (j : V ⟶ W) (ι : D ⟶ W) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : HasFiniteLocallyConstantHomology D
      ((L((ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((R((j)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (constantZModModule V ℓ)))))
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (N : ModuleCat.{u + 1} Λ) [Finite N]
    (hN : ∀ n : N, (ℓ : Λ) • n = 0) :
    HasFiniteLocallyConstantHomology D
      ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)))) := by
  intro n
  refine IsFiniteLocallyConstantSheaf.of_forget _ ?_
  obtain ⟨r, ⟨eN⟩⟩ := AddCommGrpCat.exists_iso_biproduct_of_nsmul_eq_zero (M := N) (ℓ := ℓ)
    fun m ↦ by rw [← Nat.cast_smul_eq_nsmul Λ, hN]
  obtain ⟨eG⟩ := nonempty_forget₂_homology_iso_upperStarHomologyDirectImageConstant j ι n Λ N
  obtain ⟨eK⟩ := nonempty_forget₂_homology_iso_upperStarHomologyDirectImageConstant j ι n
    (ZModCoeff.{u} ℓ) (ModuleCat.of (ZModCoeff.{u} ℓ) (ZModCoeff.{u} ℓ))
  have := h n
  have := IsFiniteLocallyConstantSheaf.biproduct fun _ : Fin r ↦
    (DerivedCategory.homologyFunctor _ n).obj
      ((L((ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((R((j)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (constantZModModule V ℓ))))
  exact IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) AddCommGrpCat.{u + 1})).mapBiproduct _ ≪≫
        biproduct.mapIso (fun _ ↦ eK) ≪≫
        ((upperStarHomologyDirectImageConstant j ι n).mapBiproduct _).symm ≪≫
        (upperStarHomologyDirectImageConstant j ι n).mapIso eN.symm ≪≫ eG.symm))
    (IsFiniteLocallyConstantSheaf.isFiniteLocallyConstantSheafOfTypes_sheafForget _)

end AlgebraicGeometry.Scheme
