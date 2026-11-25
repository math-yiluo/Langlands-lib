/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients

/-!
# Naturality of Kummer classes and restriction of constant sections

For a morphism of schemes `g : X ⟶ Y` and `n` invertible on `Y`, the Kummer boundary
`δ₀ : Γ(Y, 𝒪)ˣ ⟶ H¹(Y, μₙ)` is compatible with pullback: the pullback of `δ₀(a)` to `X`, pushed
along the comparison `g^* μₙ ⟶ μₙ`, is `δ₀(g^* a)`.

For connected schemes `X` and `Y`, the restriction `H⁰(Y, ℤ/n) ⟶ H⁰(X, g^* ℤ/n)` is bijective:
both sides are `ℤ/n`, the constant functions.

## Main statements

- `AlgebraicGeometry.Scheme.sheafH_map_cohomologyMap_kummerδ₀`
- `AlgebraicGeometry.Scheme.bijective_cohomologyMap_zero_constantZMod`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The Kummer boundary `δ₀(u)` is the connecting homomorphism `H⁰(X, 𝔾ₘ) ⟶ H¹(X, μₙ)` applied
to the class of the section `gmSection u` of `𝔾ₘ` over the terminal object of `X_ét`. -/
lemma kummerδ₀_eq_δSucc (X : Scheme.{u}) (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ) :
    X.kummerδ₀ n hn (Additive.ofMul a) =
      Sheaf.H.δSucc (X.kummerSequence_shortExact n hn) 0
        ((Sheaf.H.equiv₀ X.gmSheaf terminalIsTerminal).symm (gmSection a)) := by
  rw [Sheaf.H.δSucc_zero _ terminalIsTerminal]
  erw [AddEquiv.apply_symm_apply]
  refine Eq.trans ?_ (Sheaf.H.δ_congr terminalIsTerminal
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
    (X.kummerSequence_shortExact n hn) (gmSection a))
  exact (congrArg (Sheaf.H.δSections (X.kummerSequence_shortExact n hn)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X))
      (gmSheaf_map_gmSection X a)).symm

/-- For a connected scheme `X`, the constant étale sheaf functor is bijective on morphisms:
`φ ↦ constantSheaf.map φ` is a bijection from `A ⟶ M` to `A_X ⟶ M_X`. -/
theorem bijective_constantSheaf_map {X : Scheme.{u}} [ConnectedSpace X]
    (A M : AddCommGrpCat.{u + 1}) :
    Function.Bijective (fun φ : A ⟶ M ↦
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ) := by
  let hT : IsTerminal (Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  have hu : IsIso (adj.unit.app M) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact X.bijective_toSheafify_app_terminal M
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv A ((constantSheaf _ _).obj M)).bijective]
  have h : (adj.homEquiv A ((constantSheaf _ _).obj M) ∘ fun φ ↦ (constantSheaf _ _).map φ) =
      fun φ ↦ φ ≫ adj.unit.app M := by
    funext φ
    rw [Function.comp_apply, Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  rw [h]
  exact ⟨fun a b hab ↦ (cancel_mono _).1 hab, fun g ↦ ⟨g ≫ inv (adj.unit.app M), by simp⟩⟩

/-- **Naturality of the Kummer boundary.** For `g : X ⟶ Y`, `n` invertible on `X` and `Y` and a
unit `a` on `Y`, the pullback along `g` of the Kummer class `δ₀(a) ∈ H¹(Y, μₙ)`, pushed along the
comparison `g^* μₙ ⟶ μₙ`, is the Kummer class `δ₀(g^* a) ∈ H¹(X, μₙ)`. -/
theorem sheafH_map_cohomologyMap_kummerδ₀ {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (hY : IsUnit (n : Γ(Y, ⊤))) (hX : IsUnit (n : Γ(X, ⊤))) (a : Γ(Y, ⊤)ˣ) :
    Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) 1
        (Etale.cohomologyMap g (Y.rootsOfUnitySheaf n) 1
          (Y.kummerδ₀ n hY (Additive.ofMul a))) =
      X.kummerδ₀ n hX (Additive.ofMul (Units.map g.appTop.hom a)) := by
  rw [kummerδ₀_eq_δSucc, kummerδ₀_eq_δSucc]
  have h₁ := Etale.cohomologyMap_δSucc g (Y.kummerSequence_shortExact n hY) 0
    ((Sheaf.H.equiv₀ Y.gmSheaf terminalIsTerminal).symm (gmSection a))
  have h₂ := Sheaf.H.map_δSucc
    ((Y.kummerSequence_shortExact n hY).map_of_exact (Etale.upperStar AddCommGrpCat.{u + 1} g))
    (X.kummerSequence_shortExact n hX) (kummerSequenceUpperStarMap g n) 0
    (Etale.cohomologyMap g Y.gmSheaf 0
      ((Sheaf.H.equiv₀ Y.gmSheaf terminalIsTerminal).symm (gmSection a)))
  refine ((congrArg (Sheaf.H.map
    (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) 1) h₁).trans h₂).trans ?_
  congr 1
  apply (Sheaf.H.equiv₀ X.gmSheaf terminalIsTerminal).injective
  refine (equiv₀_gmCohomologyMap_zero g _).trans ?_
  erw [AddEquiv.apply_symm_apply]
  exact (gmSectionsPullback_gmSection g a).trans (AddEquiv.apply_symm_apply _ _).symm

/-- For connected schemes `X` and `Y`, the restriction map `H⁰(Y, ℤ/n) ⟶ H⁰(X, g^* ℤ/n)` along
any `g : X ⟶ Y` is bijective. -/
theorem bijective_cohomologyMap_zero_constantZMod {X Y : Scheme.{u}} (g : X ⟶ Y)
    [ConnectedSpace X] [ConnectedSpace Y] (n : ℕ) [NeZero n] :
    Function.Bijective (Etale.cohomologyMap g (Y.constantZMod n) 0) := by
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let M := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  let ι := upperStarConstantSheafIso AddCommGrpCat.{u + 1} g
  let Φ : (A ⟶ M) → Sheaf.H (Y.constantZMod n) 0 := fun φ ↦
    Abelian.Ext.mk₀ ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ)
  let Ψ : (A ⟶ M) → Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj (Y.constantZMod n)) 0 :=
    fun φ ↦ Abelian.Ext.mk₀
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ ≫ (ι.app M).inv)
  have hΦ : Function.Bijective Φ :=
    (Abelian.Ext.mk₀_bijective _ _).comp (bijective_constantSheaf_map A M)
  have hι : Function.Bijective fun f : (constantSheaf X.smallEtaleTopology _).obj A ⟶ _ ↦
      f ≫ (ι.app M).inv :=
    ⟨fun a b hab ↦ (cancel_mono _).1 hab, fun f ↦ ⟨f ≫ (ι.app M).hom, by simp⟩⟩
  have hΨ : Function.Bijective Ψ :=
    (Abelian.Ext.mk₀_bijective _ _).comp (hι.comp (bijective_constantSheaf_map A M))
  have h : ⇑(Etale.cohomologyMap g (Y.constantZMod n) 0) ∘ Φ = Ψ := by
    funext φ
    simp only [Function.comp_apply, Φ, Ψ, Etale.cohomologyMap_apply,
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    rw [Iso.eq_comp_inv]
    have := ι.hom.naturality φ
    simp only [Functor.comp_map] at this
    simp [ι, A, this]
  rw [← Function.Bijective.of_comp_iff _ hΦ, h]
  exact hΨ

end AlgebraicGeometry.Scheme
