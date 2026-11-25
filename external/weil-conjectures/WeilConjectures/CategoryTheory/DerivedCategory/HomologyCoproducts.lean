/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Homology commutes with coproducts in the derived category

Let `C` be an abelian category with K-injective resolutions in which coproducts of shape `β`
exist and are exact. The homology functors `D(C) ⥤ C` preserve coproducts of shape `β`: up to
isomorphism, a family in `D(C)` is the image of a family of cochain complexes, whose coproduct is
a coproduct in `D(C)` (`DerivedCategory.isColimitCofanMkQObj`), and homology of cochain complexes
commutes with exact coproducts.

As an application, let `L ⊣ G` be an adjunction with `G : C ⥤ ModuleCat R` preserving coproducts
and `P = L(R)` projective. Then `P[0]` is compact with respect to coproducts of shape `β`, in the
following weak form: for a coproduct `c` of a family `Y` in `D(C)` and morphisms
`π j : c.pt ⟶ Y j` with `c.inj i ≫ π j = 0` for `i ≠ j`, every morphism `φ : P[0] ⟶ c.pt`
satisfies `φ ≫ π j = 0` for all but finitely many `j`
(`DerivedCategory.exists_finset_forall_comp_eq_zero`). Indeed, morphisms `P[0] ⟶ X` are
elements of `G(H⁰(X))` (`DerivedCategory.singleFunctorZeroHomEquiv`), and `H⁰ ⋙ G` preserves
coproducts.

## Main statements

- `DerivedCategory.preservesColimitsOfShape_homologyFunctor`.
- `DerivedCategory.exists_finset_forall_comp_eq_zero`.
- `DerivedCategory.isIso_sigmaComparison_iff`: a functor to `D(C)` commutes with a coproduct if
  and only if all its homology functors do.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] {β : Type*}

section Homology

variable [Abelian.HasKInjectiveResolutions C] [HasColimitsOfShape (Discrete β) C]
  [HasExactColimitsOfShape (Discrete β) C]

/-- If `C` has K-injective resolutions and coproducts of shape `β` in `C` are exact, the homology
functors on the derived category preserve coproducts of shape `β`. -/
instance preservesColimitsOfShape_homologyFunctor (n : ℤ) :
    PreservesColimitsOfShape (Discrete β) (homologyFunctor C n) where
  preservesColimit {K} := by
    let M (j : β) := Q.objPreimage (K.obj ⟨j⟩)
    have : PreservesColimitsOfShape (Discrete β) (Q ⋙ homologyFunctor C n) :=
      preservesColimitsOfShape_of_natIso (homologyFunctorFactors C n).symm
    have : PreservesColimit (Discrete.functor fun j ↦ Q.obj (M j)) (homologyFunctor C n) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitCofanMkQObj (coproductIsCoproduct M))
        ((isColimitMapCoconeCofanMkEquiv (homologyFunctor C n) (fun j ↦ Q.obj (M j))
          fun j ↦ Q.map (Sigma.ι M j)).2
          ((isColimitMapCoconeCofanMkEquiv (Q ⋙ homologyFunctor C n) M (Sigma.ι M)).1
            (isColimitOfPreserves (Q ⋙ homologyFunctor C n) (coproductIsCoproduct M))))
    exact preservesColimit_of_iso_diagram _
      (Discrete.natIso fun j ↦ Q.objObjPreimageIso (K.obj ⟨j.as⟩) :
        Discrete.functor (fun j ↦ Q.obj (M j)) ≅ K)

end Homology

variable {R : Type*} [Ring R] {L : ModuleCat R ⥤ C} {G : C ⥤ ModuleCat R}
  [Projective (L.obj (ModuleCat.of R R))]

/-- The element of `G(H⁰(X))` corresponding to a morphism `P[0] ⟶ X` in the derived category,
where `P = L(R)` for an adjunction `L ⊣ G`. -/
noncomputable def homologyElementOfHom (adj : L ⊣ G) {X : DerivedCategory C}
    (φ : (singleFunctor C 0).obj (L.obj (ModuleCat.of R R)) ⟶ X) :
    G.obj ((homologyFunctor C 0).obj X) :=
  (adj.homEquiv _ _ (singleFunctorZeroHomEquiv _ X φ)).hom 1

lemma homologyElementOfHom_comp (adj : L ⊣ G) {X X' : DerivedCategory C}
    (φ : (singleFunctor C 0).obj (L.obj (ModuleCat.of R R)) ⟶ X) (f : X ⟶ X') :
    homologyElementOfHom adj (φ ≫ f) =
      G.map ((homologyFunctor C 0).map f) (homologyElementOfHom adj φ) := by
  simp [homologyElementOfHom, Adjunction.homEquiv_naturality_right]

lemma eq_zero_of_homologyElementOfHom_eq_zero (adj : L ⊣ G) [G.PreservesZeroMorphisms]
    {X : DerivedCategory C} (φ : (singleFunctor C 0).obj (L.obj (ModuleCat.of R R)) ⟶ X)
    (h : homologyElementOfHom adj φ = 0) : φ = 0 := by
  have h₁ : adj.homEquiv _ _ (singleFunctorZeroHomEquiv _ X φ) = 0 :=
    ModuleCat.hom_ext (LinearMap.ext_ring h)
  have h₂ : singleFunctorZeroHomEquiv _ X φ = 0 :=
    (adj.homEquiv _ _).injective (h₁.trans (by simp [Adjunction.homEquiv_unit]))
  exact (singleFunctorZeroHomEquiv _ X).injective (h₂.trans (by simp))

/-- Let `L ⊣ G` be an adjunction with `G : C ⥤ ModuleCat R` preserving coproducts of shape `β`
and `P = L(R)` projective. For a coproduct `c` of a family `Y` in the derived category and
morphisms `π j : c.pt ⟶ Y j` with `c.inj i ≫ π j = 0` for `i ≠ j`, every morphism
`φ : P[0] ⟶ c.pt` satisfies `φ ≫ π j = 0` for all but finitely many `j`. -/
lemma exists_finset_forall_comp_eq_zero [Abelian.HasKInjectiveResolutions C]
    [HasColimitsOfShape (Discrete β) C] [HasExactColimitsOfShape (Discrete β) C] (adj : L ⊣ G)
    [G.PreservesZeroMorphisms] [PreservesColimitsOfShape (Discrete β) G]
    {Y : β → DerivedCategory C} {c : Cofan Y}
    (hc : IsColimit c) (π : ∀ j, c.pt ⟶ Y j) (hπ : ∀ i j, i ≠ j → c.inj i ≫ π j = 0)
    (φ : (singleFunctor C 0).obj (L.obj (ModuleCat.of R R)) ⟶ c.pt) :
    ∃ S : Finset β, ∀ j ∉ S, φ ≫ π j = 0 := by
  obtain ⟨S, hS⟩ := ModuleCat.exists_finset_forall_map_apply_eq_zero
    (homologyFunctor C 0 ⋙ G) hc π hπ (homologyElementOfHom adj φ)
  exact ⟨S, fun j hj ↦ eq_zero_of_homologyElementOfHom_eq_zero adj _
    ((homologyElementOfHom_comp adj φ (π j)).trans (hS j hj))⟩

section SigmaComparison

variable {A : Type*} [Category* A] [Abelian.HasKInjectiveResolutions C] {J : Type*}
  [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C]
  [HasColimitsOfShape (Discrete J) (DerivedCategory C)]

/-- A functor to the derived category commutes with a coproduct if and only if all its homology
functors do. -/
lemma isIso_sigmaComparison_iff (F : A ⥤ DerivedCategory C) (X : J → A) [HasCoproduct X] :
    IsIso (sigmaComparison F X) ↔ ∀ n, IsIso (sigmaComparison (F ⋙ homologyFunctor C n) X) := by
  rw [isIso_iff]
  refine forall_congr' fun n ↦ ?_
  rw [sigmaComparison_comp, isIso_comp_left_iff]

/-- The functor `singleFunctor C 0` placing an object in degree `0` commutes with coproducts. -/
instance isIso_sigmaComparison_singleFunctor (X : J → C) :
    IsIso (sigmaComparison (singleFunctor C 0) X) := by
  rw [isIso_sigmaComparison_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact isIso_sigmaComparison_of_isZero _ _ fun Y ↦ isZero_of_isGE _ 0 n hn
  · exact CategoryTheory.Limits.isIso_sigmaComparison_of_natIso
      (singleFunctorCompHomologyFunctorIso C 0).symm X
  · exact isIso_sigmaComparison_of_isZero _ _ fun Y ↦ isZero_of_isLE _ 0 n hn

end SigmaComparison

end DerivedCategory
