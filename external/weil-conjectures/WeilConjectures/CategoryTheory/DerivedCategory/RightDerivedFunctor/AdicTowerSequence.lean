/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologySequence
public import WeilConjectures.CategoryTheory.Abelian.AdicTowerStructure
public import WeilConjectures.Algebra.Module.AdicTowerLimit
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Long exact sequences of derived functors of `ℓ`-adic towers

An `ℓ`-adic tower in an abelian category `C` (`CategoryTheory.AdicTowerStructure`) is a tower
`(Gₙ)` together with maps `ιₙₘ : Gₙ ⟶ Gₙ₊ₘ` such that `0 ⟶ Gₙ ⟶ Gₙ₊ₘ ⟶ Gₘ ⟶ 0` (the second map
being the transition map) is short exact, and such that the transition map `Gₙ₊ₘ ⟶ Gₙ` followed by
`ιₙₘ` is multiplication by `ℓᵐ`. For instance `Gₙ = Fₙ` for a tower of flat sheaves of
`ℤ/ℓⁿ`-modules with `Fₙ₊₁ ⊗ ℤ/ℓⁿ ≅ Fₙ`, `ιₙₘ` being induced by multiplication by `ℓᵐ`.

For an additive functor `F : C ⥤ D` and an exact functor `Φ : D ⥤ ModuleCat R` (e.g. a stalk
functor), the long exact cohomology sequences of `RF` applied to these short exact sequences
form, after applying `Φ`, the data `ModuleCat.AdicTowerSequence` of the towers
`(Φ Hʲ(RF Gₙ))ₙ` and `(Φ Hʲ⁺¹(RF Gₙ))ₙ`
(`CategoryTheory.AdicTowerStructure.adicTowerSequence`). The results of
`WeilConjectures.Algebra.Module.AdicTowerLimit` then apply: when these modules are finite,
`(Φ Hʲ(RF Gₙ))ₙ` is Artin-Rees isomorphic to `(L / ℓⁿ)ₙ` for its finitely generated limit `L`
(`CategoryTheory.AdicTowerStructure.exists_artinRees`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Abelian DerivedCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [Abelian C]

namespace AdicTowerStructure

variable {G : ℕᵒᵖ ⥤ C} {ℓ : ℕ}
/-- A functor to modules sends a composite to the composite of the maps on elements. -/
lemma _root_.CategoryTheory.Functor.map_hom_apply_of_comp_eq {R : Type u} [CommRing R]
    {E : Type*} [Category E] (T : E ⥤ ModuleCat.{v} R) {X Y Z : E} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} (e : f ≫ g = h) (x : T.obj X) :
    (T.map g).hom ((T.map f).hom x) = (T.map h).hom x := by
  rw [← e, T.map_comp]
  rfl

section Sequence

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
  {R : Type u} [CommRing R] (Φ : D ⥤ ModuleCat.{v} R) [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- The functor `G ↦ Φ Hʲ(RF G)`. -/
noncomputable abbrev homologyRightDerived (j : ℤ) : C ⥤ ModuleCat.{v} R :=
  singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙ homologyFunctor D j ⋙ Φ

omit [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
lemma homologyRightDerived_map_apply_of_eq_nsmul (j : ℤ) {X : C} {f : X ⟶ X} {k : ℕ}
    (hf : f = k • 𝟙 X) (x : (homologyRightDerived F Φ j).obj X) :
    ((homologyRightDerived F Φ j).map f).hom x = k • x := by
  rw [hf, Functor.map_nsmul, Functor.map_id]
  rfl

omit [Φ.Additive] [HasDerivedCategory D] in
/-- An exact sequence of `D` stays exact after the exact functor `Φ` to modules. -/
lemma _root_.CategoryTheory.ShortComplex.Exact.moduleCat_map_iff [Φ.PreservesZeroMorphisms]
    {S : ShortComplex D} (hS : S.Exact) (x₂ : Φ.obj S.X₂) :
    (Φ.map S.g).hom x₂ = 0 ↔ ∃ x₁, (Φ.map S.f).hom x₁ = x₂ := by
  refine ⟨(ShortComplex.moduleCat_exact_iff _).1 (hS.map Φ) x₂, ?_⟩
  rintro ⟨x₁, rfl⟩
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Φ.map_comp, S.zero, Φ.map_zero]
  rfl

/-- **The long exact sequences of `Φ Hʲ(RF -)` attached to an `ℓ`-adic tower.** -/
noncomputable def adicTowerSequence (A : AdicTowerStructure G ℓ) (j : ℤ) :
    ModuleCat.AdicTowerSequence ℓ (G ⋙ homologyRightDerived F Φ j)
      (G ⋙ homologyRightDerived F Φ (j + 1)) where
  a n m := ((homologyRightDerived F Φ j).map (A.ι n m)).hom
  a' n m := ((homologyRightDerived F Φ (j + 1)).map (A.ι n m)).hom
  δ n m := (Φ.map (F.rightDerivedHomologyδ (A.shortExact n m) j (j + 1) rfl)).hom
  towerMap_a n m x :=
    ((homologyRightDerived F Φ j).map_hom_apply_of_comp_eq (A.ι_comp_map n m) x).trans
      (homologyRightDerived_map_apply_of_eq_nsmul F Φ j rfl x)
  a_towerMap m h x :=
    ((homologyRightDerived F Φ j).map_hom_apply_of_comp_eq (A.map_comp_ι m h) x).trans
      ((homologyRightDerived F Φ j).map_hom_apply_of_comp_eq rfl x).symm
  towerMap_a' n m x :=
    ((homologyRightDerived F Φ (j + 1)).map_hom_apply_of_comp_eq (A.ι_comp_map n m) x).trans
      (homologyRightDerived_map_apply_of_eq_nsmul F Φ (j + 1) rfl x)
  a'_towerMap_self n m x :=
    ((homologyRightDerived F Φ (j + 1)).map_hom_apply_of_comp_eq (A.map_ι n m) x).trans
      (homologyRightDerived_map_apply_of_eq_nsmul F Φ (j + 1) rfl x)
  a'_towerMap m h x :=
    ((homologyRightDerived F Φ (j + 1)).map_hom_apply_of_comp_eq (A.map_comp_ι m h) x).trans
      ((homologyRightDerived F Φ (j + 1)).map_hom_apply_of_comp_eq rfl x).symm
  towerMap_δ {n k} m h z := by
    have := F.rightDerivedHomologyδ_naturality (A.shortExact k m) (A.shortExact n m)
      (A.shortComplexMapOfLE m h) j (j + 1) rfl
    dsimp [shortComplexMapOfLE] at this
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact Φ.map_hom_apply_of_comp_eq this.symm z
  δ_towerMap n m c z :=
    (Φ.map_hom_apply_of_comp_eq (F.rightDerivedHomologyδ_naturality (A.shortExact n (m + c))
      (A.shortExact (n + c) m) (A.shortComplexMapShift n m c) j (j + 1) rfl) z).trans
      (Φ.map_hom_apply_of_comp_eq rfl z).symm
  exact_a n m y :=
    (F.rightDerivedHomologySequence_exact₂ (A.shortExact n m) j).moduleCat_map_iff Φ y
  exact_δ n m z :=
    (F.rightDerivedHomologySequence_exact₃ (A.shortExact n m) j (j + 1) rfl).moduleCat_map_iff
      Φ z
  exact_a' n m y :=
    (F.rightDerivedHomologySequence_exact₁ (A.shortExact n m) j (j + 1) rfl).moduleCat_map_iff
      Φ y
  exact_a'_towerMap n m y :=
    (F.rightDerivedHomologySequence_exact₂ (A.shortExact n m) (j + 1)).moduleCat_map_iff Φ y

/-- **The towers `Φ Hʲ(RF Gₙ)` of an `ℓ`-adic tower are Artin-Rees `ℓ`-adic.** If the modules
`Φ Hʲ(RF Gₙ)` and `Φ Hʲ⁺¹(RF Gₙ)` are finite and `R` is noetherian and `ℓ`-adically precomplete,
the limit `L` of the tower `(Φ Hʲ(RF Gₙ))ₙ` is finitely generated, and there is `c` such that for
every `m` the kernel of `L ⟶ Φ Hʲ(RF Gₘ)` is `ℓᵐ L` and the image of
`Φ Hʲ(RF Gₘ₊꜀) ⟶ Φ Hʲ(RF Gₘ)` is contained in the image of `L`. -/
theorem exists_artinRees (A : AdicTowerStructure G ℓ) (j : ℤ) [IsNoetherianRing R]
    [IsPrecomplete (Ideal.span {(ℓ : R)}) R]
    [∀ n, Finite ((homologyRightDerived F Φ j).obj (G.obj n))]
    [∀ n, Finite ((homologyRightDerived F Φ (j + 1)).obj (G.obj n))] :
    Module.Finite R (ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j)) ∧
      ∃ c : ℕ, ∀ m : ℕ,
        (∀ x : ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j),
          x.1 (op m) = 0 ↔ ∃ y, ℓ ^ m • y = x) ∧
        ∀ z : (homologyRightDerived F Φ j).obj (G.obj (op (m + c))),
          ∃ x : ModuleCat.sectionsSubmodule (G ⋙ homologyRightDerived F Φ j),
            x.1 (op m) = ((homologyRightDerived F Φ j).map
              (G.map (homOfLE (Nat.le_add_right m c)).op)).hom z := by
  have (n : ℕᵒᵖ) : Finite ((G ⋙ homologyRightDerived F Φ j).obj n) :=
    inferInstanceAs (Finite ((homologyRightDerived F Φ j).obj (G.obj n)))
  have (n : ℕᵒᵖ) : Finite ((G ⋙ homologyRightDerived F Φ (j + 1)).obj n) :=
    inferInstanceAs (Finite ((homologyRightDerived F Φ (j + 1)).obj (G.obj n)))
  exact (A.adicTowerSequence F Φ j).exists_artinRees

end Sequence

end AdicTowerStructure

end CategoryTheory
