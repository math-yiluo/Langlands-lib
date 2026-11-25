/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Dévissage of the homology of a triangulated functor

Let `Φ : D(C) ⥤ D(C')` be a triangulated functor. If `Hᵐ(Φ K) ≠ 0` for a bounded object `K`,
then some homology object `Hᵇ K`, placed in degree `0`, has `Hᵐ⁻ᵇ(Φ Hᵇ K) ≠ 0`: by induction on
the length of the amplitude of `K`, along the truncation triangles.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasDerivedCategory.{w'} C']

/-- `Hᵐ(Φ (X[b])) ≅ Hᵐ⁻ᵇ(Φ X)` for `X` placed in degree `0` and shifted to degree `b`. -/
noncomputable def homologyObjSingleFunctorIso (Φ : DerivedCategory C ⥤ DerivedCategory C')
    [Φ.CommShift ℤ] (X : C) (b m : ℤ) :
    (homologyFunctor C' m).obj (Φ.obj ((singleFunctor C b).obj X)) ≅
      (homologyFunctor C' (m - b)).obj (Φ.obj ((singleFunctor C 0).obj X)) :=
  (homologyFunctor C' m).mapIso (Φ.mapIso
      (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app X).symm ≪≫
    (Φ.commShiftIso (-b)).app _) ≪≫
  ((homologyFunctor C' 0).shiftIso (-b) m (m - b) (by lia)).app _

/-- **Dévissage of the homology of a triangulated functor.** Let `Φ : D(C) ⥤ D(C')` be a
triangulated functor and `K` an object with homology in `[a, a + n - 1]`. If `Hᵐ(Φ K) ≠ 0`, then
`Hᵐ⁻ᵇ(Φ Hᵇ K) ≠ 0` for some `b`, the object `Hᵇ K` being placed in degree `0`: along the
truncation triangle `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` with `b = a + n - 1`, whose third term is
`Hᵇ K` placed in degree `b`, either `Hᵐ(Φ τ_{< b} K)` or `Hᵐ(Φ τ_{≥ b} K)` is nonzero. -/
lemma exists_not_isZero_homology_obj_singleFunctor (Φ : DerivedCategory C ⥤ DerivedCategory C')
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (n : ℕ) :
    ∀ (a : ℤ) (K : DerivedCategory C), K.IsGE a → K.IsLE (a + n - 1) → ∀ m : ℤ,
      ¬ IsZero ((homologyFunctor C' m).obj (Φ.obj K)) →
      ∃ b, ¬ IsZero ((homologyFunctor C' (m - b)).obj
        (Φ.obj ((singleFunctor C 0).obj ((homologyFunctor C b).obj K)))) := by
  induction n with
  | zero =>
    intro a K _ _ m hm
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact absurd ((homologyFunctor C' m).map_isZero
      (Φ.map_isZero (TStructure.t.isZero K (a - 1) a (by lia)))) hm
  | succ n ih =>
    intro a K _ _ m hm
    set b : ℤ := a + n
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    have : T.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
    have hex := (Φ ⋙ homologyFunctor C' m).map_distinguished_exact _ hT
    by_cases h₃ : IsZero ((homologyFunctor C' m).obj (Φ.obj T.obj₃))
    · -- the first term has nonzero homology, and the dévissage applies to it
      have h₁ : ¬ IsZero ((homologyFunctor C' m).obj (Φ.obj T.obj₁)) :=
        fun h₁ ↦ hm (hex.isZero_of_both_isZero h₁ h₃)
      obtain ⟨b', hb'⟩ := ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
        (TStructure.t.isLE_of_le _ (b - 1) _ (by lia)) m h₁
      refine ⟨b', fun h ↦ hb' ?_⟩
      by_cases hb : b' < b
      · have : IsIso ((homologyFunctor C b').map T.mor₁) :=
          isIso_homologyMap_mor₁ _ hT (b' - 1) b' (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact h.of_iso ((homologyFunctor C' _).mapIso (Φ.mapIso
          ((singleFunctor C 0).mapIso (asIso ((homologyFunctor C b').map T.mor₁)))))
      · exact (homologyFunctor C' _).map_isZero (Φ.map_isZero
          ((singleFunctor C 0).map_isZero (isZero_of_isLE _ (b - 1) _ (by lia))))
    · -- the third term is `Hᵇ K` placed in degree `b`
      refine ⟨b, fun h ↦ h₃ ?_⟩
      obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
      have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl (isZero_of_isLE _ (b - 1) _ (by lia))
        (isZero_of_isLE _ (b - 1) _ (by lia))
      let e : (homologyFunctor C b).obj K ≅ G := asIso ((homologyFunctor C b).map T.mor₂) ≪≫
        (homologyFunctor C b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso C b).app G
      exact h.of_iso ((homologyFunctor C' m).mapIso (Φ.mapIso eG) ≪≫
        homologyObjSingleFunctorIso Φ G b m ≪≫
        (homologyFunctor C' (m - b)).mapIso (Φ.mapIso ((singleFunctor C 0).mapIso e.symm)))

end DerivedCategory
