/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparisonFormal
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Formal coherence of the etale internal-Hom comparison

Source: Bhatt--Scholze, Lemma 6.3.16, with the closed monoidal mate calculus.
(blueprint: lem-weil-pbc-ind-etale-internal-hom-coherence).

The clauses are proved for a general coefficient category in
`WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparisonFormal`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace Etale

-- Elaborate the statement with the instances of the general coefficient category specialised to
-- `ModuleCat`, so that it agrees syntactically with the general lemmas.
attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- Composition, identity, shift, and lower-bound clauses for the canonical internal-Hom
comparison. Monoidal naturality gives composition. For identity, cancel whiskering from
the derived composition/unit coherence to prove that the identity isomorphism is monoidal.
The target-shift square is the mate of the inverse tensor comparison. Combining the two
canonical tensor-shift squares and taking mates gives the source-shift square, with the
inverse shift determined by the shift adjunction triangle. Finally the tensor-Hom
adjunction estimate and exact inverse image give both lower bounds.

Source: Bhatt--Scholze, Lemma 6.3.16, pp. 47--48, small-etale analogue; the closed
monoidal mate calculus proves these formal clauses without ind-etale assumptions.
(blueprint: lem-weil-pbc-ind-etale-internal-hom-coherence). -/
theorem indEtaleInternalHomComparison_coherence_and_bounds
    (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (f : U ⟶ X)
    (K M : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
      (∀ {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
        (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
        (P Q : _root_.DerivedCategory
          (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} A))),
        derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g₁₂ P Q ≫
            (RHom(T)[ModuleCat.{u + 1} A].obj
              (op ((L((g₁₂)^*[ModuleCat.{u + 1} A])).obj P))).map
              ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app Q) =
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app
              ((RHom(R)[ModuleCat.{u + 1} A].obj (op P)).obj Q) ≫
            (L((g₁)^*[ModuleCat.{u + 1} A])).map
              (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g₂ P Q) ≫
            derivedHomUpperStarComparison (ModuleCat.{u + 1} A) g₁
              ((L((g₂)^*[ModuleCat.{u + 1} A])).obj P)
              ((L((g₂)^*[ModuleCat.{u + 1} A])).obj Q) ≫
            (pre ((leftDerivedUpperStarComp
              (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app P)).app
              ((L((g₁)^*[ModuleCat.{u + 1} A])).obj
                ((L((g₂)^*[ModuleCat.{u + 1} A])).obj Q))) ∧
      (∀ (Y : Scheme.{u}) (P Q : _root_.DerivedCategory
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))),
        derivedHomUpperStarComparison (ModuleCat.{u + 1} A) (𝟙 Y) P Q ≫
            (RHom(Y)[ModuleCat.{u + 1} A].obj
              (op ((L((𝟙 Y)^*[ModuleCat.{u + 1} A])).obj P))).map
              ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app Q) =
          (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app
              ((RHom(Y)[ModuleCat.{u + 1} A].obj (op P)).obj Q) ≫
            (pre ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app P)).app Q) ∧
      (∀ (n : ℤ),
        derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f (K⟦n⟧) M ≫
            (pre (((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso n).inv.app K)).app
              ((L((f)^*[ModuleCat.{u + 1} A])).obj M) ≫
            (derivedHomShiftIso (ModuleCat.{u + 1} A)
              ((L((f)^*[ModuleCat.{u + 1} A])).obj K) n).hom.app
              ((L((f)^*[ModuleCat.{u + 1} A])).obj M) =
          (L((f)^*[ModuleCat.{u + 1} A])).map
              ((derivedHomShiftIso (ModuleCat.{u + 1} A) K n).hom.app M) ≫
            ((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso (-n)).hom.app
              ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M) ≫
            (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f K M)⟦-n⟧') ∧
      (∀ (n : ℤ),
        derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f K (M⟦n⟧) ≫
            (RHom(U)[ModuleCat.{u + 1} A].obj
              (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))).map
              (((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso n).hom.app M) ≫
            (Functor.commShiftIso (RHom(U)[ModuleCat.{u + 1} A].obj
              (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K)))
              (self := commShiftDerivedHomObj (ModuleCat.{u + 1} A)
                (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))) n).hom.app
              ((L((f)^*[ModuleCat.{u + 1} A])).obj M) =
          (L((f)^*[ModuleCat.{u + 1} A])).map
              ((Functor.commShiftIso (RHom(X)[ModuleCat.{u + 1} A].obj (op K))
              (self := commShiftDerivedHomObj (ModuleCat.{u + 1} A) (op K)) n).hom.app M) ≫
            ((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso n).hom.app
              ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M) ≫
            (derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f K M)⟦n⟧') ∧
      (∀ (b N : ℤ), K.IsLE b → M.IsGE N →
        ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M).IsGE (N - b) ∧
        ((RHom(U)[ModuleCat.{u + 1} A].obj
          (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))).obj
          ((L((f)^*[ModuleCat.{u + 1} A])).obj M)).IsGE (N - b) ∧
        ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M).IsGE (N - b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T S R g₁ g₂ g₁₂ hg P Q
    exact derivedHomUpperStarComparison_comp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg P Q
  · intro Y P Q
    exact derivedHomUpperStarComparison_id (ModuleCat.{u + 1} A) Y P Q
  · intro n
    exact derivedHomUpperStarComparison_shift_left (ModuleCat.{u + 1} A) f K M n
  · intro n
    exact derivedHomUpperStarComparison_shift_right (ModuleCat.{u + 1} A) f K M n
  · intro b N hb hN
    have : K.IsLE b := hb
    have : M.IsGE N := hN
    have hX := isGE_derivedHom_obj (ModuleCat.{u + 1} A) K M b N
    have : ((f)^*[ModuleCat.{u + 1} A]).mapDerivedCategory.obj K |>.IsLE b :=
      ((f)^*[ModuleCat.{u + 1} A]).isLE_mapDerivedCategory_obj K b
    have : ((f)^*[ModuleCat.{u + 1} A]).mapDerivedCategory.obj M |>.IsGE N :=
      ((f)^*[ModuleCat.{u + 1} A]).isGE_mapDerivedCategory_obj M N
    have : ((L((f)^*[ModuleCat.{u + 1} A])).obj K).IsLE b :=
      _root_.DerivedCategory.TStructure.t.isLE_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K).symm b
    have : ((L((f)^*[ModuleCat.{u + 1} A])).obj M).IsGE N :=
      _root_.DerivedCategory.TStructure.t.isGE_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app M).symm N
    exact ⟨hX, isGE_derivedHom_obj (ModuleCat.{u + 1} A) _ _ b N, hX⟩

end Etale
end AlgebraicGeometry
