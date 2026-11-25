/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Mathlib.Data.Int.Interval
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.SmoothCompactDualModel

/-!
# Generic direct images from a smooth source

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-asd-smooth-generic-direct-image.md`, statement and proof
(blueprint: lemma-smooth-morphisms-locally-constant-sheaves).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Keep the derived-functor implementation behind its API during elaboration.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedHom constantComplex finiteLisseDualPullbackComparison
  derivedBaseChangeMap upperStar lowerStar
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  _root_.DerivedCategory.homologyFunctor

private theorem exists_dense_open_lisse_homology
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S : Scheme.{u}} (C : DerivedCategoryModule Λ S)
    (hC : DerivedCategory.isBoundedConstructible Λ S C) :
    ∃ U : S.Opens, Dense (U : Set S) ∧ ∀ i : ℤ,
      Scheme.IsFiniteLocallyConstantSheaf
        ((_root_.DerivedCategory.homologyFunctor _ i).obj
          ((L(upperStar (ModuleCat.{u + 1} Λ) U.ι)).obj C)) := by
  obtain ⟨hc, a, b, hab, hz⟩ := hC
  have key : ∀ t : Finset ℤ, ∃ U : S.Opens, Dense (U : Set S) ∧ ∀ i ∈ t,
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨⊤, by simp, by simp⟩
    | insert i t hi ih =>
      obtain ⟨V, hV, ht⟩ := ih
      have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
      obtain ⟨W, hW, hw⟩ := Scheme.IsConstructibleSheaf.exists_dense_open
        ((_root_.DerivedCategory.homologyFunctor _ i).obj C)
      refine ⟨V ⊓ W, hV.inter_of_isOpen_left hW V.isOpen, fun j hj ↦ ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
          (V ⊓ W).ι W.ι (by simp) _
      · have := ht j hj
        exact Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
          (V ⊓ W).ι V.ι (by simp) _
  obtain ⟨U, hU, hl⟩ := key (Finset.Icc a b)
  refine ⟨U, hU, fun i ↦ ?_⟩
  have : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) := by
    by_cases hi : a ≤ i ∧ i ≤ b
    · exact hl i (Finset.mem_Icc.2 hi)
    · exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero
        ((upperStar (ModuleCat.{u + 1} Λ) U.ι).map_isZero (hz i (by omega)))
  exact @Scheme.IsFiniteLocallyConstantSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    ((leftDerivedUpperStarHomologyFunctorIso (ModuleCat.{u + 1} Λ) U.ι i).app C) this

/-- A finite locally constant prime-field sheaf on a separated smooth finite-type source
has bounded finite locally constant ordinary derived direct image on a nonempty base open,
where its canonical ordinary exchange is invertible for every Noetherian test scheme.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-asd-smooth-generic-direct-image.md`
(blueprint: lemma-smooth-morphisms-locally-constant-sheaves).

Proof:
1. The schemes are Noetherian by lemma-smooth-morphisms-locally-constant-sheaves--1. The locally
constant relative
   dimension (lemma-smooth-morphisms-locally-constant-sheaves) and quasi-compactness
   split X into finitely many open-and-closed pure-dimensional pieces. Compactify each
   by theorem-nagata-s-compactification-theorem--1.
2. On one piece put omega = f^times lambda and N = L^dual tensor omega.
   By proposition-exceptional-inverse-image-smooth-morphism, omega is a rank-one lisse sheaf shifted
   by 2d. Finite-free biduality gives L = RHom(N, omega): compute on trivializing etale
   neighborhoods and use lemma-weil-pbc-geometric-stalk-conservative. Thus N is bounded
   constructible.
3. lemma-internal-adjunction-two-exchange-formulas--1 identifies Rf_*L with RHom(Rf_!N, lambda).
   lemma-smooth-morphisms-locally-constant-sheaves makes C = Rf_!N bounded constructible.
   In each of its finitely many cohomological degrees, the stratum through the generic
   point contains a nonempty open. Intersect these opens and apply
   lemma-smooth-morphisms-locally-constant-sheaves to obtain bounded finite locally constant
   cohomology of the dual.
4. For every Noetherian T, proposition-exceptional-inverse-image-smooth-morphism--6 identifies the
pulled-back omega
   and N with those for f_T. Base-changed compactification and finite type make the
   ambient adjunction available (lemma-nagata-compactification-base-change and
   lemma-smooth-morphisms-locally-constant-sheaves--1). Compact-support exchange and
   lemma-smooth-morphisms-locally-constant-sheaves then give an isomorphism between the desired
   objects.
5. Identify this map with definition-derived-base-change-map--1: transpose the internal-adjunction
   pairing obtained from the ordinary counit f^*Rf_*L -> L and evaluation L tensor N ->
   omega. Compact exchange is natural for this pairing; exceptional exchange is the
   transpose of compact exchange followed by the exceptional counit. Pulling back these
   pairings therefore gives precisely the ordinary inverse-image square comparison
   followed by the pulled-back ordinary counit. Equality of adjunction transposes proves
   equality with the specified ordinary exchange, hence its invertibility.
6. Intersect the opens from all dimensions. Direct image and exchange on a finite
   disjoint union are finite products, which are exact in the abelian sheaf category.
   Take common bounds; finite sums of finite locally constant sheaves remain so.
   For empty X use the zero complex and the whole integral base as the open. -/
theorem exists_nonempty_open_smooth_directImage_lisse_baseChange
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X : Scheme.{u}) (f : X ⟶ S) [IsSeparated f] [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
        IsPullback p fU f U.ι →
        (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        (∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
          ((_root_.DerivedCategory.homologyFunctor _ i).obj
            ((R((fU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))))) ∧
        ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
          (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
          (sq : IsPullback vX fT fU v),
          IsIso ((derivedBaseChangeMap
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
              ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj L))) := by
  obtain ⟨model⟩ := exists_smooth_compact_dual_model k S aS ℓ hℓ X f L hL
  let C := model.complex
  have hC := model.boundedConstructible
  obtain ⟨U, hUd, hlisse⟩ :=
    exists_dense_open_lisse_homology (ULift.{u + 1} (ZMod ℓ)) C hC
  have hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        ((L((U.ι)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj C)) := by
    obtain ⟨a, b, hab, hz⟩ := hC.2
    refine ⟨a, b, hab, fun i hi ↦ ?_⟩
    exact ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) U.ι).map_isZero
      (hz i hi)).of_iso ((leftDerivedUpperStarHomologyFunctorIso
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) U.ι i).app C).symm
  refine ⟨U, hUd.nonempty.to_subtype, ?_⟩
  intro XU p fU sqU
  let eU := model.openIso U XU p fU sqU
  have hprime : ℓ.Prime := Fact.out
  have hchar : (ℓ : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k hprime hℓ.symm
  have hunit : IsUnit (ℓ : Γ(U.toScheme, ⊤)) := by
    have hspec : IsUnit (ℓ : Γ(Spec (.of k), ⊤)) := by
      simpa only [map_natCast] using hchar.isUnit.map (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa only [map_natCast] using hspec.map (U.ι ≫ aS).appTop.hom
  obtain ⟨hdual, hhom, hexchange⟩ := finiteLisseFieldDual ℓ U.toScheme hunit
    ((L((U.ι)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj C) hbounded hlisse
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, hab, hvan⟩ := hbounded
    refine ⟨-b, -a, neg_le_neg hab, fun i hi ↦ ?_⟩
    have hz := hvan (-i) (by omega)
    obtain ⟨e⟩ := hhom i
    exact (CategoryTheory.MonoidalCategory.isZero_ihom_obj_of_isZero hz _).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso eU ≪≫ e)
  · intro i
    have := hdual i
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso eU.symm)
  · intro T inst v XT vX fT sq
    let eT := model.testIso U XU p fU sqU T v XT vX fT sq
    have heT := model.exchange U XU p fU sqU T v XT vX fT sq
    have := hexchange T v
    have : IsIso ((derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
          ((L((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) ≫ eT.hom) := by
      rw [← heT]
      infer_instance
    exact IsIso.of_isIso_comp_right _ eT.hom

end AlgebraicGeometry.Etale
